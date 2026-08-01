theory M0_List_Bridge
  imports "EAL6_FreeRTOS_V611_List_Smoke.List_V611_Translation"
begin

text \<open>
  M0 is deliberately a one-item needle.  It is large enough to distinguish
  the empty and singleton list states and small enough to expose whether the
  stock mini-sentinel cast has a satisfiable lifted-heap interpretation.
\<close>

datatype m0_abs = M0_Empty | M0_One "xLIST_ITEM_C ptr"

fun m0_insert_end :: "xLIST_ITEM_C ptr \<Rightarrow> m0_abs \<Rightarrow> m0_abs option" where
  "m0_insert_end item M0_Empty = Some (M0_One item)"
| "m0_insert_end item (M0_One old) = None"

fun m0_remove :: "xLIST_ITEM_C ptr \<Rightarrow> m0_abs \<Rightarrow> m0_abs option" where
  "m0_remove item M0_Empty = None"
| "m0_remove item (M0_One old) = (if item = old then Some M0_Empty else None)"

definition m0_sentinel :: "xLIST_C ptr \<Rightarrow> xLIST_ITEM_C ptr" where
  "m0_sentinel list = PTR(xLIST_ITEM_C) &(list\<rightarrow>[''xListEnd_C''])"

text \<open>
  These generated validity facts are printed in the first audit build; the
  bridge proof below will use their exact checked statements rather than
  guessing at the open-structure heap layout.
\<close>

print_statement xLIST_C.ptr_valid.unfold
print_statement xLIST_ITEM_C.ptr_valid.unfold
print_statement ptr_valid_addressable_field_field_lvalue
print_statement ptr_valid_same_type_neq_no_overlap_conv
print_statement root_ptr_valid_cases
print_statement xLIST_C_xListEnd_C_fl
print_statement xLIST_C_size_of
print_statement xLIST_ITEM_C_size_of

lemma m0_abstract_round_trip_non_vacuous:
  "m0_insert_end item M0_Empty = Some (M0_One item) \<and>
   m0_remove item (M0_One item) = Some M0_Empty"
  by simp

text \<open>
  Target-gate A: the generated split heap treats both C structure types as
  root-only types.  The embedded mini-sentinel starts inside the list root's
  footprint, so its cast address cannot simultaneously be a distinct
  xLIST_ITEM_C root.  This theorem is only a heap-typing conflict; it does not
  by itself state that the whole vListInsertEnd' execution relation is empty.
\<close>

lemma m0_word_of_nat_8:
  "(of_nat 8 :: 32 word) = 8"
  by simp

lemma m0_sentinel_typed_roots_conflict:
  assumes list_root: "root_ptr_valid d (list :: xLIST_C ptr)"
    and item_root: "root_ptr_valid d (m0_sentinel list)"
  shows False
  using root_ptr_valid_cases[OF list_root item_root]
  unfolding m0_sentinel_def
  apply (simp add: field_lvalue_def xLIST_C_xListEnd_C_fl)
  apply (subgoal_tac
    "ptr_val list + of_nat 8 \<in>
      {ptr_val list..+20} \<inter> {ptr_val list + 8..+20}")
   apply blast
  apply (rule IntI)
   apply (rule intvlI)
   apply simp
  apply (simp only: m0_word_of_nat_8)
  apply (rule intvl_self)
  apply simp
  done

text \<open>
  Target-gate B is the same fact at the exact validity guards emitted by
  AutoCorres for vListInitialise'/vListInsertEnd'.
\<close>

lemma m0_generated_sentinel_guard_conflict:
  assumes list_valid: "IS_VALID(xLIST_C) s (list :: xLIST_C ptr)"
  shows "\<not> IS_VALID(xLIST_ITEM_C) s (m0_sentinel list)"
proof
  assume sentinel_valid: "IS_VALID(xLIST_ITEM_C) s (m0_sentinel list)"
  have list_root: "root_ptr_valid (heap_typing s) list"
    using list_valid by (simp add: xLIST_C.ptr_valid.unfold)
  have sentinel_root: "root_ptr_valid (heap_typing s) (m0_sentinel list)"
    using sentinel_valid by (simp add: xLIST_ITEM_C.ptr_valid.unfold)
  show False
    using m0_sentinel_typed_roots_conflict
      [where d = "heap_typing s" and list = list, OF list_root sentinel_root] .
qed

text \<open>
  Operational consequence, deliberately scoped to states whose concrete
  cursor is the cast sentinel.  The generated body reads that cursor and then
  executes an xLIST_ITEM_C validity guard before its first heap modification.
\<close>

lemma m0_vListInsertEnd_at_sentinel_runs_to_top:
  assumes list_valid: "IS_VALID(xLIST_C) s (list :: xLIST_C ptr)"
    and index_is_sentinel:
      "pxIndex_C (heap_xLIST_C s list) = m0_sentinel list"
  shows "run (vListInsertEnd' list item) s = \<top>"
proof -
  have sentinel_invalid:
    "\<not> IS_VALID(xLIST_ITEM_C) s (m0_sentinel list)"
    using m0_generated_sentinel_guard_conflict[OF list_valid] .
  show ?thesis
    unfolding vListInsertEnd'_def
    using list_valid index_is_sentinel sentinel_invalid
    by (simp add: run_spec_monad)
qed

corollary m0_vListInsertEnd_at_sentinel_has_no_run:
  assumes list_valid: "IS_VALID(xLIST_C) s (list :: xLIST_C ptr)"
    and index_is_sentinel:
      "pxIndex_C (heap_xLIST_C s list) = m0_sentinel list"
  shows "\<not> (vListInsertEnd' list item \<bullet> s \<lbrace>Q\<rbrace>)"
  using m0_vListInsertEnd_at_sentinel_runs_to_top
    [OF list_valid index_is_sentinel]
  by (simp add: runs_to.rep_eq)

end
