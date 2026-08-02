theory Scheduler_Ordered_Insert_Generated_Capstone
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Ordered_Insert_General_Loop.Scheduler_Ordered_Insert_General_Loop"
    "EAL6_FreeRTOS_V611_Scheduler_Universal_Ordered_Insert_Composition.Scheduler_Universal_Ordered_Insert_Composition"
begin

text \<open>
  First source-level Gate-L capstone for ordered insertion.  The theorem joins
  actual execution of the generated scheduler vListInsert body to the
  capacity-free ordered raw-list post-relation and the exact six-field
  external frame.  Its only semantic premises are the ordered pre-relation and
  insertion freshness.  No non-empty-ring or neighbour-distinctness premise is
  present, so the legal empty-ring sentinel alias remains admitted.

  This theorem does not close Gate L: generated insert-end exact framing and
  scheduler-family Generic/Event frames remain separate obligations.
\<close>

theorem scheduler_vListInsert_ordered_general_source_capstone:
  fixes s :: Scheduler_V611_Parse.globals
  assumes ordered:
      "raw_ordered_xlist_rel
        (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
        (abi_list_ptr lp) xs"
    and fresh:
      "raw_fresh_for_insert (abi_list_ptr lp) (ring xs)
        (abi_item_ptr p)"
  shows
    "Scheduler_V611_Delay_Translation.vListInsert' lp p \<bullet> s
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       raw_ordered_xlist_rel
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' t))
         (abi_list_ptr lp)
         (list_insert_ordered_abs (abi_item_ptr p)
           (raw_key_at
             (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
             (abi_item_ptr p)) xs) \<and>
       (\<forall>a.
          a \<notin> raw_ordered_insert_general_exact_write_footprint
            (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
            (abi_list_ptr lp) xs (abi_item_ptr p)
          \<longrightarrow>
          hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' t) a =
            hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s) a)
     \<rbrace>"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s)"
  let ?rp = "abi_item_ptr p"
  let ?rlp = "abi_list_ptr lp"
  let ?h' = "raw_ordered_insert_general_heap ?h ?rlp xs ?rp"
  note execution = scheduler_vListInsert_ordered_general_exact_state[
    OF ordered fresh]
  have relation:
    "raw_ordered_xlist_rel ?h' ?rlp
       (list_insert_ordered_abs ?rp (raw_key_at ?h ?rp) xs)"
    by (rule raw_ordered_insert_general_transformer_refines_unconditionally[
          OF ordered fresh])
  have raw_relation: "raw_xlist_rel ?h ?rlp xs"
    using ordered by (simp add: raw_ordered_xlist_rel_def)
  have frame:
    "\<forall>a.
       a \<notin> raw_ordered_insert_general_exact_write_footprint
         ?h ?rlp xs ?rp
       \<longrightarrow> ?h' a = ?h a"
  proof (intro allI impI)
    fix a
    assume outside:
      "a \<notin> raw_ordered_insert_general_exact_write_footprint
         ?h ?rlp xs ?rp"
    show "?h' a = ?h a"
      by (rule raw_ordered_insert_general_heap_exact_external_frame[
            OF raw_relation fresh outside])
  qed
  show ?thesis
    apply (rule runs_to_weaken[OF execution])
    using relation frame by auto
qed

end
