theory Scheduler_Remove_Translation_General
  imports
    "EAL6_FreeRTOS_V611_Scheduler_P2_Remove_Source.Scheduler_P2_Remove_Source"
    "EAL6_FreeRTOS_V611_Scheduler_Remove_Unlinked_Ownership.Scheduler_Remove_Unlinked_Ownership"
begin

text \<open>
  Gate-H scheduler-translation source theorem.  The quantified list may have
  any finite valid ring represented by @{const raw_xlist_rel}; the removed item
  may occupy any member position, and the relation's cursor is unrestricted.
  In particular, no singleton, P2, priority, concrete address, or additional
  anti-alias premise occurs below.  The generated scheduler body is opened
  exactly once, in the exact-state theorem; the corollary is purely semantic.
\<close>

theorem scheduler_vListRemove_general_exact_state:
  fixes s :: Scheduler_V611_Parse.globals
    and lp :: "Scheduler_V611_Parse.xLIST_C ptr"
    and p :: "Scheduler_V611_Parse.xLIST_ITEM_C ptr"
  assumes rel:
      "raw_xlist_rel
        (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
        (abi_list_ptr lp) xs"
    and member: "abi_item_ptr p \<in> set (ring xs)"
  shows
    "Scheduler_V611_Delay_Translation.vListRemove' p \<bullet> s
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       t = scheduler_mem_state
         (raw_remove_concrete_heap
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
           (abi_item_ptr p)) s
     \<rbrace>"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s)"
  note guards = scheduler_remove_dynamic_guards[OF rel member]
  have item_guard: "c_guard p"
    using guards by blast
  have next_guard:
    "c_guard
      (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C (h_val ?h p))"
    using guards by blast
  have previous_guard:
    "c_guard
      (Scheduler_V611_Parse.xLIST_ITEM_C.pxPrevious_C
        (h_val (scheduler_source_unlink_first ?h p) p))"
    by (rule scheduler_remove_previous_guard_after_first_unlink[
          OF rel member])
  have container_guard:
    "c_guard
      (PTR_COERCE(unit \<rightarrow> Scheduler_V611_Parse.xLIST_C)
        (Scheduler_V611_Parse.xLIST_ITEM_C.pvContainer_C
          (h_val (scheduler_source_unlink_two ?h p) p)))"
    by (rule scheduler_remove_container_guard_after_two_unlinks[
          OF rel member])
  note container_guard_expanded =
    container_guard[unfolded scheduler_source_unlink_two_def Let_def]
  have concrete:
    "raw_remove_concrete_heap ?h (abi_item_ptr p) =
     scheduler_remove_concrete_heap ?h p"
    using scheduler_remove_concrete_heap_abi[
      OF item_guard container_guard]
    by simp
  show ?thesis
    unfolding Scheduler_V611_Delay_Translation.vListRemove'_def
    apply runs_to_vcg
    apply (simp_all only: hrs_mem_update)
    apply (fold scheduler_source_unlink_first_def)
    apply ((rule
        previous_guard
      | rule container_guard_expanded
      | rule item_guard
      | rule next_guard)+)
    apply (simp_all only: concrete)
    apply (all \<open>cases s\<close>)
    apply (all \<open>simp add:
        scheduler_mem_state_def
        hrs_mem_update_def
        hrs_mem_def
        scheduler_remove_concrete_heap_def
        scheduler_source_unlink_two_def
        scheduler_source_unlink_first_def
        scheduler_remove_suffix_heap_def
        scheduler_remove_index_heap_def
        scheduler_remove_container_heap_def
        scheduler_remove_count_heap_def
        concrete Let_def
        split: prod.splits\<close>)
    done
qed

corollary scheduler_vListRemove_general_unlinked_effect:
  fixes s :: Scheduler_V611_Parse.globals
    and lp :: "Scheduler_V611_Parse.xLIST_C ptr"
    and p :: "Scheduler_V611_Parse.xLIST_ITEM_C ptr"
  assumes rel:
      "raw_xlist_rel
        (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
        (abi_list_ptr lp) xs"
    and member: "abi_item_ptr p \<in> set (ring xs)"
  shows
    "Scheduler_V611_Delay_Translation.vListRemove' p \<bullet> s
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       raw_remove_unlinked_effect
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' t))
         (abi_list_ptr lp) xs (abi_item_ptr p)
     \<rbrace>"
proof -
  note exact = scheduler_vListRemove_general_exact_state[OF rel member]
  note effect = raw_remove_concrete_heap_unlinked_effect[OF rel member]
  show ?thesis
    apply (rule runs_to_weaken[OF exact])
    using effect by auto
qed

end
