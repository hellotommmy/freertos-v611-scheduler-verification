theory List_V611_Raw_R6_Remove_Source_Effects
  imports "EAL6_FreeRTOS_V611_List_Raw_R6_Remove_Metadata.List_V611_Raw_R6_Remove_Metadata"
begin

text \<open>
  Single symbolic-execution gate for the general-N removal effect interface.
  All pure representation assembly is already checked in the parent theory.
\<close>

theorem raw_vListRemove_general_count_effect:
  assumes rel:
    "raw_xlist_rel (hrs_mem (t_hrs_' s)) lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "vListRemove' p \<bullet> s
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       uxNumberOfItems_C (h_val (hrs_mem (t_hrs_' t)) lp) =
         uxNumberOfItems_C (h_val (hrs_mem (t_hrs_' s)) lp) - 1
     \<rbrace>"
  unfolding vListRemove'_def
  apply runs_to_vcg
  apply (simp_all only: hrs_mem_update)
  apply ((rule
      raw_general_remove_previous_guard_after_first_unlink[OF rel member]
    | rule raw_general_remove_container_guard_after_two_unlinks_exact[
        OF rel member]
    | rule raw_general_remove_item_guard[OF rel member]
    | rule raw_general_remove_next_guard[OF rel member]
    | rule raw_general_remove_previous_guard[OF rel member]
    | rule raw_general_remove_container_list_guard[OF rel member])+)
  apply (fold raw_previous_field_ptr_def raw_next_field_ptr_def)
  apply (fold raw_source_unlink_first_def)
  apply (fold raw_source_unlink_two_def)
  apply (simp_all only: raw_source_unlink_two_container_cast[OF rel member])
  subgoal
    apply (fold raw_remove_taken_index_heap_def)
    apply (fold raw_remove_container_heap_def)
    apply (fold raw_remove_count_heap_def)
    apply (fold raw_remove_taken_suffix_heap_def)
    apply (rule raw_remove_taken_source_count_effect[OF rel member])
    done
  subgoal
    apply (fold raw_remove_container_heap_def)
    apply (fold raw_remove_count_heap_def)
    apply (fold raw_remove_plain_suffix_heap_def)
    apply (rule raw_remove_plain_source_count_effect[OF rel member])
    done
  done

text \<open>
  Strong source-semantics certificate: the generated C body produces exactly
  the explicit byte-heap transformer assembled in the parent theory.  Later
  representation facts should be projections of this theorem, not fresh
  symbolic executions of the function body.
\<close>

theorem raw_vListRemove_general_heap_effect:
  assumes rel:
    "raw_xlist_rel (hrs_mem (t_hrs_' s)) lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "vListRemove' p \<bullet> s
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       hrs_mem (t_hrs_' t) =
         raw_remove_concrete_heap (hrs_mem (t_hrs_' s)) p
     \<rbrace>"
  unfolding vListRemove'_def
  apply runs_to_vcg
  apply (simp_all only: hrs_mem_update)
  apply ((rule
      raw_general_remove_previous_guard_after_first_unlink[OF rel member]
    | rule raw_general_remove_container_guard_after_two_unlinks_exact[
        OF rel member]
    | rule raw_general_remove_item_guard[OF rel member]
    | rule raw_general_remove_next_guard[OF rel member]
    | rule raw_general_remove_previous_guard[OF rel member]
    | rule raw_general_remove_container_list_guard[OF rel member])+)
  apply (fold raw_previous_field_ptr_def raw_next_field_ptr_def)
  apply (fold raw_source_unlink_first_def)
  apply (fold raw_source_unlink_two_def)
  apply (simp_all only: raw_source_unlink_two_container_cast[OF rel member])
  apply (simp_all add:
      raw_source_unlink_two_container_cast[OF rel member]
      raw_remove_concrete_heap_def raw_remove_suffix_heap_def
      raw_remove_index_heap_def raw_remove_container_heap_def
      raw_remove_count_heap_def Let_def)
  done

end
