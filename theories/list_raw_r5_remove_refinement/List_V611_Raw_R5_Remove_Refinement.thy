theory List_V611_Raw_R5_Remove_Refinement
  imports
    "EAL6_FreeRTOS_V611_List_Raw_R5_Remove_Prestate.List_V611_Raw_R5_Remove_Prestate"
    "EAL6_FreeRTOS_V611_List_Raw_R4_Topology_Post.List_V611_Raw_R4_Topology_Post"
begin

text \<open>
  Fixed singleton-to-empty source-to-model simulation.  It combines two
  already checked source-order postcondition groups and does not reopen the
  generated vListRemove body.
\<close>

theorem raw_vListRemove_singleton_refines:
  "vListRemove' raw_item_ptr \<bullet>
     (raw_singleton_prestate base d h k owner)
   \<lbrace>\<lambda>r t.
      r = Result () \<and>
      raw_xlist_rel (hrs_mem (t_hrs_' t)) raw_list_ptr
        (list_remove_abs raw_item_ptr
          (raw_singleton_abs raw_item_ptr keys k))
    \<rbrace>"
proof -
  let ?f = "vListRemove' raw_item_ptr"
  let ?s0 = "raw_singleton_prestate base d h k owner"
  have grouped:
    "?f \<bullet> ?s0
     \<lbrace>\<lambda>r t.
       (r = Result () \<and>
        uxNumberOfItems_C
          (h_val (hrs_mem (t_hrs_' t)) raw_list_ptr) = 0 \<and>
        pxIndex_C
          (h_val (hrs_mem (t_hrs_' t)) raw_list_ptr) =
            raw_sentinel_ptr raw_list_ptr) \<and>
       (r = Result () \<and>
        xMINI_LIST_ITEM_C.pxNext_C
          (xListEnd_C (h_val (hrs_mem (t_hrs_' t)) raw_list_ptr)) =
            raw_sentinel_ptr raw_list_ptr \<and>
        xMINI_LIST_ITEM_C.pxPrevious_C
          (xListEnd_C (h_val (hrs_mem (t_hrs_' t)) raw_list_ptr)) =
            raw_sentinel_ptr raw_list_ptr \<and>
        pvContainer_C
          (h_val (hrs_mem (t_hrs_' t)) raw_item_ptr) = NULL)
     \<rbrace>"
    using raw_vListRemove_singleton_count_index[
        where base=base and d=d and h=h and k=k and owner=owner]
      raw_vListRemove_singleton_topology_container[
        where base=base and d=d and h=h and k=k and owner=owner]
    by (simp only: runs_to_conj)
  show ?thesis
    apply (rule runs_to_weaken[OF grouped])
    apply clarsimp
    apply (rule raw_xlist_rel_emptyI)
    apply (rule raw_fixed_empty_layout)
    apply assumption
    apply (simp add: raw_end_item_def)
    apply (simp add: raw_end_item_def)
    apply (simp add: raw_end_item_def)
    done
qed

end
