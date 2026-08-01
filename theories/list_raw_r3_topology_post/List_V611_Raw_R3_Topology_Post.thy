theory List_V611_Raw_R3_Topology_Post
  imports "EAL6_FreeRTOS_V611_List_Raw_R3_Topology.List_V611_Raw_R3_Topology"
begin

text \<open>
  The topology postconditions are added here only after their pure heap
  read-after-write bricks are checker-green.
\<close>

lemma raw_vListInsertEnd_empty_sentinel_links:
  "vListInsertEnd' raw_list_ptr raw_item_ptr \<bullet>
     (raw_insert_end_prestate base d h k owner)
   \<lbrace>\<lambda>r t.
      r = Result () \<and>
      xMINI_LIST_ITEM_C.pxNext_C
        (xListEnd_C (h_val (hrs_mem (t_hrs_' t)) raw_list_ptr)) =
          raw_item_ptr \<and>
      xMINI_LIST_ITEM_C.pxPrevious_C
        (xListEnd_C (h_val (hrs_mem (t_hrs_' t)) raw_list_ptr)) =
          raw_item_ptr
    \<rbrace>"
  unfolding vListInsertEnd'_def
  apply runs_to_vcg
  apply (rule raw_insert_end_prestate_index_guard)
  apply (simp only: hrs_mem_update)
  apply (rule raw_prestate_index_next_guard_after_item_updates)
  apply (simp_all only: hrs_mem_update
      raw_insert_end_prestate_index
      raw_sentinel_h_val_after_item_update_direct
      raw_insert_end_prestate_sentinel_next_raw
      raw_sentinel_next_after_whole_next_update
      raw_sentinel_previous_after_previous_then_next)
  done

lemma raw_vListInsertEnd_empty_item_links:
  "vListInsertEnd' raw_list_ptr raw_item_ptr \<bullet>
     (raw_insert_end_prestate base d h k owner)
   \<lbrace>\<lambda>r t.
      r = Result () \<and>
      xLIST_ITEM_C.pxNext_C
        (h_val (hrs_mem (t_hrs_' t)) raw_item_ptr) =
          raw_sentinel_ptr raw_list_ptr \<and>
      xLIST_ITEM_C.pxPrevious_C
        (h_val (hrs_mem (t_hrs_' t)) raw_item_ptr) =
          raw_sentinel_ptr raw_list_ptr
    \<rbrace>"
  unfolding vListInsertEnd'_def
  apply runs_to_vcg
  apply (rule raw_insert_end_prestate_index_guard)
  apply (simp only: hrs_mem_update)
  apply (rule raw_prestate_index_next_guard_after_item_updates)
  apply (simp_all only: hrs_mem_update
      raw_insert_end_prestate_index
      raw_sentinel_h_val_after_item_update_direct
      raw_insert_end_prestate_sentinel_next_raw
      raw_item_h_val_after_list_update_direct
      raw_item_h_val_after_sentinel_update_direct
      raw_item_h_val_survives_sentinel_previous_field_update
      h_val_heap_update)
  apply simp_all
  done

lemma raw_vListInsertEnd_empty_container:
  "vListInsertEnd' raw_list_ptr raw_item_ptr \<bullet>
     (raw_insert_end_prestate base d h k owner)
   \<lbrace>\<lambda>r t.
      r = Result () \<and>
      pvContainer_C
        (h_val (hrs_mem (t_hrs_' t)) raw_item_ptr) =
          PTR_COERCE(xLIST_C \<rightarrow> unit) raw_list_ptr
    \<rbrace>"
  unfolding vListInsertEnd'_def
  apply runs_to_vcg
  apply (rule raw_insert_end_prestate_index_guard)
  apply (simp only: hrs_mem_update)
  apply (rule raw_prestate_index_next_guard_after_item_updates)
  apply (simp_all only: hrs_mem_update
      raw_item_h_val_after_list_update_direct
      h_val_heap_update)
  apply simp_all
  done

end
