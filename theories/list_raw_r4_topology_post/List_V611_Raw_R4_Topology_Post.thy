theory List_V611_Raw_R4_Topology_Post
  imports "EAL6_FreeRTOS_V611_List_Raw_R4_Topology.List_V611_Raw_R4_Topology"
begin

text \<open>
  R4e checker gate: the singleton sentinel becomes self-linked and the
  removed item's ownership container is cleared.  Detached item links are a
  separate preservation theorem, because the C source does not clear them.
\<close>

theorem raw_vListRemove_singleton_topology_container:
  "vListRemove' raw_item_ptr \<bullet>
     (raw_singleton_prestate base d h k owner)
   \<lbrace>\<lambda>r t.
      r = Result () \<and>
      xMINI_LIST_ITEM_C.pxNext_C
        (xListEnd_C (h_val (hrs_mem (t_hrs_' t)) raw_list_ptr)) =
          raw_sentinel_ptr raw_list_ptr \<and>
      xMINI_LIST_ITEM_C.pxPrevious_C
        (xListEnd_C (h_val (hrs_mem (t_hrs_' t)) raw_list_ptr)) =
          raw_sentinel_ptr raw_list_ptr \<and>
      pvContainer_C
        (h_val (hrs_mem (t_hrs_' t)) raw_item_ptr) = NULL
    \<rbrace>"
  unfolding vListRemove'_def
  apply runs_to_vcg
  apply (simp_all only: hrs_mem_update
      raw_item_ptr_guard
      raw_sentinel_ptr_guard
      raw_list_ptr_guard
      raw_singleton_prestate_item_next
      raw_singleton_prestate_item_previous
      raw_singleton_prestate_item_container
      raw_singleton_prestate_index
      raw_singleton_container_cast_back
      raw_singleton_prestate_list_guard
      raw_item_h_val_survives_sentinel_previous_field_update
      raw_item_h_val_survives_sentinel_next_field_update
      raw_list_index_survives_sentinel_previous_field_update
      raw_list_index_survives_sentinel_next_field_update
      raw_sentinel_next_after_two_unlink_writes
      raw_sentinel_previous_after_two_unlink_writes
      raw_sentinel_next_survives_whole_index_update
      raw_sentinel_previous_survives_whole_index_update
      raw_sentinel_next_survives_item_container_update
      raw_sentinel_previous_survives_item_container_update
      raw_sentinel_next_survives_item_container_value_update
      raw_sentinel_previous_survives_item_container_value_update
      raw_sentinel_next_survives_whole_count_modify
      raw_sentinel_previous_survives_whole_count_modify
      raw_item_container_after_whole_container_update
      raw_item_container_after_container_value_update
      raw_item_h_val_after_list_update_direct)
  apply (simp_all only: raw_sentinel_ptr_at_witness)
  done

end
