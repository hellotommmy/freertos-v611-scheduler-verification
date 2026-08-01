theory List_V611_Raw_R4_Count_Index_Post
  imports "EAL6_FreeRTOS_V611_List_Raw_R4_Count_Index.List_V611_Raw_R4_Count_Index"
begin

text \<open>
  R4d checker gate: one source-order VCG for the count/cursor postcondition,
  after the pure projection ledger has been checked separately.
\<close>

theorem raw_vListRemove_singleton_count_index:
  "vListRemove' raw_item_ptr \<bullet>
     (raw_singleton_prestate base d h k owner)
   \<lbrace>\<lambda>r t.
      r = Result () \<and>
      uxNumberOfItems_C
        (h_val (hrs_mem (t_hrs_' t)) raw_list_ptr) = 0 \<and>
      pxIndex_C
        (h_val (hrs_mem (t_hrs_' t)) raw_list_ptr) =
          raw_sentinel_ptr raw_list_ptr
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
      raw_singleton_prestate_count
      raw_singleton_container_cast_back
      raw_singleton_prestate_list_guard
      raw_item_h_val_survives_sentinel_previous_field_update
      raw_item_h_val_survives_sentinel_next_field_update
      raw_list_index_survives_sentinel_previous_field_update
      raw_list_index_survives_sentinel_next_field_update
      raw_list_count_survives_sentinel_previous_field_update
      raw_list_count_survives_sentinel_next_field_update
      raw_list_index_after_whole_index_update
      raw_list_count_survives_whole_index_update
      raw_list_index_survives_item_container_update
      raw_list_count_survives_item_container_update
      raw_list_count_after_whole_count_modify
      raw_list_index_survives_whole_count_modify
      raw_remove_count_one_to_zero)
  apply (simp only: raw_sentinel_ptr_at_witness)
  done

end
