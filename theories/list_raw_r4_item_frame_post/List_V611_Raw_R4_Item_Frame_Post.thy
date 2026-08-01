theory List_V611_Raw_R4_Item_Frame_Post
  imports "EAL6_FreeRTOS_V611_List_Raw_R4_Frames.List_V611_Raw_R4_Frames"
begin

text \<open>
  One grouped item-frame VCG: links remain stale-to-sentinel by source design,
  while key and owner retain their explicit witness values.
\<close>

theorem raw_vListRemove_singleton_item_frame:
  "vListRemove' raw_item_ptr \<bullet>
     (raw_singleton_prestate base d h k owner)
   \<lbrace>\<lambda>r t.
      r = Result () \<and>
      xLIST_ITEM_C.pxNext_C
        (h_val (hrs_mem (t_hrs_' t)) raw_item_ptr) =
          raw_sentinel_ptr raw_list_ptr \<and>
      xLIST_ITEM_C.pxPrevious_C
        (h_val (hrs_mem (t_hrs_' t)) raw_item_ptr) =
          raw_sentinel_ptr raw_list_ptr \<and>
      xLIST_ITEM_C.xItemValue_C
        (h_val (hrs_mem (t_hrs_' t)) raw_item_ptr) = k \<and>
      pvOwner_C
        (h_val (hrs_mem (t_hrs_' t)) raw_item_ptr) = owner
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
      raw_singleton_prestate_item_key
      raw_singleton_prestate_item_owner
      raw_item_h_val_survives_sentinel_previous_field_update
      raw_item_h_val_survives_sentinel_next_field_update
      raw_list_index_survives_sentinel_previous_field_update
      raw_list_index_survives_sentinel_next_field_update
      raw_item_h_val_after_list_update_direct
      raw_item_next_after_container_value_update
      raw_item_previous_after_container_value_update
      raw_item_key_after_container_value_update
      raw_item_owner_after_container_value_update)
  apply (simp_all only: raw_sentinel_ptr_at_witness)
  done

end
