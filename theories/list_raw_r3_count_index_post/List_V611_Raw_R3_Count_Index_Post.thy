theory List_V611_Raw_R3_Count_Index_Post
  imports "EAL6_FreeRTOS_V611_List_Raw_R3_Count_Index.List_V611_Raw_R3_Count_Index"
begin

text \<open>
  The R3e VCG combines only checker-green guard and count-frame bricks.  Its
  postcondition deliberately stops at list count and cursor.
\<close>

lemma raw_vListInsertEnd_empty_count_index:
  "vListInsertEnd' raw_list_ptr raw_item_ptr \<bullet>
     (raw_insert_end_prestate base d h k owner)
   \<lbrace>\<lambda>r t.
      r = Result () \<and>
      uxNumberOfItems_C
        (h_val (hrs_mem (t_hrs_' t)) raw_list_ptr) = 1 \<and>
      pxIndex_C
        (h_val (hrs_mem (t_hrs_' t)) raw_list_ptr) = raw_item_ptr
    \<rbrace>"
  unfolding vListInsertEnd'_def
  apply runs_to_vcg
  apply (rule raw_insert_end_prestate_index_guard)
  apply (simp only: hrs_mem_update)
  apply (rule raw_prestate_index_next_guard_after_item_updates)
  apply (simp only: hrs_mem_update
      raw_insert_end_prestate_index
      raw_sentinel_h_val_after_item_update_direct
      raw_insert_end_prestate_sentinel_next_raw
      raw_list_h_val_after_item_update_direct
      raw_list_count_survives_sentinel_next_update
      raw_list_count_survives_sentinel_previous_field_update
      raw_insert_end_prestate_count)
  done

end
