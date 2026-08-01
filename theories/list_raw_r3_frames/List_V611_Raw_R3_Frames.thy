theory List_V611_Raw_R3_Frames
  imports "EAL6_FreeRTOS_V611_List_Raw_R3_Topology_Post.List_V611_Raw_R3_Topology_Post"
begin

text \<open>
  R3g adds preservation evidence in separate VCGs.  This first gate records
  only the detached item's key and owner.
\<close>

lemma raw_insert_end_prestate_item_key:
  "xLIST_ITEM_C.xItemValue_C
     (h_val
       (hrs_mem
         (t_hrs_' (raw_insert_end_prestate base d h k owner)))
       raw_item_ptr) = k"
  unfolding raw_insert_end_prestate_def raw_insert_end_preheap_def
    raw_empty_list_value_def raw_fresh_item_value_def
  by (simp add: hrs_mem_def h_val_heap_update)

lemma raw_insert_end_prestate_item_owner:
  "pvOwner_C
     (h_val
       (hrs_mem
         (t_hrs_' (raw_insert_end_prestate base d h k owner)))
       raw_item_ptr) = owner"
  unfolding raw_insert_end_prestate_def raw_insert_end_preheap_def
    raw_empty_list_value_def raw_fresh_item_value_def
  by (simp add: hrs_mem_def h_val_heap_update)

lemma raw_vListInsertEnd_empty_key_owner:
  "vListInsertEnd' raw_list_ptr raw_item_ptr \<bullet>
     (raw_insert_end_prestate base d h k owner)
   \<lbrace>\<lambda>r t.
      r = Result () \<and>
      xLIST_ITEM_C.xItemValue_C
        (h_val (hrs_mem (t_hrs_' t)) raw_item_ptr) = k \<and>
      pvOwner_C
        (h_val (hrs_mem (t_hrs_' t)) raw_item_ptr) = owner
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
      h_val_heap_update
      raw_insert_end_prestate_item_key
      raw_insert_end_prestate_item_owner)
  apply simp_all
  apply (rule raw_insert_end_prestate_item_key)
  apply (rule raw_insert_end_prestate_item_owner)
  done

end
