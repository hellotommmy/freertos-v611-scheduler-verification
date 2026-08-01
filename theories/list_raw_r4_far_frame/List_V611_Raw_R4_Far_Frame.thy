theory List_V611_Raw_R4_Far_Frame
  imports "EAL6_FreeRTOS_V611_List_Raw_R4_Tail_Frame_Post.List_V611_Raw_R4_Tail_Frame_Post"
begin

text \<open>
  R4f external-byte and heap-typing frames, grouped after the per-write
  locality facts are checker-green.
\<close>

theorem raw_vListRemove_singleton_canary_htd:
  "vListRemove' raw_item_ptr \<bullet>
     (raw_singleton_prestate base d h k owner)
   \<lbrace>\<lambda>r t.
      r = Result () \<and>
      hrs_mem (t_hrs_' t) raw_canary_addr =
        hrs_mem
          (t_hrs_' (raw_singleton_prestate base d h k owner))
          raw_canary_addr \<and>
      hrs_htd (t_hrs_' t) =
        hrs_htd
          (t_hrs_' (raw_singleton_prestate base d h k owner))
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
      raw_sentinel_previous_field_update_canary
      raw_sentinel_next_field_update_canary
      raw_list_heap_update_canary
      raw_item_heap_update_canary)
  done

end
