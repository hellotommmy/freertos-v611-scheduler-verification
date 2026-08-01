theory List_V611_Raw_R4_Run
  imports "EAL6_FreeRTOS_V611_List_Raw_R4_Locality.List_V611_Raw_R4_Locality"
begin

text \<open>
  R4c opens the generated vListRemove' monad only for the weakest positive
  execution gate.  All pointer, operand, and guard obligations are discharged
  by the separately checked R4b bricks.
\<close>

theorem raw_vListRemove_singleton_result:
  "vListRemove' raw_item_ptr \<bullet>
     (raw_singleton_prestate base d h k owner)
   \<lbrace>\<lambda>r t. r = Result ()\<rbrace>"
  unfolding vListRemove'_def
  apply runs_to_vcg
  apply (simp_all only: hrs_mem_update
      raw_singleton_prestate_item_next
      raw_singleton_prestate_item_previous
      raw_item_h_val_survives_sentinel_previous_field_update
      raw_item_h_val_survives_sentinel_next_field_update
      raw_item_ptr_guard
      raw_sentinel_ptr_guard
      raw_singleton_prestate_list_guard_after_unlink)
  apply (rule raw_singleton_prestate_list_guard)
  done

end
