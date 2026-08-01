theory List_V611_Raw_R3_Far_Frame
  imports "EAL6_FreeRTOS_V611_List_Raw_R3_Tail_Frame_Post.List_V611_Raw_R3_Tail_Frame_Post"
begin

text \<open>
  Final split frame gate: preserve the byte canary at 0x3000 and the heap
  typing component.  Sentinel writes are first reduced to embedded-list
  writes, then reuse the R1 canary fact.
\<close>

lemma raw_sentinel_previous_field_update_canary:
  "heap_update
     (PTR(xLIST_ITEM_C ptr)
       &(raw_sentinel_ptr raw_list_ptr\<rightarrow>[''pxPrevious_C''])) q h
     raw_canary_addr = h raw_canary_addr"
  apply (subst raw_sentinel_previous_field_update_to_list)
  apply (rule raw_list_heap_update_canary)
  done

lemma raw_sentinel_next_update_canary:
  "heap_update (raw_sentinel_ptr raw_list_ptr)
     (xLIST_ITEM_C.pxNext_C_update (\<lambda>_. q)
       (h_val h (raw_sentinel_ptr raw_list_ptr))) h
     raw_canary_addr = h raw_canary_addr"
  apply (subst raw_sentinel_whole_next_update_to_list)
  apply (rule raw_list_heap_update_canary)
  done

lemma raw_vListInsertEnd_empty_canary:
  "vListInsertEnd' raw_list_ptr raw_item_ptr \<bullet>
     (raw_insert_end_prestate base d h k owner)
   \<lbrace>\<lambda>r t.
      r = Result () \<and>
      hrs_mem (t_hrs_' t) raw_canary_addr =
        hrs_mem
          (t_hrs_' (raw_insert_end_prestate base d h k owner))
          raw_canary_addr
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
      raw_list_heap_update_canary
      raw_item_heap_update_canary
      raw_sentinel_previous_field_update_canary
      raw_sentinel_next_update_canary)
  done

lemma raw_vListInsertEnd_empty_htd:
  "vListInsertEnd' raw_list_ptr raw_item_ptr \<bullet>
     (raw_insert_end_prestate base d h k owner)
   \<lbrace>\<lambda>r t.
      r = Result () \<and>
      hrs_htd (t_hrs_' t) =
        hrs_htd
          (t_hrs_' (raw_insert_end_prestate base d h k owner))
    \<rbrace>"
  unfolding vListInsertEnd'_def
  apply runs_to_vcg
  apply (rule raw_insert_end_prestate_index_guard)
  apply (simp only: hrs_mem_update)
  apply (rule raw_prestate_index_next_guard_after_item_updates)
  done

end
