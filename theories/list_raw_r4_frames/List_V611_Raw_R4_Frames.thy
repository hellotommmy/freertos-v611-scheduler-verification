theory List_V611_Raw_R4_Frames
  imports "EAL6_FreeRTOS_V611_List_Raw_R4_Topology_Post.List_V611_Raw_R4_Topology_Post"
begin

text \<open>
  R4f item-frame bricks.  Removal clears only pvContainer_C: the source leaves
  the detached item's links, key, and owner unchanged.
\<close>

lemma raw_singleton_prestate_item_key:
  "xLIST_ITEM_C.xItemValue_C
     (h_val
       (hrs_mem
         (t_hrs_' (raw_singleton_prestate base d h k owner)))
       raw_item_ptr) = k"
  unfolding raw_singleton_prestate_def raw_singleton_preheap_def
    raw_singleton_list_value_def raw_linked_item_value_def
    raw_empty_list_value_def raw_fresh_item_value_def
  by (simp add: hrs_mem_def h_val_heap_update)

lemma raw_singleton_prestate_item_owner:
  "pvOwner_C
     (h_val
       (hrs_mem
         (t_hrs_' (raw_singleton_prestate base d h k owner)))
       raw_item_ptr) = owner"
  unfolding raw_singleton_prestate_def raw_singleton_preheap_def
    raw_singleton_list_value_def raw_linked_item_value_def
    raw_empty_list_value_def raw_fresh_item_value_def
  by (simp add: hrs_mem_def h_val_heap_update)

lemma raw_item_key_after_container_value_update:
  "xLIST_ITEM_C.xItemValue_C
     (h_val
       (heap_update raw_item_ptr
         (pvContainer_C_update (\<lambda>_. c) v) h)
       raw_item_ptr) = xLIST_ITEM_C.xItemValue_C v"
  by (simp add: h_val_heap_update)

lemma raw_item_owner_after_container_value_update:
  "pvOwner_C
     (h_val
       (heap_update raw_item_ptr
         (pvContainer_C_update (\<lambda>_. c) v) h)
       raw_item_ptr) = pvOwner_C v"
  by (simp add: h_val_heap_update)

lemma raw_sentinel_next_field_update_tail8_pointwise:
  assumes tail: "a \<in> {raw_sentinel_tail_addr..+8}"
  shows
    "heap_update
       (PTR(xLIST_ITEM_C ptr)
         &(raw_sentinel_ptr raw_list_ptr\<rightarrow>[''pxNext_C''])) q h a =
     h a"
  using raw_sentinel_whole_next_update_tail8_pointwise[
    OF tail, where q=q and h=h]
  by (simp only: raw_sentinel_whole_next_update_to_field)

lemma raw_sentinel_next_field_update_canary:
  "heap_update
     (PTR(xLIST_ITEM_C ptr)
       &(raw_sentinel_ptr raw_list_ptr\<rightarrow>[''pxNext_C''])) q h
     raw_canary_addr = h raw_canary_addr"
  using raw_sentinel_next_update_canary[where q=q and h=h]
  by (simp only: raw_sentinel_whole_next_update_to_field)

end
