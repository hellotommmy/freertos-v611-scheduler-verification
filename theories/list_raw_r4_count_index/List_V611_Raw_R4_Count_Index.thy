theory List_V611_Raw_R4_Count_Index
  imports "EAL6_FreeRTOS_V611_List_Raw_R4_Run.List_V611_Raw_R4_Run"
begin

text \<open>
  R4d helper ledger for the cursor-repair and count-decrement suffix.  These
  are pure heap projection facts; vListRemove' is not unfolded here.
\<close>

lemma raw_remove_singleton_count_after_unlink:
  assumes singleton: "raw_singleton_heap_fields h"
  shows
    "uxNumberOfItems_C
       (h_val
         (heap_update
           (PTR(xLIST_ITEM_C ptr)
             &(raw_sentinel_ptr raw_list_ptr\<rightarrow>[''pxNext_C'']))
           (raw_sentinel_ptr raw_list_ptr)
           (heap_update
             (PTR(xLIST_ITEM_C ptr)
               &(raw_sentinel_ptr raw_list_ptr\<rightarrow>[''pxPrevious_C'']))
             (raw_sentinel_ptr raw_list_ptr) h))
         raw_list_ptr) = 1"
  apply (simp only: raw_list_count_survives_sentinel_next_field_update
      raw_list_count_survives_sentinel_previous_field_update)
  using singleton
  unfolding raw_singleton_heap_fields_def
  by blast

lemma raw_list_index_after_whole_index_update:
  "pxIndex_C
     (h_val
       (heap_update raw_list_ptr
         (pxIndex_C_update (\<lambda>_. q) (h_val h raw_list_ptr)) h)
       raw_list_ptr) = q"
  by (simp add: h_val_heap_update)

lemma raw_list_count_survives_whole_index_update:
  "uxNumberOfItems_C
     (h_val
       (heap_update raw_list_ptr
         (pxIndex_C_update (\<lambda>_. q) (h_val h raw_list_ptr)) h)
       raw_list_ptr) = uxNumberOfItems_C (h_val h raw_list_ptr)"
  by (simp add: h_val_heap_update)

lemma raw_list_index_survives_item_container_update:
  "pxIndex_C
     (h_val
       (heap_update raw_item_ptr
         (pvContainer_C_update (\<lambda>_. c) (h_val h raw_item_ptr)) h)
       raw_list_ptr) = pxIndex_C (h_val h raw_list_ptr)"
  by (simp only: raw_list_h_val_after_item_update_direct)

lemma raw_list_count_survives_item_container_update:
  "uxNumberOfItems_C
     (h_val
       (heap_update raw_item_ptr
         (pvContainer_C_update (\<lambda>_. c) (h_val h raw_item_ptr)) h)
       raw_list_ptr) = uxNumberOfItems_C (h_val h raw_list_ptr)"
  by (simp only: raw_list_h_val_after_item_update_direct)

lemma raw_list_count_after_whole_count_update:
  "uxNumberOfItems_C
     (h_val
       (heap_update raw_list_ptr
         (uxNumberOfItems_C_update (\<lambda>_. n) (h_val h raw_list_ptr)) h)
       raw_list_ptr) = n"
  by (simp add: h_val_heap_update)

lemma raw_list_count_after_whole_count_modify:
  "uxNumberOfItems_C
     (h_val
       (heap_update raw_list_ptr
         (uxNumberOfItems_C_update f (h_val h raw_list_ptr)) h)
       raw_list_ptr) = f (uxNumberOfItems_C (h_val h raw_list_ptr))"
  by (simp add: h_val_heap_update)

lemma raw_list_index_survives_whole_count_update:
  "pxIndex_C
     (h_val
       (heap_update raw_list_ptr
         (uxNumberOfItems_C_update (\<lambda>_. n) (h_val h raw_list_ptr)) h)
       raw_list_ptr) = pxIndex_C (h_val h raw_list_ptr)"
  by (simp add: h_val_heap_update)

lemma raw_list_index_survives_whole_count_modify:
  "pxIndex_C
     (h_val
       (heap_update raw_list_ptr
         (uxNumberOfItems_C_update f (h_val h raw_list_ptr)) h)
       raw_list_ptr) = pxIndex_C (h_val h raw_list_ptr)"
  by (simp add: h_val_heap_update)

end
