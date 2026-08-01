theory List_V611_Raw_R4_Topology
  imports "EAL6_FreeRTOS_V611_List_Raw_R4_Count_Index_Post.List_V611_Raw_R4_Count_Index_Post"
begin

text \<open>
  R4e pure projection ledger for the two unlink writes and the three suffix
  updates.  This theory fixes topology/container readback before reopening
  the generated monad.
\<close>

lemma raw_sentinel_next_after_next_field_update:
  "xMINI_LIST_ITEM_C.pxNext_C
     (xListEnd_C
       (h_val
         (heap_update
           (PTR(xLIST_ITEM_C ptr)
             &(raw_sentinel_ptr raw_list_ptr\<rightarrow>[''pxNext_C''])) q h)
         raw_list_ptr)) = q"
  apply (subst raw_sentinel_next_field_update_to_list)
  apply (simp add: raw_sentinel_mini_value)
  done

lemma raw_sentinel_previous_survives_next_field_update:
  "xMINI_LIST_ITEM_C.pxPrevious_C
     (xListEnd_C
       (h_val
         (heap_update
           (PTR(xLIST_ITEM_C ptr)
             &(raw_sentinel_ptr raw_list_ptr\<rightarrow>[''pxNext_C''])) q h)
         raw_list_ptr)) =
   xMINI_LIST_ITEM_C.pxPrevious_C
     (xListEnd_C (h_val h raw_list_ptr))"
  apply (subst raw_sentinel_next_field_update_to_list)
  apply (simp add: raw_sentinel_mini_value)
  done

lemma raw_sentinel_next_after_two_unlink_writes:
  "xMINI_LIST_ITEM_C.pxNext_C
     (xListEnd_C
       (h_val
         (heap_update
           (PTR(xLIST_ITEM_C ptr)
             &(raw_sentinel_ptr raw_list_ptr\<rightarrow>[''pxNext_C''])) qn
           (heap_update
             (PTR(xLIST_ITEM_C ptr)
               &(raw_sentinel_ptr raw_list_ptr\<rightarrow>[''pxPrevious_C'']))
             qp h))
         raw_list_ptr)) = qn"
  by (rule raw_sentinel_next_after_next_field_update)

lemma raw_sentinel_previous_after_two_unlink_writes:
  "xMINI_LIST_ITEM_C.pxPrevious_C
     (xListEnd_C
       (h_val
         (heap_update
           (PTR(xLIST_ITEM_C ptr)
             &(raw_sentinel_ptr raw_list_ptr\<rightarrow>[''pxNext_C''])) qn
           (heap_update
             (PTR(xLIST_ITEM_C ptr)
               &(raw_sentinel_ptr raw_list_ptr\<rightarrow>[''pxPrevious_C'']))
             qp h))
         raw_list_ptr)) = qp"
  apply (subst raw_sentinel_previous_survives_next_field_update)
  apply (rule raw_sentinel_previous_after_previous_field_update)
  done

lemma raw_sentinel_next_survives_whole_index_update:
  "xMINI_LIST_ITEM_C.pxNext_C
     (xListEnd_C
       (h_val
         (heap_update raw_list_ptr
           (pxIndex_C_update (\<lambda>_. q) (h_val h raw_list_ptr)) h)
         raw_list_ptr)) =
   xMINI_LIST_ITEM_C.pxNext_C
     (xListEnd_C (h_val h raw_list_ptr))"
  by (simp add: h_val_heap_update)

lemma raw_sentinel_previous_survives_whole_index_update:
  "xMINI_LIST_ITEM_C.pxPrevious_C
     (xListEnd_C
       (h_val
         (heap_update raw_list_ptr
           (pxIndex_C_update (\<lambda>_. q) (h_val h raw_list_ptr)) h)
         raw_list_ptr)) =
   xMINI_LIST_ITEM_C.pxPrevious_C
     (xListEnd_C (h_val h raw_list_ptr))"
  by (simp add: h_val_heap_update)

lemma raw_sentinel_next_survives_item_container_update:
  "xMINI_LIST_ITEM_C.pxNext_C
     (xListEnd_C
       (h_val
         (heap_update raw_item_ptr
           (pvContainer_C_update (\<lambda>_. c) (h_val h raw_item_ptr)) h)
         raw_list_ptr)) =
   xMINI_LIST_ITEM_C.pxNext_C
     (xListEnd_C (h_val h raw_list_ptr))"
  by (simp only: raw_list_h_val_after_item_update_direct)

lemma raw_sentinel_previous_survives_item_container_update:
  "xMINI_LIST_ITEM_C.pxPrevious_C
     (xListEnd_C
       (h_val
         (heap_update raw_item_ptr
           (pvContainer_C_update (\<lambda>_. c) (h_val h raw_item_ptr)) h)
         raw_list_ptr)) =
   xMINI_LIST_ITEM_C.pxPrevious_C
     (xListEnd_C (h_val h raw_list_ptr))"
  by (simp only: raw_list_h_val_after_item_update_direct)

lemma raw_sentinel_next_survives_item_container_value_update:
  "xMINI_LIST_ITEM_C.pxNext_C
     (xListEnd_C
       (h_val
         (heap_update raw_item_ptr
           (pvContainer_C_update (\<lambda>_. c) v) h)
         raw_list_ptr)) =
   xMINI_LIST_ITEM_C.pxNext_C
     (xListEnd_C (h_val h raw_list_ptr))"
  by (simp only: raw_list_h_val_after_item_update_direct)

lemma raw_sentinel_previous_survives_item_container_value_update:
  "xMINI_LIST_ITEM_C.pxPrevious_C
     (xListEnd_C
       (h_val
         (heap_update raw_item_ptr
           (pvContainer_C_update (\<lambda>_. c) v) h)
         raw_list_ptr)) =
   xMINI_LIST_ITEM_C.pxPrevious_C
     (xListEnd_C (h_val h raw_list_ptr))"
  by (simp only: raw_list_h_val_after_item_update_direct)

lemma raw_sentinel_next_survives_whole_count_modify:
  "xMINI_LIST_ITEM_C.pxNext_C
     (xListEnd_C
       (h_val
         (heap_update raw_list_ptr
           (uxNumberOfItems_C_update f (h_val h raw_list_ptr)) h)
         raw_list_ptr)) =
   xMINI_LIST_ITEM_C.pxNext_C
     (xListEnd_C (h_val h raw_list_ptr))"
  by (simp add: h_val_heap_update)

lemma raw_sentinel_previous_survives_whole_count_modify:
  "xMINI_LIST_ITEM_C.pxPrevious_C
     (xListEnd_C
       (h_val
         (heap_update raw_list_ptr
           (uxNumberOfItems_C_update f (h_val h raw_list_ptr)) h)
         raw_list_ptr)) =
   xMINI_LIST_ITEM_C.pxPrevious_C
     (xListEnd_C (h_val h raw_list_ptr))"
  by (simp add: h_val_heap_update)

lemma raw_item_container_after_whole_container_update:
  "pvContainer_C
     (h_val
       (heap_update raw_item_ptr
         (pvContainer_C_update (\<lambda>_. c) (h_val h raw_item_ptr)) h)
       raw_item_ptr) = c"
  by (simp add: h_val_heap_update)

lemma raw_item_container_after_container_value_update:
  "pvContainer_C
     (h_val
       (heap_update raw_item_ptr
         (pvContainer_C_update (\<lambda>_. c) v) h)
       raw_item_ptr) = c"
  by (simp add: h_val_heap_update)

lemma raw_item_next_after_container_value_update:
  "xLIST_ITEM_C.pxNext_C
     (h_val
       (heap_update raw_item_ptr
         (pvContainer_C_update (\<lambda>_. c) v) h)
       raw_item_ptr) = xLIST_ITEM_C.pxNext_C v"
  by (simp add: h_val_heap_update)

lemma raw_item_previous_after_container_value_update:
  "xLIST_ITEM_C.pxPrevious_C
     (h_val
       (heap_update raw_item_ptr
         (pvContainer_C_update (\<lambda>_. c) v) h)
       raw_item_ptr) = xLIST_ITEM_C.pxPrevious_C v"
  by (simp add: h_val_heap_update)

end
