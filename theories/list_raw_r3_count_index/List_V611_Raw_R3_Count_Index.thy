theory List_V611_Raw_R3_Count_Index
  imports "EAL6_FreeRTOS_V611_List_Raw_R3_Run.List_V611_Raw_R3_Run"
begin

text \<open>
  R3e first normalises the two list-root writes needed by the minimal
  count/cursor postcondition.  The VCG remains separate from these byte-level
  conversion and frame bricks.
\<close>

lemma raw_list_whole_index_update_to_field:
  "heap_update raw_list_ptr
      (pxIndex_C_update (\<lambda>_. q) (h_val h raw_list_ptr)) h =
   heap_update
      (PTR(xLIST_ITEM_C ptr)
        &(raw_list_ptr\<rightarrow>[''pxIndex_C''])) q h"
  apply (rule sym)
  apply (rule xLIST_C_heap_update_fields(2))
  apply (rule raw_list_ptr_guard)
  done

lemma raw_list_whole_count_update_to_field:
  "heap_update raw_list_ptr
      (uxNumberOfItems_C_update (\<lambda>_. n)
        (h_val h raw_list_ptr)) h =
   heap_update
      (PTR(32 word)
        &(raw_list_ptr\<rightarrow>[''uxNumberOfItems_C''])) n h"
  apply (rule sym)
  apply (rule xLIST_C_heap_update_fields(1))
  apply (rule raw_list_ptr_guard)
  done

lemma raw_list_h_val_survives_item_container_update:
  "h_val
     (heap_update raw_item_ptr
       (pvContainer_C_update (\<lambda>_. c)
         (h_val h raw_item_ptr)) h)
     raw_list_ptr = h_val h raw_list_ptr"
  by (rule raw_list_h_val_after_item_update_direct)

lemma raw_sentinel_previous_field_update_to_list:
  "heap_update
      (PTR(xLIST_ITEM_C ptr)
        &(raw_sentinel_ptr raw_list_ptr\<rightarrow>[''pxPrevious_C''])) q h =
   heap_update raw_list_ptr
      (xListEnd_C_update
        (\<lambda>_. xMINI_LIST_ITEM_C.pxPrevious_C_update (\<lambda>_. q)
          (h_val h raw_sentinel_mini_ptr))
        (h_val h raw_list_ptr)) h"
proof -
  have
    "heap_update
       (PTR(xLIST_ITEM_C ptr)
         &(raw_sentinel_ptr raw_list_ptr\<rightarrow>[''pxPrevious_C''])) q h =
     heap_update (raw_sentinel_ptr raw_list_ptr)
       (xLIST_ITEM_C.pxPrevious_C_update (\<lambda>_. q)
         (h_val h (raw_sentinel_ptr raw_list_ptr))) h"
    by (rule sym, rule raw_sentinel_whole_previous_update_to_field)
  also have "... = heap_update raw_list_ptr
      (xListEnd_C_update
        (\<lambda>_. xMINI_LIST_ITEM_C.pxPrevious_C_update (\<lambda>_. q)
          (h_val h raw_sentinel_mini_ptr))
        (h_val h raw_list_ptr)) h"
    by (rule raw_sentinel_whole_previous_update_to_list)
  finally show ?thesis .
qed

lemma raw_list_count_survives_sentinel_previous_field_update:
  "uxNumberOfItems_C
     (h_val
       (heap_update
         (PTR(xLIST_ITEM_C ptr)
           &(raw_sentinel_ptr raw_list_ptr\<rightarrow>[''pxPrevious_C''])) q h)
       raw_list_ptr) =
   uxNumberOfItems_C (h_val h raw_list_ptr)"
  apply (subst raw_sentinel_previous_field_update_to_list)
  apply simp
  done

lemma raw_list_count_survives_sentinel_next_update:
  "uxNumberOfItems_C
     (h_val
       (heap_update (raw_sentinel_ptr raw_list_ptr)
         (xLIST_ITEM_C.pxNext_C_update (\<lambda>_. q)
           (h_val h (raw_sentinel_ptr raw_list_ptr))) h)
       raw_list_ptr) =
   uxNumberOfItems_C (h_val h raw_list_ptr)"
  apply (subst raw_sentinel_whole_next_update_to_list)
  apply simp
  done

lemma raw_insert_end_prestate_count:
  "uxNumberOfItems_C
     (h_val
       (hrs_mem
         (t_hrs_' (raw_insert_end_prestate base d h k owner)))
       raw_list_ptr) = 0"
  unfolding raw_insert_end_prestate_def raw_insert_end_preheap_def
    raw_empty_list_value_def raw_fresh_item_value_def
  apply (simp add: hrs_mem_def h_val_heap_update)
  done

end
