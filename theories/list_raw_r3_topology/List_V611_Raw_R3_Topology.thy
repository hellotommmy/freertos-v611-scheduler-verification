theory List_V611_Raw_R3_Topology
  imports "EAL6_FreeRTOS_V611_List_Raw_R3_Count_Index_Post.List_V611_Raw_R3_Count_Index_Post"
begin

text \<open>
  R3f prepares only the detached-item and container locality facts needed for
  the singleton ring topology.  Key/owner and byte-canary frames remain out
  of scope.
\<close>

lemma raw_list_item_intervals_disjoint_symmetric:
  "{(0x1000 :: addr)..+20} \<inter> {(0x2000 :: addr)..+20} = {}"
  using raw_list_item_intervals_disjoint
  by (metis Int_commute)

lemma raw_sentinel_item_intervals_disjoint_symmetric:
  "{(0x1008 :: addr)..+20} \<inter> {(0x2000 :: addr)..+20} = {}"
  using raw_item_sentinel_intervals_disjoint
  by (metis Int_commute)

lemma raw_item_h_val_after_list_update_direct[simp]:
  "h_val (heap_update raw_list_ptr (v :: xLIST_C) h) raw_item_ptr =
   h_val h raw_item_ptr"
proof -
  have disjoint:
    "{ptr_val raw_list_ptr..+
       length (to_bytes v
         (heap_list h (size_of TYPE(xLIST_C))
           (ptr_val raw_list_ptr)))} \<inter>
     {ptr_val raw_item_ptr..+size_of TYPE(xLIST_ITEM_C)} = {}"
    by (simp add: raw_list_ptr_def raw_item_ptr_def size_of_def
        raw_list_item_intervals_disjoint_symmetric)
  have heap_lists_same:
    "heap_list
       (heap_update_list (ptr_val raw_list_ptr)
         (to_bytes v
           (heap_list h (size_of TYPE(xLIST_C))
             (ptr_val raw_list_ptr))) h)
       (size_of TYPE(xLIST_ITEM_C)) (ptr_val raw_item_ptr) =
     heap_list h (size_of TYPE(xLIST_ITEM_C)) (ptr_val raw_item_ptr)"
    by (rule heap_list_update_disjoint_same[OF disjoint])
  show ?thesis
    unfolding h_val_def heap_update_def
    using heap_lists_same by simp
qed

lemma raw_item_h_val_after_sentinel_update_direct[simp]:
  "h_val
     (heap_update (raw_sentinel_ptr raw_list_ptr)
       (v :: xLIST_ITEM_C) h)
     raw_item_ptr = h_val h raw_item_ptr"
proof -
  have disjoint:
    "{ptr_val (raw_sentinel_ptr raw_list_ptr)..+
       length (to_bytes v
         (heap_list h (size_of TYPE(xLIST_ITEM_C))
           (ptr_val (raw_sentinel_ptr raw_list_ptr))))} \<inter>
     {ptr_val raw_item_ptr..+size_of TYPE(xLIST_ITEM_C)} = {}"
    by (simp add: raw_sentinel_ptr_at_witness raw_item_ptr_def size_of_def
        raw_sentinel_item_intervals_disjoint_symmetric)
  have heap_lists_same:
    "heap_list
       (heap_update_list (ptr_val (raw_sentinel_ptr raw_list_ptr))
         (to_bytes v
           (heap_list h (size_of TYPE(xLIST_ITEM_C))
             (ptr_val (raw_sentinel_ptr raw_list_ptr)))) h)
       (size_of TYPE(xLIST_ITEM_C)) (ptr_val raw_item_ptr) =
     heap_list h (size_of TYPE(xLIST_ITEM_C)) (ptr_val raw_item_ptr)"
    by (rule heap_list_update_disjoint_same[OF disjoint])
  show ?thesis
    unfolding h_val_def heap_update_def
    using heap_lists_same by simp
qed

lemma raw_item_h_val_survives_sentinel_previous_field_update:
  "h_val
     (heap_update
       (PTR(xLIST_ITEM_C ptr)
         &(raw_sentinel_ptr raw_list_ptr\<rightarrow>[''pxPrevious_C''])) q h)
     raw_item_ptr = h_val h raw_item_ptr"
  apply (subst raw_sentinel_previous_field_update_to_list)
  apply (rule raw_item_h_val_after_list_update_direct)
  done

lemma raw_item_whole_container_update_to_field:
  "heap_update raw_item_ptr
      (pvContainer_C_update (\<lambda>_. c)
        (h_val h raw_item_ptr)) h =
   heap_update
      (PTR(unit ptr)
        &(raw_item_ptr\<rightarrow>[''pvContainer_C''])) c h"
  apply (rule sym)
  apply (rule xLIST_ITEM_C_heap_update_fields(5))
  apply (rule raw_item_ptr_guard)
  done

lemma raw_sentinel_previous_after_previous_field_update:
  "xMINI_LIST_ITEM_C.pxPrevious_C
     (xListEnd_C
       (h_val
         (heap_update
           (PTR(xLIST_ITEM_C ptr)
             &(raw_sentinel_ptr raw_list_ptr\<rightarrow>[''pxPrevious_C'']))
           q h)
         raw_list_ptr)) = q"
  apply (subst raw_sentinel_previous_field_update_to_list)
  apply simp
  done

lemma raw_sentinel_next_after_whole_next_update:
  "xMINI_LIST_ITEM_C.pxNext_C
     (xListEnd_C
       (h_val
         (heap_update (raw_sentinel_ptr raw_list_ptr)
           (xLIST_ITEM_C.pxNext_C_update (\<lambda>_. q)
             (h_val h (raw_sentinel_ptr raw_list_ptr))) h)
         raw_list_ptr)) = q"
  apply (subst raw_sentinel_whole_next_update_to_list)
  apply simp
  done

lemma raw_sentinel_previous_after_previous_then_next:
  "xMINI_LIST_ITEM_C.pxPrevious_C
     (xListEnd_C
       (h_val
         (heap_update (raw_sentinel_ptr raw_list_ptr)
           (xLIST_ITEM_C.pxNext_C_update (\<lambda>_. qn)
             (h_val
               (heap_update
                 (PTR(xLIST_ITEM_C ptr)
                   &(raw_sentinel_ptr raw_list_ptr\<rightarrow>[''pxPrevious_C'']))
                 qp h)
               (raw_sentinel_ptr raw_list_ptr)))
           (heap_update
             (PTR(xLIST_ITEM_C ptr)
               &(raw_sentinel_ptr raw_list_ptr\<rightarrow>[''pxPrevious_C'']))
             qp h))
         raw_list_ptr)) = qp"
  apply (subst raw_sentinel_previous_survives_next_update)
  apply (rule raw_sentinel_previous_after_previous_field_update)
  done

end
