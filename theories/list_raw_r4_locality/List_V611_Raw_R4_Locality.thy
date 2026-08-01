theory List_V611_Raw_R4_Locality
  imports "EAL6_FreeRTOS_V611_List_Raw_R4_Prestate.List_V611_Raw_R4_Prestate"
begin

text \<open>
  R4b resolves the two singleton unlink targets and packages the local
  read-after-write facts needed by the generated source order.  No generated
  monad is opened in this theory.
\<close>

lemma raw_remove_successor_previous_field_at_singleton:
  assumes singleton: "raw_singleton_heap_fields h"
  shows
   "PTR(xLIST_ITEM_C ptr)
      &(xLIST_ITEM_C.pxNext_C (h_val h raw_item_ptr)
          \<rightarrow>[''pxPrevious_C'']) =
    (Ptr 0x1010 :: xLIST_ITEM_C ptr ptr)"
  using singleton
  unfolding raw_singleton_heap_fields_def
  by (simp add: field_lvalue_def xLIST_ITEM_C_pxPrevious_C_fl)

lemma raw_remove_predecessor_next_field_at_singleton:
  assumes singleton: "raw_singleton_heap_fields h"
  shows
   "PTR(xLIST_ITEM_C ptr)
      &(xLIST_ITEM_C.pxPrevious_C (h_val h raw_item_ptr)
          \<rightarrow>[''pxNext_C'']) =
    (Ptr 0x100C :: xLIST_ITEM_C ptr ptr)"
  using singleton
  unfolding raw_singleton_heap_fields_def
  by (simp add: field_lvalue_def xLIST_ITEM_C_pxNext_C_fl)

lemma raw_sentinel_next_field_update_to_list:
  "heap_update
      (PTR(xLIST_ITEM_C ptr)
        &(raw_sentinel_ptr raw_list_ptr\<rightarrow>[''pxNext_C''])) q h =
   heap_update raw_list_ptr
      (xListEnd_C_update
        (\<lambda>_. xMINI_LIST_ITEM_C.pxNext_C_update (\<lambda>_. q)
          (h_val h raw_sentinel_mini_ptr))
        (h_val h raw_list_ptr)) h"
proof -
  have
    "heap_update
       (PTR(xLIST_ITEM_C ptr)
         &(raw_sentinel_ptr raw_list_ptr\<rightarrow>[''pxNext_C''])) q h =
     heap_update (raw_sentinel_ptr raw_list_ptr)
       (xLIST_ITEM_C.pxNext_C_update (\<lambda>_. q)
         (h_val h (raw_sentinel_ptr raw_list_ptr))) h"
    by (rule sym, rule raw_sentinel_whole_next_update_to_field)
  also have "... = heap_update raw_list_ptr
      (xListEnd_C_update
        (\<lambda>_. xMINI_LIST_ITEM_C.pxNext_C_update (\<lambda>_. q)
          (h_val h raw_sentinel_mini_ptr))
        (h_val h raw_list_ptr)) h"
    by (rule raw_sentinel_whole_next_update_to_list)
  finally show ?thesis .
qed

lemma raw_item_h_val_survives_sentinel_next_field_update:
  "h_val
     (heap_update
       (PTR(xLIST_ITEM_C ptr)
         &(raw_sentinel_ptr raw_list_ptr\<rightarrow>[''pxNext_C''])) q h)
     raw_item_ptr = h_val h raw_item_ptr"
  apply (subst raw_sentinel_next_field_update_to_list)
  apply (rule raw_item_h_val_after_list_update_direct)
  done

lemma raw_item_h_val_survives_two_unlink_writes:
  "h_val
     (heap_update
       (PTR(xLIST_ITEM_C ptr)
         &(raw_sentinel_ptr raw_list_ptr\<rightarrow>[''pxNext_C''])) qn
       (heap_update
         (PTR(xLIST_ITEM_C ptr)
           &(raw_sentinel_ptr raw_list_ptr\<rightarrow>[''pxPrevious_C''])) qp h))
     raw_item_ptr = h_val h raw_item_ptr"
  by (simp only: raw_item_h_val_survives_sentinel_next_field_update
      raw_item_h_val_survives_sentinel_previous_field_update)

lemma raw_remove_predecessor_next_field_after_first_unlink:
  assumes singleton: "raw_singleton_heap_fields h"
  shows
   "PTR(xLIST_ITEM_C ptr)
      &(xLIST_ITEM_C.pxPrevious_C
          (h_val
            (heap_update
              (PTR(xLIST_ITEM_C ptr)
                &(raw_sentinel_ptr raw_list_ptr\<rightarrow>
                    [''pxPrevious_C'']))
              (raw_sentinel_ptr raw_list_ptr) h)
            raw_item_ptr)
          \<rightarrow>[''pxNext_C'']) =
    (Ptr 0x100C :: xLIST_ITEM_C ptr ptr)"
  apply (simp only: raw_item_h_val_survives_sentinel_previous_field_update)
  apply (rule raw_remove_predecessor_next_field_at_singleton[OF singleton])
  done

lemma raw_list_index_survives_sentinel_previous_field_update:
  "pxIndex_C
     (h_val
       (heap_update
         (PTR(xLIST_ITEM_C ptr)
           &(raw_sentinel_ptr raw_list_ptr\<rightarrow>[''pxPrevious_C''])) q h)
       raw_list_ptr) = pxIndex_C (h_val h raw_list_ptr)"
  apply (subst raw_sentinel_previous_field_update_to_list)
  apply simp
  done

lemma raw_list_index_survives_sentinel_next_field_update:
  "pxIndex_C
     (h_val
       (heap_update
         (PTR(xLIST_ITEM_C ptr)
           &(raw_sentinel_ptr raw_list_ptr\<rightarrow>[''pxNext_C''])) q h)
       raw_list_ptr) = pxIndex_C (h_val h raw_list_ptr)"
  apply (subst raw_sentinel_next_field_update_to_list)
  apply simp
  done

lemma raw_list_count_survives_sentinel_next_field_update:
  "uxNumberOfItems_C
     (h_val
       (heap_update
         (PTR(xLIST_ITEM_C ptr)
           &(raw_sentinel_ptr raw_list_ptr\<rightarrow>[''pxNext_C''])) q h)
       raw_list_ptr) = uxNumberOfItems_C (h_val h raw_list_ptr)"
  apply (subst raw_sentinel_next_field_update_to_list)
  apply simp
  done

lemma raw_remove_singleton_cursor_and_item_after_unlink:
  assumes singleton: "raw_singleton_heap_fields h"
  shows
    "pxIndex_C
       (h_val
         (heap_update
           (PTR(xLIST_ITEM_C ptr)
             &(raw_sentinel_ptr raw_list_ptr\<rightarrow>[''pxNext_C'']))
           (raw_sentinel_ptr raw_list_ptr)
           (heap_update
             (PTR(xLIST_ITEM_C ptr)
               &(raw_sentinel_ptr raw_list_ptr\<rightarrow>[''pxPrevious_C'']))
             (raw_sentinel_ptr raw_list_ptr) h))
         raw_list_ptr) = raw_item_ptr \<and>
     xLIST_ITEM_C.pxPrevious_C
       (h_val
         (heap_update
           (PTR(xLIST_ITEM_C ptr)
             &(raw_sentinel_ptr raw_list_ptr\<rightarrow>[''pxNext_C'']))
           (raw_sentinel_ptr raw_list_ptr)
           (heap_update
             (PTR(xLIST_ITEM_C ptr)
               &(raw_sentinel_ptr raw_list_ptr\<rightarrow>[''pxPrevious_C'']))
             (raw_sentinel_ptr raw_list_ptr) h))
         raw_item_ptr) = raw_sentinel_ptr raw_list_ptr"
  apply (simp only: raw_list_index_survives_sentinel_next_field_update
      raw_list_index_survives_sentinel_previous_field_update
      raw_item_h_val_survives_two_unlink_writes)
  using singleton
  unfolding raw_singleton_heap_fields_def
  by blast

lemma raw_remove_singleton_container_read_after_unlink:
  assumes singleton: "raw_singleton_heap_fields h"
  shows
    "PTR_COERCE(unit \<rightarrow> xLIST_C)
       (pvContainer_C
         (h_val
           (heap_update
             (PTR(xLIST_ITEM_C ptr)
               &(raw_sentinel_ptr raw_list_ptr\<rightarrow>[''pxNext_C'']))
             (raw_sentinel_ptr raw_list_ptr)
             (heap_update
               (PTR(xLIST_ITEM_C ptr)
                 &(raw_sentinel_ptr raw_list_ptr\<rightarrow>[''pxPrevious_C'']))
               (raw_sentinel_ptr raw_list_ptr) h))
           raw_item_ptr)) = raw_list_ptr"
  apply (simp only: raw_item_h_val_survives_two_unlink_writes)
  using singleton
  unfolding raw_singleton_heap_fields_def
  by simp

lemmas raw_list_index_update_to_field =
  raw_list_whole_index_update_to_field

lemmas raw_item_container_update_to_field =
  raw_item_whole_container_update_to_field

lemmas raw_list_count_update_to_field =
  raw_list_whole_count_update_to_field

lemma raw_remove_count_one_to_zero:
  "((1 :: 32 word) - 1) = 0"
  by simp

lemma raw_singleton_prestate_heap_fields_direct:
  "raw_singleton_heap_fields
     (hrs_mem
       (t_hrs_' (raw_singleton_prestate base d h k owner)))"
  apply (simp only: raw_singleton_prestate_heap)
  apply (rule raw_singleton_prestate_heap_fields)
  done

lemma raw_singleton_prestate_item_next:
  "xLIST_ITEM_C.pxNext_C
     (h_val
       (hrs_mem
         (t_hrs_' (raw_singleton_prestate base d h k owner)))
       raw_item_ptr) = raw_sentinel_ptr raw_list_ptr"
  using raw_singleton_prestate_heap_fields_direct[
    where base=base and d=d and h=h and k=k and owner=owner]
  unfolding raw_singleton_heap_fields_def
  by simp

lemma raw_singleton_prestate_item_previous:
  "xLIST_ITEM_C.pxPrevious_C
     (h_val
       (hrs_mem
         (t_hrs_' (raw_singleton_prestate base d h k owner)))
       raw_item_ptr) = raw_sentinel_ptr raw_list_ptr"
  using raw_singleton_prestate_heap_fields_direct[
    where base=base and d=d and h=h and k=k and owner=owner]
  unfolding raw_singleton_heap_fields_def
  by simp

lemma raw_singleton_prestate_item_container:
  "pvContainer_C
     (h_val
       (hrs_mem
         (t_hrs_' (raw_singleton_prestate base d h k owner)))
       raw_item_ptr) =
   PTR_COERCE(xLIST_C \<rightarrow> unit) raw_list_ptr"
  using raw_singleton_prestate_heap_fields_direct[
    where base=base and d=d and h=h and k=k and owner=owner]
  unfolding raw_singleton_heap_fields_def
  by simp

lemma raw_singleton_container_cast_back:
  "PTR_COERCE(unit \<rightarrow> xLIST_C)
     (PTR_COERCE(xLIST_C \<rightarrow> unit) raw_list_ptr) = raw_list_ptr"
  by simp

lemma raw_singleton_prestate_list_guard:
  "c_guard
     (PTR_COERCE(unit \<rightarrow> xLIST_C)
       (pvContainer_C
         (h_val
           (hrs_mem
             (t_hrs_' (raw_singleton_prestate base d h k owner)))
           raw_item_ptr)))"
  apply (subst raw_singleton_prestate_item_container)
  apply (simp only: raw_singleton_container_cast_back)
  apply (rule raw_list_ptr_guard)
  done

lemma raw_singleton_prestate_index:
  "pxIndex_C
     (h_val
       (hrs_mem
         (t_hrs_' (raw_singleton_prestate base d h k owner)))
       raw_list_ptr) = raw_item_ptr"
  using raw_singleton_prestate_heap_fields_direct[
    where base=base and d=d and h=h and k=k and owner=owner]
  unfolding raw_singleton_heap_fields_def
  by simp

lemma raw_singleton_prestate_count:
  "uxNumberOfItems_C
     (h_val
       (hrs_mem
         (t_hrs_' (raw_singleton_prestate base d h k owner)))
       raw_list_ptr) = 1"
  using raw_singleton_prestate_heap_fields_direct[
    where base=base and d=d and h=h and k=k and owner=owner]
  unfolding raw_singleton_heap_fields_def
  by simp

lemma raw_singleton_prestate_item_next_guard:
  "c_guard
     (xLIST_ITEM_C.pxNext_C
       (h_val
         (hrs_mem
           (t_hrs_' (raw_singleton_prestate base d h k owner)))
         raw_item_ptr))"
  apply (subst raw_singleton_prestate_item_next)
  apply (rule raw_sentinel_ptr_guard)
  done

lemma raw_singleton_prestate_successor_previous_field:
  "PTR(xLIST_ITEM_C ptr)
      &(xLIST_ITEM_C.pxNext_C
          (h_val
            (hrs_mem
              (t_hrs_' (raw_singleton_prestate base d h k owner)))
            raw_item_ptr)
          \<rightarrow>[''pxPrevious_C'']) =
    (Ptr 0x1010 :: xLIST_ITEM_C ptr ptr)"
  apply (rule raw_remove_successor_previous_field_at_singleton)
  apply (rule raw_singleton_prestate_heap_fields_direct)
  done

lemma raw_singleton_prestate_item_previous_guard_after_first_unlink:
  "c_guard
     (xLIST_ITEM_C.pxPrevious_C
       (h_val
         (heap_update
           (PTR(xLIST_ITEM_C ptr)
             &(raw_sentinel_ptr raw_list_ptr\<rightarrow>[''pxPrevious_C'']))
           (raw_sentinel_ptr raw_list_ptr)
           (hrs_mem
             (t_hrs_' (raw_singleton_prestate base d h k owner))))
         raw_item_ptr))"
  apply (simp only: raw_item_h_val_survives_sentinel_previous_field_update)
  apply (subst raw_singleton_prestate_item_previous)
  apply (rule raw_sentinel_ptr_guard)
  done

lemma raw_singleton_prestate_predecessor_next_field_after_first_unlink:
  "PTR(xLIST_ITEM_C ptr)
      &(xLIST_ITEM_C.pxPrevious_C
          (h_val
            (heap_update
              (PTR(xLIST_ITEM_C ptr)
                &(raw_sentinel_ptr raw_list_ptr\<rightarrow>
                    [''pxPrevious_C'']))
              (raw_sentinel_ptr raw_list_ptr)
              (hrs_mem
                (t_hrs_' (raw_singleton_prestate base d h k owner))))
            raw_item_ptr)
          \<rightarrow>[''pxNext_C'']) =
    (Ptr 0x100C :: xLIST_ITEM_C ptr ptr)"
  apply (rule raw_remove_predecessor_next_field_after_first_unlink)
  apply (rule raw_singleton_prestate_heap_fields_direct)
  done

lemma raw_singleton_prestate_list_guard_after_unlink:
  "c_guard
     (PTR_COERCE(unit \<rightarrow> xLIST_C)
       (pvContainer_C
         (h_val
           (heap_update
             (PTR(xLIST_ITEM_C ptr)
               &(raw_sentinel_ptr raw_list_ptr\<rightarrow>[''pxNext_C'']))
             (raw_sentinel_ptr raw_list_ptr)
             (heap_update
               (PTR(xLIST_ITEM_C ptr)
                 &(raw_sentinel_ptr raw_list_ptr\<rightarrow>[''pxPrevious_C'']))
               (raw_sentinel_ptr raw_list_ptr)
               (hrs_mem
                 (t_hrs_' (raw_singleton_prestate base d h k owner)))))
           raw_item_ptr)))"
  apply (subst raw_remove_singleton_container_read_after_unlink)
  apply (rule raw_singleton_prestate_heap_fields_direct)
  apply (rule raw_list_ptr_guard)
  done

end
