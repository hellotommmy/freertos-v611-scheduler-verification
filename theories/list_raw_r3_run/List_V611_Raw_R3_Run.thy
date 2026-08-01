theory List_V611_Raw_R3_Run
  imports "EAL6_FreeRTOS_V611_List_Raw_R3_Prestate.List_V611_Raw_R3_Prestate"
begin

text \<open>
  R3d starts with the weakest positive execution gate: the concrete empty
  witness reaches Result ().  No post-state field, frame, or abstract
  refinement claim is included in this first VCG.
\<close>

lemma raw_item_sentinel_intervals_disjoint:
  "{(0x2000 :: addr)..+20} \<inter> {(0x1008 :: addr)..+20} = {}"
proof -
  have item_no_wrap: "unat (0x2000 :: addr) + 20 \<le> addr_card"
    by (simp add: addr_card_def card_word)
  have sentinel_no_wrap: "unat (0x1008 :: addr) + 20 \<le> addr_card"
    by (simp add: addr_card_def card_word)
  have item_range:
    "{(0x2000 :: addr)..+20} =
      {x. unat (0x2000 :: addr) \<le> unat x \<and>
          unat x < unat (0x2000 :: addr) + 20}"
    by (rule intvl_no_overflow_nat_conv[OF item_no_wrap])
  have sentinel_range:
    "{(0x1008 :: addr)..+20} =
      {x. unat (0x1008 :: addr) \<le> unat x \<and>
          unat x < unat (0x1008 :: addr) + 20}"
    by (rule intvl_no_overflow_nat_conv[OF sentinel_no_wrap])
  show ?thesis
  proof (rule equals0I)
    fix x
    assume xmem:
      "x \<in> {(0x2000 :: addr)..+20} \<inter> {(0x1008 :: addr)..+20}"
    have lower: "8192 \<le> unat x"
      using xmem by (simp add: item_range)
    have upper: "unat x < 4124"
      using xmem by (simp add: sentinel_range)
    have "(8192 :: nat) < 4124"
      by (rule le_less_trans[OF lower upper])
    then show False by simp
  qed
qed

lemma raw_sentinel_h_val_after_item_update_direct[simp]:
  "h_val (heap_update raw_item_ptr (v :: xLIST_ITEM_C) h)
     (raw_sentinel_ptr raw_list_ptr) =
   h_val h (raw_sentinel_ptr raw_list_ptr)"
proof -
  have disjoint:
    "{ptr_val raw_item_ptr..+
       length (to_bytes v
         (heap_list h (size_of TYPE(xLIST_ITEM_C))
           (ptr_val raw_item_ptr)))} \<inter>
     {ptr_val (raw_sentinel_ptr raw_list_ptr)..+
       size_of TYPE(xLIST_ITEM_C)} = {}"
    by (simp add: raw_item_ptr_def raw_sentinel_ptr_at_witness
        size_of_def raw_item_sentinel_intervals_disjoint)
  have heap_lists_same:
    "heap_list
       (heap_update_list (ptr_val raw_item_ptr)
         (to_bytes v
           (heap_list h (size_of TYPE(xLIST_ITEM_C))
             (ptr_val raw_item_ptr))) h)
       (size_of TYPE(xLIST_ITEM_C))
       (ptr_val (raw_sentinel_ptr raw_list_ptr)) =
     heap_list h (size_of TYPE(xLIST_ITEM_C))
       (ptr_val (raw_sentinel_ptr raw_list_ptr))"
    by (rule heap_list_update_disjoint_same[OF disjoint])
  show ?thesis
    unfolding h_val_def heap_update_def
    using heap_lists_same by simp
qed

lemma raw_sentinel_guard_at_witness:
  "c_guard (Ptr 0x1008 :: xLIST_ITEM_C ptr)"
  using raw_sentinel_ptr_guard
  by (simp only: raw_sentinel_ptr_at_witness)

lemma raw_insert_end_prestate_index:
  "pxIndex_C
     (h_val
       (hrs_mem
         (t_hrs_' (raw_insert_end_prestate base d h k owner)))
       raw_list_ptr) = raw_sentinel_ptr raw_list_ptr"
  unfolding raw_insert_end_prestate_def raw_insert_end_preheap_def
    raw_empty_list_value_def raw_fresh_item_value_def
  by (simp add: hrs_mem_def h_val_heap_update)

lemma raw_insert_end_prestate_sentinel_next_raw:
  "xLIST_ITEM_C.pxNext_C
     (h_val
       (hrs_mem
         (t_hrs_' (raw_insert_end_prestate base d h k owner)))
       (raw_sentinel_ptr raw_list_ptr)) =
   raw_sentinel_ptr raw_list_ptr"
  apply (subst raw_sentinel_next_prefix)
  unfolding raw_insert_end_prestate_def raw_insert_end_preheap_def
    raw_empty_list_value_def raw_fresh_item_value_def
  apply (simp add: hrs_mem_def h_val_heap_update)
  done

lemma raw_insert_end_prestate_index_guard:
  "c_guard
    (pxIndex_C
      (h_val
        (hrs_mem
          (t_hrs_' (raw_insert_end_prestate base d h k owner)))
        raw_list_ptr))"
  apply (simp only: raw_insert_end_prestate_index)
  apply (rule raw_sentinel_ptr_guard)
  done

lemma raw_prestate_index_next_guard_after_item_updates:
  "c_guard
    (xLIST_ITEM_C.pxNext_C
      (h_val
        (heap_update raw_item_ptr (v2 :: xLIST_ITEM_C)
          (heap_update raw_item_ptr (v1 :: xLIST_ITEM_C)
            (hrs_mem
              (t_hrs_' (raw_insert_end_prestate base d h k owner)))))
        (pxIndex_C
          (h_val
            (hrs_mem
              (t_hrs_' (raw_insert_end_prestate base d h k owner)))
            raw_list_ptr))))"
  apply (simp only: raw_insert_end_prestate_index)
  apply (simp only: raw_sentinel_h_val_after_item_update_direct)
  apply (simp only: raw_insert_end_prestate_sentinel_next_raw)
  apply (rule raw_sentinel_ptr_guard)
  done

lemma raw_vListInsertEnd_empty_result:
  "vListInsertEnd' raw_list_ptr raw_item_ptr \<bullet>
     (raw_insert_end_prestate base d h k owner)
   \<lbrace>\<lambda>r t. r = Result ()\<rbrace>"
  unfolding vListInsertEnd'_def
  apply runs_to_vcg
  apply (rule raw_insert_end_prestate_index_guard)
  apply (simp only: hrs_mem_update)
  apply (rule raw_prestate_index_next_guard_after_item_updates)
  done

end
