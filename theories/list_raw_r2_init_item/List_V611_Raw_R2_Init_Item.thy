theory List_V611_Raw_R2_Init_Item
  imports "EAL6_FreeRTOS_V611_List_Raw_R1_Init.List_V611_Raw_R1_Init"
begin

text \<open>
  R2 symbolically executes only vListInitialiseItem'.  Besides the changed
  container field, the theorem records exact frames for all four other item
  fields, the separate list object, and the byte canary.
\<close>

lemma raw_3000_outside_item_interval:
  "(0x3000 :: addr) \<notin> {0x2000..+20}"
proof -
  have no_wrap: "unat (0x2000 :: addr) + 20 \<le> addr_card"
    by (simp add: addr_card_def card_word)
  have membership:
    "((0x3000 :: addr) \<in> {0x2000..+20}) =
      (unat (0x2000 :: addr) \<le> unat (0x3000 :: addr) \<and>
       unat (0x3000 :: addr) < unat (0x2000 :: addr) + 20)"
    by (rule intvl_no_overflow_nat[OF no_wrap])
  from membership show ?thesis by simp
qed

lemma raw_list_item_intervals_disjoint:
  "{(0x2000 :: addr)..+20} \<inter> {(0x1000 :: addr)..+20} = {}"
proof -
  have item_no_wrap: "unat (0x2000 :: addr) + 20 \<le> addr_card"
    by (simp add: addr_card_def card_word)
  have list_no_wrap: "unat (0x1000 :: addr) + 20 \<le> addr_card"
    by (simp add: addr_card_def card_word)
  have item_range:
    "{(0x2000 :: addr)..+20} =
      {x. unat (0x2000 :: addr) \<le> unat x \<and>
          unat x < unat (0x2000 :: addr) + 20}"
    by (rule intvl_no_overflow_nat_conv[OF item_no_wrap])
  have list_range:
    "{(0x1000 :: addr)..+20} =
      {x. unat (0x1000 :: addr) \<le> unat x \<and>
          unat x < unat (0x1000 :: addr) + 20}"
    by (rule intvl_no_overflow_nat_conv[OF list_no_wrap])
  show ?thesis
  proof (rule equals0I)
    fix x
    assume xmem:
      "x \<in> {(0x2000 :: addr)..+20} \<inter> {(0x1000 :: addr)..+20}"
    have lower: "8192 \<le> unat x"
      using xmem by (simp add: item_range)
    have upper: "unat x < 4116"
      using xmem by (simp add: list_range)
    have "(8192 :: nat) < 4116"
      by (rule le_less_trans[OF lower upper])
    then show False by simp
  qed
qed

lemma raw_item_heap_update_canary[simp]:
  "heap_update raw_item_ptr (v :: xLIST_ITEM_C) h raw_canary_addr =
   h raw_canary_addr"
  unfolding heap_update_def raw_item_ptr_def raw_canary_addr_def
  apply (rule heap_update_nmem_same)
  apply (simp add: raw_3000_outside_item_interval)
  done

lemma raw_item_h_val_after_self_update[simp]:
  "h_val
     (hrs_mem
       (hrs_mem_update (heap_update raw_item_ptr (v :: xLIST_ITEM_C)) h))
     raw_item_ptr = v"
  by (simp add: hrs_mem_update h_val_heap_update)

lemma raw_list_h_val_after_item_update[simp]:
  "h_val
     (hrs_mem
       (hrs_mem_update (heap_update raw_item_ptr (v :: xLIST_ITEM_C)) h))
     raw_list_ptr = h_val (hrs_mem h) raw_list_ptr"
proof -
  have disjoint:
    "{ptr_val raw_item_ptr..+
       length (to_bytes v
         (heap_list (hrs_mem h) (size_of TYPE(xLIST_ITEM_C))
           (ptr_val raw_item_ptr)))} \<inter>
     {ptr_val raw_list_ptr..+size_of TYPE(xLIST_C)} = {}"
    by (simp add: raw_item_ptr_def raw_list_ptr_def size_of_def
        raw_list_item_intervals_disjoint)
  have heap_lists_same:
    "heap_list
       (heap_update_list (ptr_val raw_item_ptr)
         (to_bytes v
           (heap_list (hrs_mem h) (size_of TYPE(xLIST_ITEM_C))
             (ptr_val raw_item_ptr)))
         (hrs_mem h))
       (size_of TYPE(xLIST_C)) (ptr_val raw_list_ptr) =
     heap_list (hrs_mem h) (size_of TYPE(xLIST_C))
       (ptr_val raw_list_ptr)"
    by (rule heap_list_update_disjoint_same[OF disjoint])
  show ?thesis
    unfolding hrs_mem_update h_val_def heap_update_def
    using heap_lists_same by simp
qed

lemma raw_vListInitialiseItem_exact_post_and_frames:
  "vListInitialiseItem' raw_item_ptr \<bullet> s
   \<lbrace>\<lambda>r t.
      r = Result () \<and>
      pvContainer_C
        (h_val (hrs_mem (t_hrs_' t)) raw_item_ptr) = NULL \<and>
      xLIST_ITEM_C.xItemValue_C
        (h_val (hrs_mem (t_hrs_' t)) raw_item_ptr) =
        xLIST_ITEM_C.xItemValue_C
          (h_val (hrs_mem (t_hrs_' s)) raw_item_ptr) \<and>
      xLIST_ITEM_C.pxNext_C
        (h_val (hrs_mem (t_hrs_' t)) raw_item_ptr) =
        xLIST_ITEM_C.pxNext_C
          (h_val (hrs_mem (t_hrs_' s)) raw_item_ptr) \<and>
      xLIST_ITEM_C.pxPrevious_C
        (h_val (hrs_mem (t_hrs_' t)) raw_item_ptr) =
        xLIST_ITEM_C.pxPrevious_C
          (h_val (hrs_mem (t_hrs_' s)) raw_item_ptr) \<and>
      pvOwner_C
        (h_val (hrs_mem (t_hrs_' t)) raw_item_ptr) =
        pvOwner_C (h_val (hrs_mem (t_hrs_' s)) raw_item_ptr) \<and>
      h_val (hrs_mem (t_hrs_' t)) raw_list_ptr =
        h_val (hrs_mem (t_hrs_' s)) raw_list_ptr \<and>
      hrs_mem (t_hrs_' t) raw_canary_addr =
        hrs_mem (t_hrs_' s) raw_canary_addr
    \<rbrace>"
  unfolding vListInitialiseItem'_def
  apply runs_to_vcg
  apply (simp add: hrs_mem_update)
  done

end
