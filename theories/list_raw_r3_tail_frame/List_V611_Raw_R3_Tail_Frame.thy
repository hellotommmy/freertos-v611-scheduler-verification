theory List_V611_Raw_R3_Tail_Frame
  imports "EAL6_FreeRTOS_V611_List_Raw_R3_Frames.List_V611_Raw_R3_Frames"
begin

text \<open>
  R3g tail locality: the list and detached item root writes are proved
  pointwise outside the symbolic eight-byte tail.  The two sentinel whole
  writes reuse the R3b theorems.
\<close>

lemma raw_list_tail_intervals_disjoint:
  "{(0x1000 :: addr)..+20} \<inter> {raw_sentinel_tail_addr..+8} = {}"
proof -
  have list_no_wrap: "unat (0x1000 :: addr) + 20 \<le> addr_card"
    by (simp add: addr_card_def card_word)
  have tail_no_wrap: "unat (0x1014 :: addr) + 8 \<le> addr_card"
    by (simp add: addr_card_def card_word)
  have list_range:
    "{(0x1000 :: addr)..+20} =
      {x. unat (0x1000 :: addr) \<le> unat x \<and>
          unat x < unat (0x1000 :: addr) + 20}"
    by (rule intvl_no_overflow_nat_conv[OF list_no_wrap])
  have tail_range:
    "{raw_sentinel_tail_addr..+8} =
      {x. unat (0x1014 :: addr) \<le> unat x \<and>
          unat x < unat (0x1014 :: addr) + 8}"
    unfolding raw_sentinel_tail_addr_def
    by (rule intvl_no_overflow_nat_conv[OF tail_no_wrap])
  show ?thesis
  proof (rule equals0I)
    fix x
    assume xmem:
      "x \<in> {(0x1000 :: addr)..+20} \<inter>
        {raw_sentinel_tail_addr..+8}"
    have upper: "unat x < 4116"
      using xmem by (simp add: list_range)
    have lower: "4116 \<le> unat x"
      using xmem by (simp add: tail_range)
    then show False using upper by simp
  qed
qed

lemma raw_item_tail_intervals_disjoint:
  "{(0x2000 :: addr)..+20} \<inter> {raw_sentinel_tail_addr..+8} = {}"
proof -
  have item_no_wrap: "unat (0x2000 :: addr) + 20 \<le> addr_card"
    by (simp add: addr_card_def card_word)
  have tail_no_wrap: "unat (0x1014 :: addr) + 8 \<le> addr_card"
    by (simp add: addr_card_def card_word)
  have item_range:
    "{(0x2000 :: addr)..+20} =
      {x. unat (0x2000 :: addr) \<le> unat x \<and>
          unat x < unat (0x2000 :: addr) + 20}"
    by (rule intvl_no_overflow_nat_conv[OF item_no_wrap])
  have tail_range:
    "{raw_sentinel_tail_addr..+8} =
      {x. unat (0x1014 :: addr) \<le> unat x \<and>
          unat x < unat (0x1014 :: addr) + 8}"
    unfolding raw_sentinel_tail_addr_def
    by (rule intvl_no_overflow_nat_conv[OF tail_no_wrap])
  show ?thesis
  proof (rule equals0I)
    fix x
    assume xmem:
      "x \<in> {(0x2000 :: addr)..+20} \<inter>
        {raw_sentinel_tail_addr..+8}"
    have lower: "8192 \<le> unat x"
      using xmem by (simp add: item_range)
    have upper: "unat x < 4124"
      using xmem by (simp add: tail_range)
    have "(8192 :: nat) < 4124"
      by (rule le_less_trans[OF lower upper])
    then show False by simp
  qed
qed

lemma raw_list_update_tail8_pointwise:
  assumes tail: "a \<in> {raw_sentinel_tail_addr..+8}"
  shows "heap_update raw_list_ptr (v :: xLIST_C) h a = h a"
proof -
  have outside: "a \<notin> {(0x1000 :: addr)..+20}"
    using raw_list_tail_intervals_disjoint tail by blast
  show ?thesis
    unfolding heap_update_def raw_list_ptr_def
    apply (rule heap_update_nmem_same)
    using outside
    apply simp
    done
qed

corollary raw_list_update_tail8:
  "\<forall>a \<in> {raw_sentinel_tail_addr..+8}.
     heap_update raw_list_ptr (v :: xLIST_C) h a = h a"
  by (intro ballI; rule raw_list_update_tail8_pointwise)

lemma raw_item_update_tail8_pointwise:
  assumes tail: "a \<in> {raw_sentinel_tail_addr..+8}"
  shows "heap_update raw_item_ptr (v :: xLIST_ITEM_C) h a = h a"
proof -
  have outside: "a \<notin> {(0x2000 :: addr)..+20}"
    using raw_item_tail_intervals_disjoint tail by blast
  show ?thesis
    unfolding heap_update_def raw_item_ptr_def
    apply (rule heap_update_nmem_same)
    using outside
    apply simp
    done
qed

corollary raw_item_update_tail8:
  "\<forall>a \<in> {raw_sentinel_tail_addr..+8}.
     heap_update raw_item_ptr (v :: xLIST_ITEM_C) h a = h a"
  by (intro ballI; rule raw_item_update_tail8_pointwise)

lemma raw_sentinel_previous_field_update_tail8_pointwise:
  assumes tail: "a \<in> {raw_sentinel_tail_addr..+8}"
  shows
    "heap_update
       (PTR(xLIST_ITEM_C ptr)
         &(raw_sentinel_ptr raw_list_ptr\<rightarrow>[''pxPrevious_C''])) q h a =
     h a"
  using raw_sentinel_whole_previous_update_tail8_pointwise[
    OF tail, where q=q and h=h]
  by (simp only: raw_sentinel_whole_previous_update_to_field)

end
