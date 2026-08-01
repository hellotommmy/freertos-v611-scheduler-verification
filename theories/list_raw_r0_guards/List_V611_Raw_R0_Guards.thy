theory List_V611_Raw_R0_Guards
  imports "EAL6_FreeRTOS_V611_List_Raw_Skip.List_V611_Raw_Skip_Translation"
begin

text \<open>
  R0 of the raw-heap bridge: three fixed, disjoint witness addresses and
  their exact C guards.  This theory deliberately contains no symbolic
  execution; later bricks may rely on these guards without recomputing word
  intervals.
\<close>

definition raw_list_ptr :: "xLIST_C ptr" where
  "raw_list_ptr = Ptr 0x1000"

definition raw_item_ptr :: "xLIST_ITEM_C ptr" where
  "raw_item_ptr = Ptr 0x2000"

definition raw_sentinel_ptr :: "xLIST_C ptr \<Rightarrow> xLIST_ITEM_C ptr" where
  "raw_sentinel_ptr list = PTR(xLIST_ITEM_C) &(list\<rightarrow>[''xListEnd_C''])"

lemma raw_1000_no_null_interval:
  "(0 :: addr) \<notin> {0x1000..+20}"
proof -
  have no_wrap: "unat (0x1000 :: addr) + 20 \<le> addr_card"
    by (simp add: addr_card_def card_word)
  have membership:
    "((0 :: addr) \<in> {0x1000..+20}) =
      (unat (0x1000 :: addr) \<le> unat (0 :: addr) \<and>
       unat (0 :: addr) < unat (0x1000 :: addr) + 20)"
    by (rule intvl_no_overflow_nat[OF no_wrap])
  from membership show ?thesis by simp
qed

lemma raw_2000_no_null_interval:
  "(0 :: addr) \<notin> {0x2000..+20}"
proof -
  have no_wrap: "unat (0x2000 :: addr) + 20 \<le> addr_card"
    by (simp add: addr_card_def card_word)
  have membership:
    "((0 :: addr) \<in> {0x2000..+20}) =
      (unat (0x2000 :: addr) \<le> unat (0 :: addr) \<and>
       unat (0 :: addr) < unat (0x2000 :: addr) + 20)"
    by (rule intvl_no_overflow_nat[OF no_wrap])
  from membership show ?thesis by simp
qed

lemma raw_1008_no_null_interval:
  "(0 :: addr) \<notin> {0x1008..+20}"
proof -
  have no_wrap: "unat (0x1008 :: addr) + 20 \<le> addr_card"
    by (simp add: addr_card_def card_word)
  have membership:
    "((0 :: addr) \<in> {0x1008..+20}) =
      (unat (0x1008 :: addr) \<le> unat (0 :: addr) \<and>
       unat (0 :: addr) < unat (0x1008 :: addr) + 20)"
    by (rule intvl_no_overflow_nat[OF no_wrap])
  from membership show ?thesis by simp
qed

lemma raw_sentinel_ptr_at_witness[simp]:
  "raw_sentinel_ptr raw_list_ptr = (Ptr 0x1008 :: xLIST_ITEM_C ptr)"
  unfolding raw_sentinel_ptr_def raw_list_ptr_def
  by (simp add: field_lvalue_def xLIST_C_xListEnd_C_fl)

lemma raw_list_ptr_guard[simp]:
  "c_guard raw_list_ptr"
  unfolding raw_list_ptr_def
  by (simp add: c_guard_def c_null_guard_def ptr_aligned_def align_of_def
      size_of_def raw_1000_no_null_interval)

lemma raw_item_ptr_guard[simp]:
  "c_guard raw_item_ptr"
  unfolding raw_item_ptr_def
  by (simp add: c_guard_def c_null_guard_def ptr_aligned_def align_of_def
      size_of_def raw_2000_no_null_interval)

lemma raw_sentinel_ptr_guard[simp]:
  "c_guard (raw_sentinel_ptr raw_list_ptr)"
  by (simp add: c_guard_def c_null_guard_def ptr_aligned_def align_of_def
      size_of_def raw_1008_no_null_interval)

theorem raw_needle_pointer_guards:
  "c_guard raw_list_ptr \<and>
   c_guard raw_item_ptr \<and>
   c_guard (raw_sentinel_ptr raw_list_ptr)"
  apply (intro conjI)
  apply (rule raw_list_ptr_guard)
  apply (rule raw_item_ptr_guard)
  apply (rule raw_sentinel_ptr_guard)
  done

end
