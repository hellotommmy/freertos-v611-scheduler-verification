theory List_V611_Raw_R3_Tail
  imports "EAL6_FreeRTOS_V611_List_Raw_R3_Prefix.List_V611_Raw_R3_Prefix"
begin

text \<open>
  R3b isolates the raw locality obligation created by using a full
  xLIST_ITEM_C read/modify/write at the embedded 12-byte sentinel.  The
  generated field-update conversions are used before any byte-frame proof;
  no full 20-byte sentinel allocation premise is introduced.
\<close>

print_statement xLIST_ITEM_C_heap_update_fields(2)
print_statement xLIST_ITEM_C_heap_update_fields(3)

definition raw_sentinel_tail_addr :: addr where
  "raw_sentinel_tail_addr = 0x1014"

lemma raw_sentinel_whole_next_update_to_field:
  "heap_update (raw_sentinel_ptr raw_list_ptr)
      (xLIST_ITEM_C.pxNext_C_update (\<lambda>_. q)
        (h_val h (raw_sentinel_ptr raw_list_ptr))) h =
   heap_update
      (PTR(xLIST_ITEM_C ptr)
        &(raw_sentinel_ptr raw_list_ptr\<rightarrow>[''pxNext_C''])) q h"
  apply (rule sym)
  apply (rule xLIST_ITEM_C_heap_update_fields(2))
  apply (rule raw_sentinel_ptr_guard)
  done

lemma raw_sentinel_whole_previous_update_to_field:
  "heap_update (raw_sentinel_ptr raw_list_ptr)
      (xLIST_ITEM_C.pxPrevious_C_update (\<lambda>_. q)
        (h_val h (raw_sentinel_ptr raw_list_ptr))) h =
   heap_update
      (PTR(xLIST_ITEM_C ptr)
        &(raw_sentinel_ptr raw_list_ptr\<rightarrow>[''pxPrevious_C''])) q h"
  apply (rule sym)
  apply (rule xLIST_ITEM_C_heap_update_fields(3))
  apply (rule raw_sentinel_ptr_guard)
  done

lemma raw_sentinel_next_field_at_witness[simp]:
  "PTR(xLIST_ITEM_C ptr)
      &(raw_sentinel_ptr raw_list_ptr\<rightarrow>[''pxNext_C'']) =
    (Ptr 0x100C :: xLIST_ITEM_C ptr ptr)"
  by (simp add: field_lvalue_def xLIST_ITEM_C_pxNext_C_fl)

lemma raw_sentinel_next_field_tail_disjoint:
  "{(0x100C :: addr)..+4} \<inter> {raw_sentinel_tail_addr..+8} = {}"
proof -
  have field_no_wrap: "unat (0x100C :: addr) + 4 \<le> addr_card"
    by (simp add: addr_card_def card_word)
  have tail_no_wrap: "unat (0x1014 :: addr) + 8 \<le> addr_card"
    by (simp add: addr_card_def card_word)
  have field_range:
    "{(0x100C :: addr)..+4} =
      {x. unat (0x100C :: addr) \<le> unat x \<and>
          unat x < unat (0x100C :: addr) + 4}"
    by (rule intvl_no_overflow_nat_conv[OF field_no_wrap])
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
      "x \<in> {(0x100C :: addr)..+4} \<inter>
        {raw_sentinel_tail_addr..+8}"
    have upper: "unat x < 4112"
      using xmem by (simp add: field_range)
    have lower: "4116 \<le> unat x"
      using xmem by (simp add: tail_range)
    have "(4116 :: nat) < 4112"
      by (rule le_less_trans[OF lower upper])
    then show False by simp
  qed
qed

lemma raw_sentinel_whole_next_update_tail8_pointwise:
  assumes tail: "a \<in> {raw_sentinel_tail_addr..+8}"
  shows
    "heap_update (raw_sentinel_ptr raw_list_ptr)
       (xLIST_ITEM_C.pxNext_C_update (\<lambda>_. q)
         (h_val h (raw_sentinel_ptr raw_list_ptr))) h a = h a"
proof -
  have outside: "a \<notin> {(0x100C :: addr)..+4}"
    using raw_sentinel_next_field_tail_disjoint tail by blast
  show ?thesis
  apply (subst raw_sentinel_whole_next_update_to_field)
  apply (simp only: raw_sentinel_next_field_at_witness)
  unfolding heap_update_def
  apply (rule heap_update_nmem_same)
  using outside
  apply simp
  done
qed

corollary raw_sentinel_whole_next_update_tail8:
  "\<forall>a \<in> {raw_sentinel_tail_addr..+8}.
     heap_update (raw_sentinel_ptr raw_list_ptr)
       (xLIST_ITEM_C.pxNext_C_update (\<lambda>_. q)
         (h_val h (raw_sentinel_ptr raw_list_ptr))) h a = h a"
  by (intro ballI; rule raw_sentinel_whole_next_update_tail8_pointwise)

lemma raw_sentinel_previous_field_at_witness[simp]:
  "PTR(xLIST_ITEM_C ptr)
      &(raw_sentinel_ptr raw_list_ptr\<rightarrow>[''pxPrevious_C'']) =
    (Ptr 0x1010 :: xLIST_ITEM_C ptr ptr)"
  by (simp add: field_lvalue_def xLIST_ITEM_C_pxPrevious_C_fl)

lemma raw_sentinel_previous_field_tail_disjoint:
  "{(0x1010 :: addr)..+4} \<inter> {raw_sentinel_tail_addr..+8} = {}"
proof -
  have field_no_wrap: "unat (0x1010 :: addr) + 4 \<le> addr_card"
    by (simp add: addr_card_def card_word)
  have tail_no_wrap: "unat (0x1014 :: addr) + 8 \<le> addr_card"
    by (simp add: addr_card_def card_word)
  have field_range:
    "{(0x1010 :: addr)..+4} =
      {x. unat (0x1010 :: addr) \<le> unat x \<and>
          unat x < unat (0x1010 :: addr) + 4}"
    by (rule intvl_no_overflow_nat_conv[OF field_no_wrap])
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
      "x \<in> {(0x1010 :: addr)..+4} \<inter>
        {raw_sentinel_tail_addr..+8}"
    have upper: "unat x < 4116"
      using xmem by (simp add: field_range)
    have lower: "4116 \<le> unat x"
      using xmem by (simp add: tail_range)
    then show False
      using upper by simp
  qed
qed

lemma raw_sentinel_whole_previous_update_tail8_pointwise:
  assumes tail: "a \<in> {raw_sentinel_tail_addr..+8}"
  shows
    "heap_update (raw_sentinel_ptr raw_list_ptr)
       (xLIST_ITEM_C.pxPrevious_C_update (\<lambda>_. q)
         (h_val h (raw_sentinel_ptr raw_list_ptr))) h a = h a"
proof -
  have outside: "a \<notin> {(0x1010 :: addr)..+4}"
    using raw_sentinel_previous_field_tail_disjoint tail by blast
  show ?thesis
  apply (subst raw_sentinel_whole_previous_update_to_field)
  apply (simp only: raw_sentinel_previous_field_at_witness)
  unfolding heap_update_def
  apply (rule heap_update_nmem_same)
  using outside
  apply simp
  done
qed

corollary raw_sentinel_whole_previous_update_tail8:
  "\<forall>a \<in> {raw_sentinel_tail_addr..+8}.
     heap_update (raw_sentinel_ptr raw_list_ptr)
       (xLIST_ITEM_C.pxPrevious_C_update (\<lambda>_. q)
         (h_val h (raw_sentinel_ptr raw_list_ptr))) h a = h a"
  by (intro ballI; rule raw_sentinel_whole_previous_update_tail8_pointwise)

definition raw_sentinel_mini_ptr :: "xMINI_LIST_ITEM_C ptr" where
  "raw_sentinel_mini_ptr =
    PTR(xMINI_LIST_ITEM_C) &(raw_list_ptr\<rightarrow>[''xListEnd_C''])"

lemma raw_sentinel_mini_ptr_at_witness:
  "raw_sentinel_mini_ptr = (Ptr 0x1008 :: xMINI_LIST_ITEM_C ptr)"
  unfolding raw_sentinel_mini_ptr_def raw_list_ptr_def
  by (simp add: field_lvalue_def xLIST_C_xListEnd_C_fl)

lemma raw_1008_mini_no_null_interval:
  "(0 :: addr) \<notin> {0x1008..+12}"
proof -
  have no_wrap: "unat (0x1008 :: addr) + 12 \<le> addr_card"
    by (simp add: addr_card_def card_word)
  have membership:
    "((0 :: addr) \<in> {0x1008..+12}) =
      (unat (0x1008 :: addr) \<le> unat (0 :: addr) \<and>
       unat (0 :: addr) < unat (0x1008 :: addr) + 12)"
    by (rule intvl_no_overflow_nat[OF no_wrap])
  from membership show ?thesis by simp
qed

lemma raw_sentinel_mini_ptr_guard[simp]:
  "c_guard raw_sentinel_mini_ptr"
  by (simp add: raw_sentinel_mini_ptr_at_witness c_guard_def
      c_null_guard_def ptr_aligned_def align_of_def size_of_def
      raw_1008_mini_no_null_interval)

lemma raw_sentinel_mini_value:
  "h_val h raw_sentinel_mini_ptr = xListEnd_C (h_val h raw_list_ptr)"
  unfolding raw_sentinel_mini_ptr_def
  by (rule xLIST_C_h_val_fields(3))

lemma raw_sentinel_mini_whole_next_update_to_field:
  "heap_update raw_sentinel_mini_ptr
      (xMINI_LIST_ITEM_C.pxNext_C_update (\<lambda>_. q)
        (h_val h raw_sentinel_mini_ptr)) h =
   heap_update
      (PTR(xLIST_ITEM_C ptr)
        &(raw_sentinel_mini_ptr\<rightarrow>[''pxNext_C''])) q h"
  apply (rule sym)
  apply (rule xMINI_LIST_ITEM_C_heap_update_fields(2))
  apply (rule raw_sentinel_mini_ptr_guard)
  done

lemma raw_sentinel_mini_whole_previous_update_to_field:
  "heap_update raw_sentinel_mini_ptr
      (xMINI_LIST_ITEM_C.pxPrevious_C_update (\<lambda>_. q)
        (h_val h raw_sentinel_mini_ptr)) h =
   heap_update
      (PTR(xLIST_ITEM_C ptr)
        &(raw_sentinel_mini_ptr\<rightarrow>[''pxPrevious_C''])) q h"
  apply (rule sym)
  apply (rule xMINI_LIST_ITEM_C_heap_update_fields(3))
  apply (rule raw_sentinel_mini_ptr_guard)
  done

lemma raw_list_whole_end_update_to_field:
  "heap_update raw_list_ptr
      (xListEnd_C_update (\<lambda>_. v) (h_val h raw_list_ptr)) h =
   heap_update raw_sentinel_mini_ptr v h"
  unfolding raw_sentinel_mini_ptr_def
  apply (rule sym)
  apply (rule xLIST_C_heap_update_fields(3))
  apply (rule raw_list_ptr_guard)
  done

lemma raw_sentinel_mini_next_field_at_witness[simp]:
  "PTR(xLIST_ITEM_C ptr)
      &(raw_sentinel_mini_ptr\<rightarrow>[''pxNext_C'']) =
    (Ptr 0x100C :: xLIST_ITEM_C ptr ptr)"
  by (simp add: raw_sentinel_mini_ptr_at_witness field_lvalue_def
      xMINI_LIST_ITEM_C_pxNext_C_fl)

lemma raw_sentinel_whole_next_update_to_list:
  "heap_update (raw_sentinel_ptr raw_list_ptr)
      (xLIST_ITEM_C.pxNext_C_update (\<lambda>_. q)
        (h_val h (raw_sentinel_ptr raw_list_ptr))) h =
   heap_update raw_list_ptr
      (xListEnd_C_update
        (\<lambda>_. xMINI_LIST_ITEM_C.pxNext_C_update (\<lambda>_. q)
          (h_val h raw_sentinel_mini_ptr))
        (h_val h raw_list_ptr)) h"
proof -
  let ?mini =
    "xMINI_LIST_ITEM_C.pxNext_C_update (\<lambda>_. q)
      (h_val h raw_sentinel_mini_ptr)"
  have
    "heap_update (raw_sentinel_ptr raw_list_ptr)
        (xLIST_ITEM_C.pxNext_C_update (\<lambda>_. q)
          (h_val h (raw_sentinel_ptr raw_list_ptr))) h =
      heap_update
        (PTR(xLIST_ITEM_C ptr)
          &(raw_sentinel_ptr raw_list_ptr\<rightarrow>[''pxNext_C''])) q h"
    by (rule raw_sentinel_whole_next_update_to_field)
  also have "... = heap_update
          (PTR(xLIST_ITEM_C ptr)
            &(raw_sentinel_mini_ptr\<rightarrow>[''pxNext_C''])) q h"
    by (simp add: field_lvalue_def xLIST_ITEM_C_pxNext_C_fl
        xMINI_LIST_ITEM_C_pxNext_C_fl raw_sentinel_mini_ptr_at_witness)
  also have "... = heap_update raw_sentinel_mini_ptr ?mini h"
    by (rule sym, rule raw_sentinel_mini_whole_next_update_to_field)
  also have "... = heap_update raw_list_ptr
          (xListEnd_C_update (\<lambda>_. ?mini)
            (h_val h raw_list_ptr)) h"
    by (rule sym, rule raw_list_whole_end_update_to_field)
  finally show ?thesis .
qed

lemma raw_sentinel_mini_previous_field_at_witness[simp]:
  "PTR(xLIST_ITEM_C ptr)
      &(raw_sentinel_mini_ptr\<rightarrow>[''pxPrevious_C'']) =
    (Ptr 0x1010 :: xLIST_ITEM_C ptr ptr)"
  by (simp add: raw_sentinel_mini_ptr_at_witness field_lvalue_def
      xMINI_LIST_ITEM_C_pxPrevious_C_fl)

lemma raw_sentinel_whole_previous_update_to_list:
  "heap_update (raw_sentinel_ptr raw_list_ptr)
      (xLIST_ITEM_C.pxPrevious_C_update (\<lambda>_. q)
        (h_val h (raw_sentinel_ptr raw_list_ptr))) h =
   heap_update raw_list_ptr
      (xListEnd_C_update
        (\<lambda>_. xMINI_LIST_ITEM_C.pxPrevious_C_update (\<lambda>_. q)
          (h_val h raw_sentinel_mini_ptr))
        (h_val h raw_list_ptr)) h"
proof -
  let ?mini =
    "xMINI_LIST_ITEM_C.pxPrevious_C_update (\<lambda>_. q)
      (h_val h raw_sentinel_mini_ptr)"
  have
    "heap_update (raw_sentinel_ptr raw_list_ptr)
        (xLIST_ITEM_C.pxPrevious_C_update (\<lambda>_. q)
          (h_val h (raw_sentinel_ptr raw_list_ptr))) h =
      heap_update
        (PTR(xLIST_ITEM_C ptr)
          &(raw_sentinel_ptr raw_list_ptr\<rightarrow>[''pxPrevious_C''])) q h"
    by (rule raw_sentinel_whole_previous_update_to_field)
  also have "... = heap_update
          (PTR(xLIST_ITEM_C ptr)
            &(raw_sentinel_mini_ptr\<rightarrow>[''pxPrevious_C''])) q h"
    by (simp add: field_lvalue_def xLIST_ITEM_C_pxPrevious_C_fl
        xMINI_LIST_ITEM_C_pxPrevious_C_fl
        raw_sentinel_mini_ptr_at_witness)
  also have "... = heap_update raw_sentinel_mini_ptr ?mini h"
    by (rule sym, rule raw_sentinel_mini_whole_previous_update_to_field)
  also have "... = heap_update raw_list_ptr
          (xListEnd_C_update (\<lambda>_. ?mini)
            (h_val h raw_list_ptr)) h"
    by (rule sym, rule raw_list_whole_end_update_to_field)
  finally show ?thesis .
qed

lemma raw_sentinel_previous_survives_next_update:
  "xMINI_LIST_ITEM_C.pxPrevious_C
     (xListEnd_C
       (h_val
         (heap_update (raw_sentinel_ptr raw_list_ptr)
           (xLIST_ITEM_C.pxNext_C_update (\<lambda>_. q)
             (h_val h (raw_sentinel_ptr raw_list_ptr))) h)
         raw_list_ptr)) =
   xMINI_LIST_ITEM_C.pxPrevious_C
     (xListEnd_C (h_val h raw_list_ptr))"
  apply (subst raw_sentinel_whole_next_update_to_list)
  apply (simp add: raw_sentinel_mini_value)
  done

lemma raw_sentinel_next_survives_previous_update:
  "xMINI_LIST_ITEM_C.pxNext_C
     (xListEnd_C
       (h_val
         (heap_update (raw_sentinel_ptr raw_list_ptr)
           (xLIST_ITEM_C.pxPrevious_C_update (\<lambda>_. q)
             (h_val h (raw_sentinel_ptr raw_list_ptr))) h)
         raw_list_ptr)) =
   xMINI_LIST_ITEM_C.pxNext_C
     (xListEnd_C (h_val h raw_list_ptr))"
  apply (subst raw_sentinel_whole_previous_update_to_list)
  apply (simp add: raw_sentinel_mini_value)
  done

end
