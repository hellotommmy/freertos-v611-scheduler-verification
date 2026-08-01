theory List_V611_Raw_R1_Init
  imports "EAL6_FreeRTOS_V611_List_Raw_R0_Guards.List_V611_Raw_R0_Guards"
begin

text \<open>
  R1 symbolically executes only vListInitialise'.  The postcondition exposes
  the five source-level initialisation facts, while a separate byte canary
  records a concrete frame fact outside the list object's 20-byte footprint.
\<close>

definition raw_canary_addr :: addr where
  "raw_canary_addr = 0x3000"

lemma raw_3000_outside_list_interval:
  "(0x3000 :: addr) \<notin> {0x1000..+20}"
proof -
  have no_wrap: "unat (0x1000 :: addr) + 20 \<le> addr_card"
    by (simp add: addr_card_def card_word)
  have membership:
    "((0x3000 :: addr) \<in> {0x1000..+20}) =
      (unat (0x1000 :: addr) \<le> unat (0x3000 :: addr) \<and>
       unat (0x3000 :: addr) < unat (0x1000 :: addr) + 20)"
    by (rule intvl_no_overflow_nat[OF no_wrap])
  from membership show ?thesis by simp
qed

lemma raw_list_heap_update_canary[simp]:
  "heap_update raw_list_ptr (v :: xLIST_C) h raw_canary_addr =
   h raw_canary_addr"
  unfolding heap_update_def raw_list_ptr_def raw_canary_addr_def
  apply (rule heap_update_nmem_same)
  apply (simp add: raw_3000_outside_list_interval)
  done

lemma raw_list_h_val_after_self_update[simp]:
  "h_val
     (hrs_mem
       (hrs_mem_update (heap_update raw_list_ptr (v :: xLIST_C)) h))
     raw_list_ptr = v"
  by (simp add: hrs_mem_update h_val_heap_update)

lemma raw_vListInitialise_exact_post:
  "vListInitialise' raw_list_ptr \<bullet> s
   \<lbrace>\<lambda>r t.
      r = Result () \<and>
      uxNumberOfItems_C
        (h_val (hrs_mem (t_hrs_' t)) raw_list_ptr) = 0 \<and>
      pxIndex_C
        (h_val (hrs_mem (t_hrs_' t)) raw_list_ptr) =
          raw_sentinel_ptr raw_list_ptr \<and>
      xMINI_LIST_ITEM_C.xItemValue_C
        (xListEnd_C (h_val (hrs_mem (t_hrs_' t)) raw_list_ptr)) =
          0xFFFFFFFF \<and>
      xMINI_LIST_ITEM_C.pxNext_C
        (xListEnd_C (h_val (hrs_mem (t_hrs_' t)) raw_list_ptr)) =
          raw_sentinel_ptr raw_list_ptr \<and>
      xMINI_LIST_ITEM_C.pxPrevious_C
        (xListEnd_C (h_val (hrs_mem (t_hrs_' t)) raw_list_ptr)) =
          raw_sentinel_ptr raw_list_ptr
    \<rbrace>"
  unfolding vListInitialise'_def raw_sentinel_ptr_def
  by runs_to_vcg

lemma raw_vListInitialise_canary_frame:
  "vListInitialise' raw_list_ptr \<bullet> s
   \<lbrace>\<lambda>r t.
      r = Result () \<and>
      hrs_mem (t_hrs_' t) raw_canary_addr =
        hrs_mem (t_hrs_' s) raw_canary_addr
    \<rbrace>"
  unfolding vListInitialise'_def
  apply runs_to_vcg
  apply (simp add: hrs_mem_update)
  done

end
