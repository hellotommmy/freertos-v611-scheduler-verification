theory List_V611_Raw_R6_Generic_Prefix
  imports "EAL6_FreeRTOS_V611_List_Raw_R5_Cycle.List_V611_Raw_R5_Cycle"
begin

text \<open>
  Address-parametric versions of the sentinel prefix bridge.  Unlike the R3
  witness lemmas, these statements do not mention the fixed 0x1000 list.
  They are byte-layout facts only: no full xLIST_ITEM_C allocation is assumed
  for the embedded xMINI_LIST_ITEM_C sentinel.
\<close>

lemma raw_sentinel_item_value_prefix_generic:
  "xLIST_ITEM_C.xItemValue_C (h_val h (raw_sentinel_ptr lp)) =
   xMINI_LIST_ITEM_C.xItemValue_C (xListEnd_C (h_val h lp))"
  by (simp
      flip: xLIST_ITEM_C_h_val_fields(1)
        xMINI_LIST_ITEM_C_h_val_fields(1)
        xLIST_C_h_val_fields(3)
      add: raw_sentinel_ptr_def field_lvalue_def
        xLIST_ITEM_C_xItemValue_C_fl
        xMINI_LIST_ITEM_C_xItemValue_C_fl
        xLIST_C_xListEnd_C_fl)

lemma raw_sentinel_next_prefix_generic:
  "xLIST_ITEM_C.pxNext_C (h_val h (raw_sentinel_ptr lp)) =
   xMINI_LIST_ITEM_C.pxNext_C (xListEnd_C (h_val h lp))"
  by (simp
      flip: xLIST_ITEM_C_h_val_fields(2)
        xMINI_LIST_ITEM_C_h_val_fields(2)
        xLIST_C_h_val_fields(3)
      add: raw_sentinel_ptr_def field_lvalue_def
        xLIST_ITEM_C_pxNext_C_fl
        xMINI_LIST_ITEM_C_pxNext_C_fl
        xLIST_C_xListEnd_C_fl)

lemma raw_sentinel_previous_prefix_generic:
  "xLIST_ITEM_C.pxPrevious_C (h_val h (raw_sentinel_ptr lp)) =
   xMINI_LIST_ITEM_C.pxPrevious_C (xListEnd_C (h_val h lp))"
  by (simp
      flip: xLIST_ITEM_C_h_val_fields(3)
        xMINI_LIST_ITEM_C_h_val_fields(3)
        xLIST_C_h_val_fields(3)
      add: raw_sentinel_ptr_def field_lvalue_def
        xLIST_ITEM_C_pxPrevious_C_fl
        xMINI_LIST_ITEM_C_pxPrevious_C_fl
        xLIST_C_xListEnd_C_fl)

corollary raw_next_at_end_item[simp]:
  "raw_next_at h lp (raw_end_item lp) =
   xMINI_LIST_ITEM_C.pxNext_C (xListEnd_C (h_val h lp))"
  by (simp add: raw_next_at_def)

corollary raw_prev_at_end_item[simp]:
  "raw_prev_at h lp (raw_end_item lp) =
   xMINI_LIST_ITEM_C.pxPrevious_C (xListEnd_C (h_val h lp))"
  by (simp add: raw_prev_at_def)

end
