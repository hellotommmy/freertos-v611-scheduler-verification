theory List_V611_Raw_R3_Prefix
  imports "EAL6_FreeRTOS_V611_List_Raw_R2_Init_Item.List_V611_Raw_R2_Init_Item"
begin

text \<open>
  R3a is the raw common-prefix gate.  It relates only the three fields that
  xLIST_ITEM_C and the embedded xMINI_LIST_ITEM_C actually share.  No heap
  typing or 20-byte allocation premise is attached to the cast sentinel.
\<close>

lemma raw_sentinel_item_value_prefix:
  "xLIST_ITEM_C.xItemValue_C
     (h_val h (raw_sentinel_ptr raw_list_ptr)) =
   xMINI_LIST_ITEM_C.xItemValue_C
     (xListEnd_C (h_val h raw_list_ptr))"
  by (simp
      flip: xLIST_ITEM_C_h_val_fields(1)
        xMINI_LIST_ITEM_C_h_val_fields(1)
        xLIST_C_h_val_fields(3)
      add: raw_sentinel_ptr_def raw_list_ptr_def field_lvalue_def
        xLIST_ITEM_C_xItemValue_C_fl
        xMINI_LIST_ITEM_C_xItemValue_C_fl
        xLIST_C_xListEnd_C_fl)

lemma raw_sentinel_next_prefix:
  "xLIST_ITEM_C.pxNext_C
     (h_val h (raw_sentinel_ptr raw_list_ptr)) =
   xMINI_LIST_ITEM_C.pxNext_C
     (xListEnd_C (h_val h raw_list_ptr))"
  by (simp
      flip: xLIST_ITEM_C_h_val_fields(2)
        xMINI_LIST_ITEM_C_h_val_fields(2)
        xLIST_C_h_val_fields(3)
      add: raw_sentinel_ptr_def raw_list_ptr_def field_lvalue_def
        xLIST_ITEM_C_pxNext_C_fl
        xMINI_LIST_ITEM_C_pxNext_C_fl
        xLIST_C_xListEnd_C_fl)

lemma raw_sentinel_previous_prefix:
  "xLIST_ITEM_C.pxPrevious_C
     (h_val h (raw_sentinel_ptr raw_list_ptr)) =
   xMINI_LIST_ITEM_C.pxPrevious_C
     (xListEnd_C (h_val h raw_list_ptr))"
  by (simp
      flip: xLIST_ITEM_C_h_val_fields(3)
        xMINI_LIST_ITEM_C_h_val_fields(3)
        xLIST_C_h_val_fields(3)
      add: raw_sentinel_ptr_def raw_list_ptr_def field_lvalue_def
        xLIST_ITEM_C_pxPrevious_C_fl
        xMINI_LIST_ITEM_C_pxPrevious_C_fl
        xLIST_C_xListEnd_C_fl)

end
