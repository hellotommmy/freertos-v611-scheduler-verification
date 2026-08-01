theory Scheduler_List_ABI_Read_Lenses
  imports
    "EAL6_FreeRTOS_V611_Scheduler_List_ABI_Write_Bridge.Scheduler_List_ABI_Write_Bridge"
begin

text \<open>
  Field-level reads across the scheduler and raw-list generated structure
  universes.  The records remain distinct; corresponding pointer fields are
  related only by the address-preserving ABI item-pointer coercion.
\<close>

lemma h_val_pointer_value_coerce:
  fixes ps :: "('a::c_type_name ptr) ptr"
    and pr :: "('b::c_type_name ptr) ptr"
  assumes addr: "ptr_val ps = ptr_val pr"
  shows
    "h_val h pr =
     PTR_COERCE('a \<rightarrow> 'b) (h_val h ps)"
  using addr
  unfolding h_val_def
  by (simp add: from_bytes_def typ_info_ptr update_ti_t_def size_of_def)

lemma abi_item_next_h_val:
  "List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pxNext_C
      (h_val h (abi_item_ptr p)) =
   abi_item_ptr
      (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C (h_val h p))"
proof -
  have read:
    "h_val h
       (PTR(List_V611_Raw_Skip_Translation.xLIST_ITEM_C ptr)
         &((abi_item_ptr p)\<rightarrow>[''pxNext_C''])) =
     abi_item_ptr
       (h_val h
         (PTR(Scheduler_V611_Parse.xLIST_ITEM_C ptr)
           &(p\<rightarrow>[''pxNext_C''])))"
  proof -
    have core:
      "h_val h
         (PTR(List_V611_Raw_Skip_Translation.xLIST_ITEM_C ptr)
           &((abi_item_ptr p)\<rightarrow>[''pxNext_C''])) =
       PTR_COERCE(Scheduler_V611_Parse.xLIST_ITEM_C \<rightarrow>
         List_V611_Raw_Skip_Translation.xLIST_ITEM_C)
         (h_val h
           (PTR(Scheduler_V611_Parse.xLIST_ITEM_C ptr)
             &(p\<rightarrow>[''pxNext_C''])))"
      by (rule h_val_pointer_value_coerce;
          rule abi_item_next_field_address)
    then show ?thesis
      by (simp only: abi_item_ptr_def)
  qed
  then show ?thesis
    by (simp only:
      List_V611_Raw_Skip_Translation.xLIST_ITEM_C_h_val_fields(2)
      Scheduler_V611_Parse.xLIST_ITEM_C_h_val_fields(2))
qed

lemma abi_item_previous_h_val:
  "List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pxPrevious_C
      (h_val h (abi_item_ptr p)) =
   abi_item_ptr
      (Scheduler_V611_Parse.xLIST_ITEM_C.pxPrevious_C (h_val h p))"
  using h_val_pointer_value_coerce[
    OF abi_item_previous_field_address, where h=h]
  by (simp only:
      abi_item_ptr_def
      List_V611_Raw_Skip_Translation.xLIST_ITEM_C_h_val_fields(3)
      Scheduler_V611_Parse.xLIST_ITEM_C_h_val_fields(3))

lemma abi_item_key_h_val:
  "List_V611_Raw_Skip_Translation.xLIST_ITEM_C.xItemValue_C
      (h_val h (abi_item_ptr p)) =
   Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C (h_val h p)"
  by (simp
      flip:
        List_V611_Raw_Skip_Translation.xLIST_ITEM_C_h_val_fields(1)
        Scheduler_V611_Parse.xLIST_ITEM_C_h_val_fields(1)
      add: abi_xLIST_ITEM_C_xItemValue_C_offset)

lemma abi_item_owner_h_val:
  "List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
      (h_val h (abi_item_ptr p)) =
   Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C (h_val h p)"
  by (simp
      flip:
        List_V611_Raw_Skip_Translation.xLIST_ITEM_C_h_val_fields(4)
        Scheduler_V611_Parse.xLIST_ITEM_C_h_val_fields(4)
      add: abi_xLIST_ITEM_C_pvOwner_C_offset)

lemma abi_item_container_h_val:
  "List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvContainer_C
      (h_val h (abi_item_ptr p)) =
   Scheduler_V611_Parse.xLIST_ITEM_C.pvContainer_C (h_val h p)"
  by (simp
      flip:
        List_V611_Raw_Skip_Translation.xLIST_ITEM_C_h_val_fields(5)
        Scheduler_V611_Parse.xLIST_ITEM_C_h_val_fields(5)
      add: abi_xLIST_ITEM_C_pvContainer_C_offset)

lemma abi_list_index_h_val:
  "List_V611_Raw_Skip_Translation.xLIST_C.pxIndex_C
      (h_val h (abi_list_ptr lp)) =
   abi_item_ptr
      (Scheduler_V611_Parse.xLIST_C.pxIndex_C (h_val h lp))"
  using h_val_pointer_value_coerce[
    OF abi_list_index_field_address, where h=h]
  by (simp only:
      abi_item_ptr_def
      List_V611_Raw_Skip_Translation.xLIST_C_h_val_fields(2)
      Scheduler_V611_Parse.xLIST_C_h_val_fields(2))

lemma abi_list_count_h_val:
  "List_V611_Raw_Skip_Translation.xLIST_C.uxNumberOfItems_C
      (h_val h (abi_list_ptr lp)) =
   Scheduler_V611_Parse.xLIST_C.uxNumberOfItems_C (h_val h lp)"
  by (simp
      flip:
        List_V611_Raw_Skip_Translation.xLIST_C_h_val_fields(1)
        Scheduler_V611_Parse.xLIST_C_h_val_fields(1)
      add: abi_list_count_field_address)

lemma abi_sentinel_key_field_address:
  "PTR(32 word)
      &((PTR(Scheduler_V611_Parse.xMINI_LIST_ITEM_C)
          &(lp\<rightarrow>[''xListEnd_C'']))\<rightarrow>[''xItemValue_C'']) =
   PTR(32 word)
      &((PTR(List_V611_Raw_Skip_Translation.xMINI_LIST_ITEM_C)
          &((abi_list_ptr lp)\<rightarrow>[''xListEnd_C'']))
        \<rightarrow>[''xItemValue_C''])"
  by (simp add: abi_list_ptr_def field_lvalue_def
      Scheduler_V611_Parse.xLIST_C_xListEnd_C_fl
      Scheduler_V611_Parse.xMINI_LIST_ITEM_C_xItemValue_C_fl
      List_V611_Raw_Skip_Translation.xLIST_C_xListEnd_C_fl
      List_V611_Raw_Skip_Translation.xMINI_LIST_ITEM_C_xItemValue_C_fl)

lemma abi_sentinel_key_h_val:
  "List_V611_Raw_Skip_Translation.xMINI_LIST_ITEM_C.xItemValue_C
      (List_V611_Raw_Skip_Translation.xLIST_C.xListEnd_C
        (h_val h (abi_list_ptr lp))) =
   Scheduler_V611_Parse.xMINI_LIST_ITEM_C.xItemValue_C
      (Scheduler_V611_Parse.xLIST_C.xListEnd_C (h_val h lp))"
  by (simp
      flip:
        List_V611_Raw_Skip_Translation.xMINI_LIST_ITEM_C_h_val_fields(1)
        List_V611_Raw_Skip_Translation.xLIST_C_h_val_fields(3)
        Scheduler_V611_Parse.xMINI_LIST_ITEM_C_h_val_fields(1)
        Scheduler_V611_Parse.xLIST_C_h_val_fields(3)
      add: abi_list_ptr_def field_lvalue_def
        Scheduler_V611_Parse.xLIST_C_xListEnd_C_fl
        Scheduler_V611_Parse.xMINI_LIST_ITEM_C_xItemValue_C_fl
        List_V611_Raw_Skip_Translation.xLIST_C_xListEnd_C_fl
        List_V611_Raw_Skip_Translation.xMINI_LIST_ITEM_C_xItemValue_C_fl)

lemma abi_sentinel_next_field_address:
  "ptr_val
     (PTR(Scheduler_V611_Parse.xLIST_ITEM_C ptr)
       &((PTR(Scheduler_V611_Parse.xMINI_LIST_ITEM_C)
          &(lp\<rightarrow>[''xListEnd_C'']))\<rightarrow>[''pxNext_C''])) =
   ptr_val
     (PTR(List_V611_Raw_Skip_Translation.xLIST_ITEM_C ptr)
       &((PTR(List_V611_Raw_Skip_Translation.xMINI_LIST_ITEM_C)
          &((abi_list_ptr lp)\<rightarrow>[''xListEnd_C'']))
        \<rightarrow>[''pxNext_C'']))"
  by (simp add: abi_list_ptr_def field_lvalue_def
      Scheduler_V611_Parse.xLIST_C_xListEnd_C_fl
      Scheduler_V611_Parse.xMINI_LIST_ITEM_C_pxNext_C_fl
      List_V611_Raw_Skip_Translation.xLIST_C_xListEnd_C_fl
      List_V611_Raw_Skip_Translation.xMINI_LIST_ITEM_C_pxNext_C_fl)

lemma abi_sentinel_next_h_val:
  "List_V611_Raw_Skip_Translation.xMINI_LIST_ITEM_C.pxNext_C
      (List_V611_Raw_Skip_Translation.xLIST_C.xListEnd_C
        (h_val h (abi_list_ptr lp))) =
   abi_item_ptr
      (Scheduler_V611_Parse.xMINI_LIST_ITEM_C.pxNext_C
        (Scheduler_V611_Parse.xLIST_C.xListEnd_C (h_val h lp)))"
  using h_val_pointer_value_coerce[
    OF abi_sentinel_next_field_address, where h=h]
  by (simp only:
      abi_item_ptr_def
      List_V611_Raw_Skip_Translation.xMINI_LIST_ITEM_C_h_val_fields(2)
      List_V611_Raw_Skip_Translation.xLIST_C_h_val_fields(3)
      Scheduler_V611_Parse.xMINI_LIST_ITEM_C_h_val_fields(2)
      Scheduler_V611_Parse.xLIST_C_h_val_fields(3))

lemma abi_sentinel_previous_field_address:
  "ptr_val
     (PTR(Scheduler_V611_Parse.xLIST_ITEM_C ptr)
       &((PTR(Scheduler_V611_Parse.xMINI_LIST_ITEM_C)
          &(lp\<rightarrow>[''xListEnd_C'']))\<rightarrow>[''pxPrevious_C''])) =
   ptr_val
     (PTR(List_V611_Raw_Skip_Translation.xLIST_ITEM_C ptr)
       &((PTR(List_V611_Raw_Skip_Translation.xMINI_LIST_ITEM_C)
          &((abi_list_ptr lp)\<rightarrow>[''xListEnd_C'']))
        \<rightarrow>[''pxPrevious_C'']))"
  by (simp add: abi_list_ptr_def field_lvalue_def
      Scheduler_V611_Parse.xLIST_C_xListEnd_C_fl
      Scheduler_V611_Parse.xMINI_LIST_ITEM_C_pxPrevious_C_fl
      List_V611_Raw_Skip_Translation.xLIST_C_xListEnd_C_fl
      List_V611_Raw_Skip_Translation.xMINI_LIST_ITEM_C_pxPrevious_C_fl)

lemma abi_sentinel_previous_h_val:
  "List_V611_Raw_Skip_Translation.xMINI_LIST_ITEM_C.pxPrevious_C
      (List_V611_Raw_Skip_Translation.xLIST_C.xListEnd_C
        (h_val h (abi_list_ptr lp))) =
   abi_item_ptr
      (Scheduler_V611_Parse.xMINI_LIST_ITEM_C.pxPrevious_C
        (Scheduler_V611_Parse.xLIST_C.xListEnd_C (h_val h lp)))"
  using h_val_pointer_value_coerce[
    OF abi_sentinel_previous_field_address, where h=h]
  by (simp only:
      abi_item_ptr_def
      List_V611_Raw_Skip_Translation.xMINI_LIST_ITEM_C_h_val_fields(3)
      List_V611_Raw_Skip_Translation.xLIST_C_h_val_fields(3)
      Scheduler_V611_Parse.xMINI_LIST_ITEM_C_h_val_fields(3)
      Scheduler_V611_Parse.xLIST_C_h_val_fields(3))

end
