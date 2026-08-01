theory Scheduler_List_ABI_Bridge
  imports
    "EAL6_FreeRTOS_V611_Scheduler_P2_Generated_Layout_First.Scheduler_P2_Generated_Layout_First"
begin

text \<open>
  This leaf records the ABI facts needed to view scheduler translation-unit
  list objects through the independently generated raw-list types.  The two
  generated record universes remain distinct; only pointer addresses and
  byte footprints are related here.
\<close>

definition abi_list_ptr ::
  "Scheduler_V611_Parse.xLIST_C ptr \<Rightarrow>
   List_V611_Raw_Skip_Translation.xLIST_C ptr"
where
  "abi_list_ptr p =
    PTR_COERCE(Scheduler_V611_Parse.xLIST_C \<rightarrow>
      List_V611_Raw_Skip_Translation.xLIST_C) p"

definition abi_item_ptr ::
  "Scheduler_V611_Parse.xLIST_ITEM_C ptr \<Rightarrow>
   List_V611_Raw_Skip_Translation.xLIST_ITEM_C ptr"
where
  "abi_item_ptr p =
    PTR_COERCE(Scheduler_V611_Parse.xLIST_ITEM_C \<rightarrow>
      List_V611_Raw_Skip_Translation.xLIST_ITEM_C) p"

lemma abi_list_ptr_ptr_val [simp]:
  "ptr_val (abi_list_ptr p) = ptr_val p"
  by (simp add: abi_list_ptr_def)

lemma abi_item_ptr_ptr_val [simp]:
  "ptr_val (abi_item_ptr p) = ptr_val p"
  by (simp add: abi_item_ptr_def)

lemma abi_list_ptr_eq_iff [simp]:
  "abi_list_ptr p = abi_list_ptr q \<longleftrightarrow> p = q"
  by (simp add: abi_list_ptr_def ptr_coerce_eq)

lemma abi_item_ptr_eq_iff [simp]:
  "abi_item_ptr p = abi_item_ptr q \<longleftrightarrow> p = q"
  by (simp add: abi_item_ptr_def ptr_coerce_eq)

lemma abi_list_ptr_NULL_iff [simp]:
  "abi_list_ptr p = NULL \<longleftrightarrow> p = NULL"
  by (simp add: abi_list_ptr_def)

lemma abi_item_ptr_NULL_iff [simp]:
  "abi_item_ptr p = NULL \<longleftrightarrow> p = NULL"
  by (simp add: abi_item_ptr_def)

lemma abi_list_ptr_NULL [simp]:
  "abi_list_ptr NULL = NULL"
  by (simp add: abi_list_ptr_def)

lemma abi_item_ptr_NULL [simp]:
  "abi_item_ptr NULL = NULL"
  by (simp add: abi_item_ptr_def)

print_statement Scheduler_V611_Parse.xLIST_C_size_of
print_statement List_V611_Raw_Skip_Translation.xLIST_C_size_of
print_statement Scheduler_V611_Parse.xLIST_C_align_of
print_statement List_V611_Raw_Skip_Translation.xLIST_C_align_of
print_statement Scheduler_V611_Parse.xLIST_ITEM_C_size_of
print_statement List_V611_Raw_Skip_Translation.xLIST_ITEM_C_size_of
print_statement Scheduler_V611_Parse.xLIST_ITEM_C_align_of
print_statement List_V611_Raw_Skip_Translation.xLIST_ITEM_C_align_of
print_statement Scheduler_V611_Parse.xMINI_LIST_ITEM_C_size_of
print_statement List_V611_Raw_Skip_Translation.xMINI_LIST_ITEM_C_size_of
print_statement Scheduler_V611_Parse.xMINI_LIST_ITEM_C_align_of
print_statement List_V611_Raw_Skip_Translation.xMINI_LIST_ITEM_C_align_of

lemma abi_xLIST_C_size:
  "size_of TYPE(Scheduler_V611_Parse.xLIST_C) =
   size_of TYPE(List_V611_Raw_Skip_Translation.xLIST_C)"
  by (simp add: Scheduler_V611_Parse.xLIST_C_size_of
      List_V611_Raw_Skip_Translation.xLIST_C_size_of)

lemma abi_xLIST_C_align:
  "align_of TYPE(Scheduler_V611_Parse.xLIST_C) =
   align_of TYPE(List_V611_Raw_Skip_Translation.xLIST_C)"
  by (simp add: Scheduler_V611_Parse.xLIST_C_align_of
      List_V611_Raw_Skip_Translation.xLIST_C_align_of)

lemma abi_xLIST_ITEM_C_size:
  "size_of TYPE(Scheduler_V611_Parse.xLIST_ITEM_C) =
   size_of TYPE(List_V611_Raw_Skip_Translation.xLIST_ITEM_C)"
  by (simp add: Scheduler_V611_Parse.xLIST_ITEM_C_size_of
      List_V611_Raw_Skip_Translation.xLIST_ITEM_C_size_of)

lemma abi_xLIST_ITEM_C_align:
  "align_of TYPE(Scheduler_V611_Parse.xLIST_ITEM_C) =
   align_of TYPE(List_V611_Raw_Skip_Translation.xLIST_ITEM_C)"
  by (simp add: Scheduler_V611_Parse.xLIST_ITEM_C_align_of
      List_V611_Raw_Skip_Translation.xLIST_ITEM_C_align_of)

lemma abi_xMINI_LIST_ITEM_C_size:
  "size_of TYPE(Scheduler_V611_Parse.xMINI_LIST_ITEM_C) =
   size_of TYPE(List_V611_Raw_Skip_Translation.xMINI_LIST_ITEM_C)"
  by (simp add: Scheduler_V611_Parse.xMINI_LIST_ITEM_C_size_of
      List_V611_Raw_Skip_Translation.xMINI_LIST_ITEM_C_size_of)

lemma abi_xMINI_LIST_ITEM_C_align:
  "align_of TYPE(Scheduler_V611_Parse.xMINI_LIST_ITEM_C) =
   align_of TYPE(List_V611_Raw_Skip_Translation.xMINI_LIST_ITEM_C)"
  by (simp add: Scheduler_V611_Parse.xMINI_LIST_ITEM_C_align_of
      List_V611_Raw_Skip_Translation.xMINI_LIST_ITEM_C_align_of)

lemma abi_list_ptr_c_guard:
  "c_guard (abi_list_ptr p) \<longleftrightarrow> c_guard p"
  unfolding abi_list_ptr_def
  apply (rule c_guard_ptr_coerce)
   apply (rule abi_xLIST_C_align)
  apply (rule abi_xLIST_C_size)
  done

lemma abi_item_ptr_c_guard:
  "c_guard (abi_item_ptr p) \<longleftrightarrow> c_guard p"
  unfolding abi_item_ptr_def
  apply (rule c_guard_ptr_coerce)
   apply (rule abi_xLIST_ITEM_C_align)
  apply (rule abi_xLIST_ITEM_C_size)
  done

definition scheduler_list_region ::
  "Scheduler_V611_Parse.xLIST_C ptr \<Rightarrow> 32 word set"
where
  "scheduler_list_region p =
    {ptr_val p..+size_of TYPE(Scheduler_V611_Parse.xLIST_C)}"

definition scheduler_item_region ::
  "Scheduler_V611_Parse.xLIST_ITEM_C ptr \<Rightarrow> 32 word set"
where
  "scheduler_item_region p =
    {ptr_val p..+size_of TYPE(Scheduler_V611_Parse.xLIST_ITEM_C)}"

lemma abi_list_region_eq:
  "List_V611_Raw_R5_Relation.raw_list_region (abi_list_ptr p) =
   scheduler_list_region p"
  by (simp add: List_V611_Raw_R5_Relation.raw_list_region_def
      scheduler_list_region_def abi_xLIST_C_size)

lemma abi_item_region_eq:
  "List_V611_Raw_R5_Relation.raw_item_region (abi_item_ptr p) =
   scheduler_item_region p"
  by (simp add: List_V611_Raw_R5_Relation.raw_item_region_def
      scheduler_item_region_def abi_xLIST_ITEM_C_size)

text \<open>Scheduler list roots, observed only through the raw pointer lens.\<close>

definition abi_ready_list_root ::
  "nat \<Rightarrow> List_V611_Raw_Skip_Translation.xLIST_C ptr"
where
  "abi_ready_list_root priority =
    abi_list_ptr
      (array_ptr_index Scheduler_V611_Parse.pxReadyTasksLists_' False priority)"

definition abi_delayed_list1_root ::
  "List_V611_Raw_Skip_Translation.xLIST_C ptr"
where
  "abi_delayed_list1_root =
    abi_list_ptr Scheduler_V611_Parse.xDelayedTaskList1_'"

definition abi_delayed_list2_root ::
  "List_V611_Raw_Skip_Translation.xLIST_C ptr"
where
  "abi_delayed_list2_root =
    abi_list_ptr Scheduler_V611_Parse.xDelayedTaskList2_'"

definition abi_pending_ready_list_root ::
  "List_V611_Raw_Skip_Translation.xLIST_C ptr"
where
  "abi_pending_ready_list_root =
    abi_list_ptr Scheduler_V611_Parse.xPendingReadyList_'"

definition abi_suspended_list_root ::
  "List_V611_Raw_Skip_Translation.xLIST_C ptr"
where
  "abi_suspended_list_root =
    abi_list_ptr Scheduler_V611_Parse.xSuspendedTaskList_'"

definition abi_current_delayed_list ::
  "Scheduler_V611_Parse.globals \<Rightarrow>
   List_V611_Raw_Skip_Translation.xLIST_C ptr"
where
  "abi_current_delayed_list s =
    abi_list_ptr (Scheduler_V611_Parse.globals.pxDelayedTaskList_' s)"

definition abi_overflow_delayed_list ::
  "Scheduler_V611_Parse.globals \<Rightarrow>
   List_V611_Raw_Skip_Translation.xLIST_C ptr"
where
  "abi_overflow_delayed_list s =
    abi_list_ptr (Scheduler_V611_Parse.globals.pxOverflowDelayedTaskList_' s)"

lemma abi_ready_list_root_ptr_val [simp]:
  "ptr_val (abi_ready_list_root priority) =
   ptr_val
     (array_ptr_index Scheduler_V611_Parse.pxReadyTasksLists_' False priority)"
  by (simp add: abi_ready_list_root_def)

lemma abi_delayed_list1_root_ptr_val [simp]:
  "ptr_val abi_delayed_list1_root =
   ptr_val Scheduler_V611_Parse.xDelayedTaskList1_'"
  by (simp add: abi_delayed_list1_root_def)

lemma abi_delayed_list2_root_ptr_val [simp]:
  "ptr_val abi_delayed_list2_root =
   ptr_val Scheduler_V611_Parse.xDelayedTaskList2_'"
  by (simp add: abi_delayed_list2_root_def)

lemma abi_current_delayed_list_ptr_val [simp]:
  "ptr_val (abi_current_delayed_list s) =
   ptr_val (Scheduler_V611_Parse.globals.pxDelayedTaskList_' s)"
  by (simp add: abi_current_delayed_list_def)

lemma abi_overflow_delayed_list_ptr_val [simp]:
  "ptr_val (abi_overflow_delayed_list s) =
   ptr_val (Scheduler_V611_Parse.globals.pxOverflowDelayedTaskList_' s)"
  by (simp add: abi_overflow_delayed_list_def)

text \<open>Embedded scheduler TCB list items, exposed as raw item pointers.\<close>

definition abi_generic_list_item_ptr ::
  "Scheduler_V611_Parse.tskTaskControlBlock_C ptr \<Rightarrow>
   List_V611_Raw_Skip_Translation.xLIST_ITEM_C ptr"
where
  "abi_generic_list_item_ptr tp =
    abi_item_ptr
      (PTR(Scheduler_V611_Parse.xLIST_ITEM_C)
        &(tp\<rightarrow>[''xGenericListItem_C'']))"

definition abi_event_list_item_ptr ::
  "Scheduler_V611_Parse.tskTaskControlBlock_C ptr \<Rightarrow>
   List_V611_Raw_Skip_Translation.xLIST_ITEM_C ptr"
where
  "abi_event_list_item_ptr tp =
    abi_item_ptr
      (PTR(Scheduler_V611_Parse.xLIST_ITEM_C)
        &(tp\<rightarrow>[''xEventListItem_C'']))"

lemma abi_generic_list_item_ptr_ptr_val [simp]:
  "ptr_val (abi_generic_list_item_ptr tp) =
   ptr_val
     (PTR(Scheduler_V611_Parse.xLIST_ITEM_C)
       &(tp\<rightarrow>[''xGenericListItem_C'']))"
  by (simp add: abi_generic_list_item_ptr_def)

lemma abi_event_list_item_ptr_ptr_val [simp]:
  "ptr_val (abi_event_list_item_ptr tp) =
   ptr_val
     (PTR(Scheduler_V611_Parse.xLIST_ITEM_C)
       &(tp\<rightarrow>[''xEventListItem_C'']))"
  by (simp add: abi_event_list_item_ptr_def)

text \<open>
  The fields used by the raw relation have the same generated offsets in both
  translation units.  Both generated facts are printed and each equality is
  also retained as a checked bridge theorem.
\<close>

print_statement Scheduler_V611_Parse.xLIST_C_uxNumberOfItems_C_fl
print_statement List_V611_Raw_Skip_Translation.xLIST_C_uxNumberOfItems_C_fl
print_statement Scheduler_V611_Parse.xLIST_C_pxIndex_C_fl
print_statement List_V611_Raw_Skip_Translation.xLIST_C_pxIndex_C_fl
print_statement Scheduler_V611_Parse.xLIST_C_xListEnd_C_fl
print_statement List_V611_Raw_Skip_Translation.xLIST_C_xListEnd_C_fl
print_statement Scheduler_V611_Parse.xLIST_ITEM_C_xItemValue_C_fl
print_statement List_V611_Raw_Skip_Translation.xLIST_ITEM_C_xItemValue_C_fl
print_statement Scheduler_V611_Parse.xLIST_ITEM_C_pxNext_C_fl
print_statement List_V611_Raw_Skip_Translation.xLIST_ITEM_C_pxNext_C_fl
print_statement Scheduler_V611_Parse.xLIST_ITEM_C_pxPrevious_C_fl
print_statement List_V611_Raw_Skip_Translation.xLIST_ITEM_C_pxPrevious_C_fl
print_statement Scheduler_V611_Parse.xLIST_ITEM_C_pvOwner_C_fl
print_statement List_V611_Raw_Skip_Translation.xLIST_ITEM_C_pvOwner_C_fl
print_statement Scheduler_V611_Parse.xLIST_ITEM_C_pvContainer_C_fl
print_statement List_V611_Raw_Skip_Translation.xLIST_ITEM_C_pvContainer_C_fl

lemma abi_xLIST_C_uxNumberOfItems_C_offset:
  "field_lvalue (p :: Scheduler_V611_Parse.xLIST_C ptr)
      [''uxNumberOfItems_C''] =
   field_lvalue (abi_list_ptr p) [''uxNumberOfItems_C'']"
  by (simp add: abi_list_ptr_def field_lvalue_def
      Scheduler_V611_Parse.xLIST_C_uxNumberOfItems_C_fl
      List_V611_Raw_Skip_Translation.xLIST_C_uxNumberOfItems_C_fl)

lemma abi_xLIST_C_pxIndex_C_offset:
  "field_lvalue (p :: Scheduler_V611_Parse.xLIST_C ptr) [''pxIndex_C''] =
   field_lvalue (abi_list_ptr p) [''pxIndex_C'']"
  by (simp add: abi_list_ptr_def field_lvalue_def
      Scheduler_V611_Parse.xLIST_C_pxIndex_C_fl
      List_V611_Raw_Skip_Translation.xLIST_C_pxIndex_C_fl)

lemma abi_xLIST_C_xListEnd_C_offset:
  "field_lvalue (p :: Scheduler_V611_Parse.xLIST_C ptr) [''xListEnd_C''] =
   field_lvalue (abi_list_ptr p) [''xListEnd_C'']"
  by (simp add: abi_list_ptr_def field_lvalue_def
      Scheduler_V611_Parse.xLIST_C_xListEnd_C_fl
      List_V611_Raw_Skip_Translation.xLIST_C_xListEnd_C_fl)

lemma abi_xLIST_ITEM_C_xItemValue_C_offset:
  "field_lvalue (p :: Scheduler_V611_Parse.xLIST_ITEM_C ptr)
      [''xItemValue_C''] =
   field_lvalue (abi_item_ptr p) [''xItemValue_C'']"
  by (simp add: abi_item_ptr_def field_lvalue_def
      Scheduler_V611_Parse.xLIST_ITEM_C_xItemValue_C_fl
      List_V611_Raw_Skip_Translation.xLIST_ITEM_C_xItemValue_C_fl)

lemma abi_xLIST_ITEM_C_pxNext_C_offset:
  "field_lvalue (p :: Scheduler_V611_Parse.xLIST_ITEM_C ptr) [''pxNext_C''] =
   field_lvalue (abi_item_ptr p) [''pxNext_C'']"
  by (simp add: abi_item_ptr_def field_lvalue_def
      Scheduler_V611_Parse.xLIST_ITEM_C_pxNext_C_fl
      List_V611_Raw_Skip_Translation.xLIST_ITEM_C_pxNext_C_fl)

lemma abi_xLIST_ITEM_C_pxPrevious_C_offset:
  "field_lvalue (p :: Scheduler_V611_Parse.xLIST_ITEM_C ptr)
      [''pxPrevious_C''] =
   field_lvalue (abi_item_ptr p) [''pxPrevious_C'']"
  by (simp add: abi_item_ptr_def field_lvalue_def
      Scheduler_V611_Parse.xLIST_ITEM_C_pxPrevious_C_fl
      List_V611_Raw_Skip_Translation.xLIST_ITEM_C_pxPrevious_C_fl)

lemma abi_xLIST_ITEM_C_pvOwner_C_offset:
  "field_lvalue (p :: Scheduler_V611_Parse.xLIST_ITEM_C ptr) [''pvOwner_C''] =
   field_lvalue (abi_item_ptr p) [''pvOwner_C'']"
  by (simp add: abi_item_ptr_def field_lvalue_def
      Scheduler_V611_Parse.xLIST_ITEM_C_pvOwner_C_fl
      List_V611_Raw_Skip_Translation.xLIST_ITEM_C_pvOwner_C_fl)

lemma abi_xLIST_ITEM_C_pvContainer_C_offset:
  "field_lvalue (p :: Scheduler_V611_Parse.xLIST_ITEM_C ptr)
      [''pvContainer_C''] =
   field_lvalue (abi_item_ptr p) [''pvContainer_C'']"
  by (simp add: abi_item_ptr_def field_lvalue_def
      Scheduler_V611_Parse.xLIST_ITEM_C_pvContainer_C_fl
      List_V611_Raw_Skip_Translation.xLIST_ITEM_C_pvContainer_C_fl)

lemma abi_sentinel_field_address_commutes:
  "abi_item_ptr
      (PTR(Scheduler_V611_Parse.xLIST_ITEM_C)
        &(p\<rightarrow>[''xListEnd_C''])) =
   PTR(List_V611_Raw_Skip_Translation.xLIST_ITEM_C)
     &((abi_list_ptr p)\<rightarrow>[''xListEnd_C''])"
  by (simp add: abi_item_ptr_def abi_list_ptr_def field_lvalue_def
      Scheduler_V611_Parse.xLIST_C_xListEnd_C_fl
      List_V611_Raw_Skip_Translation.xLIST_C_xListEnd_C_fl)

text \<open>
  Generated C records are packed types, so equal byte sizes also give the
  exact whole-value read through the coerced pointer.  This is a byte-level
  coercion statement, not record-type equality.
\<close>

lemma abi_list_h_val_packed:
  "h_val h (abi_list_ptr p) =
   COERCE(Scheduler_V611_Parse.xLIST_C \<rightarrow>
     List_V611_Raw_Skip_Translation.xLIST_C) (h_val h p)"
  unfolding abi_list_ptr_def
  by (rule h_val_coerce_ptr_coerce_packed[OF abi_xLIST_C_size])

lemma abi_item_h_val_packed:
  "h_val h (abi_item_ptr p) =
   COERCE(Scheduler_V611_Parse.xLIST_ITEM_C \<rightarrow>
     List_V611_Raw_Skip_Translation.xLIST_ITEM_C) (h_val h p)"
  unfolding abi_item_ptr_def
  by (rule h_val_coerce_ptr_coerce_packed[OF abi_xLIST_ITEM_C_size])

end
