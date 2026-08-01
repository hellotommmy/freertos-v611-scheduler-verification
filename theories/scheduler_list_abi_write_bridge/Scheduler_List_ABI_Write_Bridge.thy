theory Scheduler_List_ABI_Write_Bridge
  imports
    "EAL6_FreeRTOS_V611_Scheduler_List_ABI_Bridge.Scheduler_List_ABI_Bridge"
begin

text \<open>
  Stage D starts with the single write correspondence needed to install a
  positive-delay wake key.  The scheduler source writes the nested Generic
  list-item field directly; the raw-list view writes the same 32-bit field at
  the coerced embedded-item address.  Both statements below quantify over an
  arbitrary intermediate byte heap.
\<close>

definition scheduler_generic_item_key_ptr ::
  "Scheduler_V611_Parse.tskTaskControlBlock_C ptr \<Rightarrow> 32 word ptr"
where
  "scheduler_generic_item_key_ptr tp =
    PTR(32 word)
      &(tp\<rightarrow>[''xGenericListItem_C'', ''xItemValue_C''])"

definition raw_generic_item_key_ptr ::
  "Scheduler_V611_Parse.tskTaskControlBlock_C ptr \<Rightarrow> 32 word ptr"
where
  "raw_generic_item_key_ptr tp =
    PTR(32 word)
      &((abi_generic_list_item_ptr tp)\<rightarrow>[''xItemValue_C''])"

lemma abi_generic_item_key_field_address:
  "scheduler_generic_item_key_ptr tp = raw_generic_item_key_ptr tp"
  by (simp add: scheduler_generic_item_key_ptr_def raw_generic_item_key_ptr_def
      abi_generic_list_item_ptr_def abi_item_ptr_def field_lvalue_def
      Scheduler_V611_Parse.tskTaskControlBlock_C_xGenericListItem_C_fl
      Scheduler_V611_Parse.xLIST_ITEM_C_xItemValue_C_fl
      List_V611_Raw_Skip_Translation.xLIST_ITEM_C_xItemValue_C_fl)

lemma abi_generic_item_key_field_write:
  "heap_update (scheduler_generic_item_key_ptr tp) wake h =
   heap_update (raw_generic_item_key_ptr tp) wake h"
  by (simp only: abi_generic_item_key_field_address)

text \<open>
  Pointer-valued fields need a value coercion as well as an equal byte address:
  their generated target types are deliberately distinct.  Pointer encoding
  depends only on the address, so corresponding writes agree on the complete
  byte heap without a guard or prestate assumption.
\<close>

lemma heap_update_pointer_value_coerce:
  fixes ps :: "('a::c_type_name ptr) ptr"
    and pr :: "('b::c_type_name ptr) ptr"
    and q :: "'a ptr"
  assumes addr: "ptr_val ps = ptr_val pr"
  shows
    "heap_update ps q h =
     heap_update pr (PTR_COERCE('a \<rightarrow> 'b) q) h"
  using addr
  unfolding heap_update_def
  by (cases q; simp add: to_bytes_def typ_info_ptr)

lemma abi_item_next_field_address:
  "ptr_val
     (PTR(Scheduler_V611_Parse.xLIST_ITEM_C ptr)
       &(p\<rightarrow>[''pxNext_C''])) =
   ptr_val
     (PTR(List_V611_Raw_Skip_Translation.xLIST_ITEM_C ptr)
       &((abi_item_ptr p)\<rightarrow>[''pxNext_C'']))"
  by (simp add: abi_xLIST_ITEM_C_pxNext_C_offset)

lemma abi_item_next_field_write:
  "heap_update
     (PTR(Scheduler_V611_Parse.xLIST_ITEM_C ptr)
       &(p\<rightarrow>[''pxNext_C''])) q h =
   heap_update
     (PTR(List_V611_Raw_Skip_Translation.xLIST_ITEM_C ptr)
       &((abi_item_ptr p)\<rightarrow>[''pxNext_C'']))
     (abi_item_ptr q) h"
proof -
  have core:
    "heap_update
       (PTR(Scheduler_V611_Parse.xLIST_ITEM_C ptr)
         &(p\<rightarrow>[''pxNext_C''])) q h =
     heap_update
       (PTR(List_V611_Raw_Skip_Translation.xLIST_ITEM_C ptr)
         &((abi_item_ptr p)\<rightarrow>[''pxNext_C'']))
       (PTR_COERCE(Scheduler_V611_Parse.xLIST_ITEM_C \<rightarrow>
          List_V611_Raw_Skip_Translation.xLIST_ITEM_C) q) h"
    by (rule heap_update_pointer_value_coerce;
        rule abi_item_next_field_address)
  then show ?thesis
    by (simp only: abi_item_ptr_def)
qed

lemma abi_item_previous_field_address:
  "ptr_val
     (PTR(Scheduler_V611_Parse.xLIST_ITEM_C ptr)
       &(p\<rightarrow>[''pxPrevious_C''])) =
   ptr_val
     (PTR(List_V611_Raw_Skip_Translation.xLIST_ITEM_C ptr)
       &((abi_item_ptr p)\<rightarrow>[''pxPrevious_C'']))"
  by (simp add: abi_xLIST_ITEM_C_pxPrevious_C_offset)

lemma abi_item_previous_field_write:
  "heap_update
     (PTR(Scheduler_V611_Parse.xLIST_ITEM_C ptr)
       &(p\<rightarrow>[''pxPrevious_C''])) q h =
   heap_update
     (PTR(List_V611_Raw_Skip_Translation.xLIST_ITEM_C ptr)
       &((abi_item_ptr p)\<rightarrow>[''pxPrevious_C'']))
     (abi_item_ptr q) h"
proof -
  have core:
    "heap_update
       (PTR(Scheduler_V611_Parse.xLIST_ITEM_C ptr)
         &(p\<rightarrow>[''pxPrevious_C''])) q h =
     heap_update
       (PTR(List_V611_Raw_Skip_Translation.xLIST_ITEM_C ptr)
         &((abi_item_ptr p)\<rightarrow>[''pxPrevious_C'']))
       (PTR_COERCE(Scheduler_V611_Parse.xLIST_ITEM_C \<rightarrow>
          List_V611_Raw_Skip_Translation.xLIST_ITEM_C) q) h"
    by (rule heap_update_pointer_value_coerce;
        rule abi_item_previous_field_address)
  then show ?thesis
    by (simp only: abi_item_ptr_def)
qed

lemma abi_item_container_field_address:
  "PTR(unit ptr) &(p\<rightarrow>[''pvContainer_C'']) =
   PTR(unit ptr) &((abi_item_ptr p)\<rightarrow>[''pvContainer_C''])"
  by (simp add: abi_xLIST_ITEM_C_pvContainer_C_offset)

lemma abi_item_container_field_write:
  "heap_update
     (PTR(unit ptr) &(p\<rightarrow>[''pvContainer_C''])) container h =
   heap_update
     (PTR(unit ptr) &((abi_item_ptr p)\<rightarrow>[''pvContainer_C'']))
     container h"
  by (simp only: abi_item_container_field_address)

lemma abi_list_index_field_address:
  "ptr_val
     (PTR(Scheduler_V611_Parse.xLIST_ITEM_C ptr)
       &(lp\<rightarrow>[''pxIndex_C''])) =
   ptr_val
     (PTR(List_V611_Raw_Skip_Translation.xLIST_ITEM_C ptr)
       &((abi_list_ptr lp)\<rightarrow>[''pxIndex_C'']))"
  by (simp add: abi_xLIST_C_pxIndex_C_offset)

lemma abi_list_index_field_write:
  "heap_update
     (PTR(Scheduler_V611_Parse.xLIST_ITEM_C ptr)
       &(lp\<rightarrow>[''pxIndex_C''])) q h =
   heap_update
     (PTR(List_V611_Raw_Skip_Translation.xLIST_ITEM_C ptr)
       &((abi_list_ptr lp)\<rightarrow>[''pxIndex_C'']))
     (abi_item_ptr q) h"
proof -
  have core:
    "heap_update
       (PTR(Scheduler_V611_Parse.xLIST_ITEM_C ptr)
         &(lp\<rightarrow>[''pxIndex_C''])) q h =
     heap_update
       (PTR(List_V611_Raw_Skip_Translation.xLIST_ITEM_C ptr)
         &((abi_list_ptr lp)\<rightarrow>[''pxIndex_C'']))
       (PTR_COERCE(Scheduler_V611_Parse.xLIST_ITEM_C \<rightarrow>
          List_V611_Raw_Skip_Translation.xLIST_ITEM_C) q) h"
    by (rule heap_update_pointer_value_coerce;
        rule abi_list_index_field_address)
  then show ?thesis
    by (simp only: abi_item_ptr_def)
qed

lemma abi_list_count_field_address:
  "PTR(32 word) &(lp\<rightarrow>[''uxNumberOfItems_C'']) =
   PTR(32 word) &((abi_list_ptr lp)\<rightarrow>[''uxNumberOfItems_C''])"
  by (simp add: abi_xLIST_C_uxNumberOfItems_C_offset)

lemma abi_list_count_field_write:
  "heap_update
     (PTR(32 word) &(lp\<rightarrow>[''uxNumberOfItems_C''])) count h =
   heap_update
     (PTR(32 word) &((abi_list_ptr lp)\<rightarrow>[''uxNumberOfItems_C'']))
     count h"
  by (simp only: abi_list_count_field_address)

end
