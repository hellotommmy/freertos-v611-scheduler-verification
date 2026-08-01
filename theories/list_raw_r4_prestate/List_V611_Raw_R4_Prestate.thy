theory List_V611_Raw_R4_Prestate
  imports "EAL6_FreeRTOS_V611_List_Raw_R3_Master.List_V611_Raw_R3_Master"
begin

text \<open>
  R4a freezes the concrete singleton/empty interfaces and constructs an
  independent singleton witness for vListRemove'.  The witness is stated
  directly; it does not reuse the R3 insert postcondition as a definition.
\<close>

definition raw_singleton_heap_fields :: "heap_mem \<Rightarrow> bool" where
  "raw_singleton_heap_fields h \<longleftrightarrow>
     uxNumberOfItems_C (h_val h raw_list_ptr) = 1 \<and>
     pxIndex_C (h_val h raw_list_ptr) = raw_item_ptr \<and>
     xMINI_LIST_ITEM_C.xItemValue_C
       (xListEnd_C (h_val h raw_list_ptr)) = 0xFFFFFFFF \<and>
     xMINI_LIST_ITEM_C.pxNext_C
       (xListEnd_C (h_val h raw_list_ptr)) = raw_item_ptr \<and>
     xMINI_LIST_ITEM_C.pxPrevious_C
       (xListEnd_C (h_val h raw_list_ptr)) = raw_item_ptr \<and>
     xLIST_ITEM_C.pxNext_C (h_val h raw_item_ptr) =
       raw_sentinel_ptr raw_list_ptr \<and>
     xLIST_ITEM_C.pxPrevious_C (h_val h raw_item_ptr) =
       raw_sentinel_ptr raw_list_ptr \<and>
     pvContainer_C (h_val h raw_item_ptr) =
       PTR_COERCE(xLIST_C \<rightarrow> unit) raw_list_ptr"

definition raw_singleton_fields :: "globals \<Rightarrow> bool" where
  "raw_singleton_fields s \<longleftrightarrow>
     raw_singleton_heap_fields (hrs_mem (t_hrs_' s))"

definition raw_empty_heap_fields :: "heap_mem \<Rightarrow> bool" where
  "raw_empty_heap_fields h \<longleftrightarrow>
     uxNumberOfItems_C (h_val h raw_list_ptr) = 0 \<and>
     pxIndex_C (h_val h raw_list_ptr) =
       raw_sentinel_ptr raw_list_ptr \<and>
     xMINI_LIST_ITEM_C.xItemValue_C
       (xListEnd_C (h_val h raw_list_ptr)) = 0xFFFFFFFF \<and>
     xMINI_LIST_ITEM_C.pxNext_C
       (xListEnd_C (h_val h raw_list_ptr)) =
       raw_sentinel_ptr raw_list_ptr \<and>
     xMINI_LIST_ITEM_C.pxPrevious_C
       (xListEnd_C (h_val h raw_list_ptr)) =
       raw_sentinel_ptr raw_list_ptr"

definition raw_singleton_list_value :: xLIST_C where
  "raw_singleton_list_value =
     uxNumberOfItems_C_update (\<lambda>_. 1)
      (pxIndex_C_update (\<lambda>_. raw_item_ptr)
       (xListEnd_C_update
         (\<lambda>e.
           xMINI_LIST_ITEM_C.pxNext_C_update (\<lambda>_. raw_item_ptr)
            (xMINI_LIST_ITEM_C.pxPrevious_C_update
              (\<lambda>_. raw_item_ptr) e))
         raw_empty_list_value))"

definition raw_linked_item_value ::
  "32 word \<Rightarrow> unit ptr \<Rightarrow> xLIST_ITEM_C"
where
  "raw_linked_item_value k owner =
     pvContainer_C_update
       (\<lambda>_. PTR_COERCE(xLIST_C \<rightarrow> unit) raw_list_ptr)
       (raw_fresh_item_value k owner)"

definition raw_singleton_preheap ::
  "heap_mem \<Rightarrow> 32 word \<Rightarrow> unit ptr \<Rightarrow> heap_mem"
where
  "raw_singleton_preheap base k owner =
     heap_update raw_item_ptr (raw_linked_item_value k owner)
       (heap_update raw_list_ptr raw_singleton_list_value base)"

definition raw_singleton_prestate ::
  "globals \<Rightarrow> heap_typ_desc \<Rightarrow>
   heap_mem \<Rightarrow> 32 word \<Rightarrow> unit ptr \<Rightarrow> globals"
where
  "raw_singleton_prestate base d h k owner =
     t_hrs_'_update
       (\<lambda>_. (raw_singleton_preheap h k owner, d)) base"

lemma raw_singleton_prestate_heap:
  "hrs_mem
     (t_hrs_' (raw_singleton_prestate base d h k owner)) =
   raw_singleton_preheap h k owner"
  by (simp add: raw_singleton_prestate_def hrs_mem_def)

lemma raw_singleton_prestate_htd:
  "hrs_htd
     (t_hrs_' (raw_singleton_prestate base d h k owner)) = d"
  by (simp add: raw_singleton_prestate_def hrs_htd_def)

corollary raw_singleton_prestate_htd_unchanged:
  "hrs_htd
     (t_hrs_'
       (raw_singleton_prestate base (hrs_htd (t_hrs_' base))
         h k owner)) =
   hrs_htd (t_hrs_' base)"
  by (rule raw_singleton_prestate_htd)

lemma raw_singleton_prestate_fields:
  fixes base :: globals
    and d :: heap_typ_desc
    and h :: heap_mem
    and k :: "32 word"
    and owner :: "unit ptr"
  defines "s0 \<equiv> raw_singleton_prestate base d h k owner"
  shows
    "raw_singleton_fields s0 \<and>
     xLIST_ITEM_C.xItemValue_C
       (h_val (hrs_mem (t_hrs_' s0)) raw_item_ptr) = k \<and>
     pvOwner_C
       (h_val (hrs_mem (t_hrs_' s0)) raw_item_ptr) = owner"
  unfolding s0_def raw_singleton_fields_def
    raw_singleton_heap_fields_def raw_singleton_prestate_def
    raw_singleton_preheap_def raw_singleton_list_value_def
    raw_linked_item_value_def raw_empty_list_value_def
    raw_fresh_item_value_def
  by (simp add: hrs_mem_def h_val_heap_update)

lemma raw_singleton_prestate_heap_fields:
  "raw_singleton_heap_fields
     (raw_singleton_preheap h k owner)"
  using raw_singleton_prestate_fields[
    where base="undefined :: globals" and d=empty_htd
      and h=h and k=k and owner=owner]
  by (simp add: raw_singleton_fields_def raw_singleton_prestate_heap)

end
