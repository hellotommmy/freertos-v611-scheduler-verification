theory List_V611_Raw_R3_Prestate
  imports "EAL6_FreeRTOS_V611_List_Raw_R3_Tail.List_V611_Raw_R3_Tail"
begin

text \<open>
  R3c constructs one concrete empty-list/fresh-item witness.  It names the
  raw heap and state explicitly, checks every source-level prestate field,
  and records the heap-typing component without yet executing
  vListInsertEnd'.
\<close>

definition raw_empty_list_value :: xLIST_C where
  "raw_empty_list_value =
    uxNumberOfItems_C_update (\<lambda>_. 0)
     (pxIndex_C_update (\<lambda>_. raw_sentinel_ptr raw_list_ptr)
      (xListEnd_C_update (\<lambda>_.
        xMINI_LIST_ITEM_C.xItemValue_C_update (\<lambda>_. 0xFFFFFFFF)
         (xMINI_LIST_ITEM_C.pxNext_C_update
           (\<lambda>_. raw_sentinel_ptr raw_list_ptr)
          (xMINI_LIST_ITEM_C.pxPrevious_C_update
            (\<lambda>_. raw_sentinel_ptr raw_list_ptr)
            (undefined :: xMINI_LIST_ITEM_C))))
       (undefined :: xLIST_C)))"

definition raw_fresh_item_value ::
  "32 word \<Rightarrow> unit ptr \<Rightarrow> xLIST_ITEM_C"
where
  "raw_fresh_item_value k owner =
    xLIST_ITEM_C.xItemValue_C_update (\<lambda>_. k)
     (xLIST_ITEM_C.pxNext_C_update
       (\<lambda>_. raw_sentinel_ptr raw_list_ptr)
      (xLIST_ITEM_C.pxPrevious_C_update
        (\<lambda>_. raw_sentinel_ptr raw_list_ptr)
       (pvOwner_C_update (\<lambda>_. owner)
        (pvContainer_C_update (\<lambda>_. NULL)
          (undefined :: xLIST_ITEM_C)))))"

definition raw_insert_end_preheap ::
  "heap_mem \<Rightarrow> 32 word \<Rightarrow> unit ptr \<Rightarrow> heap_mem"
where
  "raw_insert_end_preheap base k owner =
    heap_update raw_item_ptr (raw_fresh_item_value k owner)
      (heap_update raw_list_ptr raw_empty_list_value base)"

definition raw_insert_end_prestate ::
  "globals \<Rightarrow> heap_typ_desc \<Rightarrow>
   heap_mem \<Rightarrow> 32 word \<Rightarrow> unit ptr \<Rightarrow> globals"
where
  "raw_insert_end_prestate base d h k owner =
    t_hrs_'_update
      (\<lambda>_. (raw_insert_end_preheap h k owner, d)) base"

lemma raw_list_h_val_after_item_update_direct[simp]:
  "h_val (heap_update raw_item_ptr (v :: xLIST_ITEM_C) h) raw_list_ptr =
   h_val h raw_list_ptr"
proof -
  show ?thesis
    using raw_list_h_val_after_item_update[
      where v=v and h="(h, empty_htd)"]
    by (simp add: hrs_mem_update_def hrs_mem_def)
qed

lemma raw_insert_end_prestate_heap:
  "hrs_mem
     (t_hrs_' (raw_insert_end_prestate base d h k owner)) =
   raw_insert_end_preheap h k owner"
  by (simp add: raw_insert_end_prestate_def hrs_mem_def)

lemma raw_insert_end_prestate_htd:
  "hrs_htd
     (t_hrs_' (raw_insert_end_prestate base d h k owner)) = d"
  by (simp add: raw_insert_end_prestate_def hrs_htd_def)

corollary raw_insert_end_prestate_htd_unchanged:
  "hrs_htd
     (t_hrs_'
       (raw_insert_end_prestate base (hrs_htd (t_hrs_' base))
         h k owner)) =
   hrs_htd (t_hrs_' base)"
  by (rule raw_insert_end_prestate_htd)

lemma raw_insert_end_prestate_fields:
  fixes base :: globals
    and d :: heap_typ_desc
    and h :: heap_mem
    and k :: "32 word"
    and owner :: "unit ptr"
  defines "s0 \<equiv> raw_insert_end_prestate base d h k owner"
  shows
    "uxNumberOfItems_C
       (h_val (hrs_mem (t_hrs_' s0)) raw_list_ptr) = 0 \<and>
     pxIndex_C (h_val (hrs_mem (t_hrs_' s0)) raw_list_ptr) =
       raw_sentinel_ptr raw_list_ptr \<and>
     xMINI_LIST_ITEM_C.xItemValue_C
       (xListEnd_C (h_val (hrs_mem (t_hrs_' s0)) raw_list_ptr)) =
       0xFFFFFFFF \<and>
     xMINI_LIST_ITEM_C.pxNext_C
       (xListEnd_C (h_val (hrs_mem (t_hrs_' s0)) raw_list_ptr)) =
       raw_sentinel_ptr raw_list_ptr \<and>
     xMINI_LIST_ITEM_C.pxPrevious_C
       (xListEnd_C (h_val (hrs_mem (t_hrs_' s0)) raw_list_ptr)) =
       raw_sentinel_ptr raw_list_ptr \<and>
     xLIST_ITEM_C.xItemValue_C
       (h_val (hrs_mem (t_hrs_' s0)) raw_item_ptr) = k \<and>
     xLIST_ITEM_C.pxNext_C
       (h_val (hrs_mem (t_hrs_' s0)) raw_item_ptr) =
       raw_sentinel_ptr raw_list_ptr \<and>
     xLIST_ITEM_C.pxPrevious_C
       (h_val (hrs_mem (t_hrs_' s0)) raw_item_ptr) =
       raw_sentinel_ptr raw_list_ptr \<and>
     pvOwner_C (h_val (hrs_mem (t_hrs_' s0)) raw_item_ptr) = owner \<and>
     pvContainer_C (h_val (hrs_mem (t_hrs_' s0)) raw_item_ptr) = NULL"
  unfolding s0_def raw_insert_end_prestate_def raw_insert_end_preheap_def
    raw_empty_list_value_def raw_fresh_item_value_def
  by (simp add: hrs_mem_def h_val_heap_update)

end
