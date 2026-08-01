theory List_V611_Raw_R3_Master
  imports "EAL6_FreeRTOS_V611_List_Raw_R3_Far_Frame.List_V611_Raw_R3_Far_Frame"
begin

text \<open>
  R3 master: mechanically conjoin the eight checker-green postcondition
  groups.  This theory does not unfold or symbolically execute the C
  function again.
\<close>

theorem raw_vListInsertEnd_empty_master:
  "vListInsertEnd' raw_list_ptr raw_item_ptr \<bullet>
     (raw_insert_end_prestate base d h k owner)
   \<lbrace>\<lambda>r t.
      r = Result () \<and>
      uxNumberOfItems_C
        (h_val (hrs_mem (t_hrs_' t)) raw_list_ptr) = 1 \<and>
      pxIndex_C
        (h_val (hrs_mem (t_hrs_' t)) raw_list_ptr) = raw_item_ptr \<and>
      xMINI_LIST_ITEM_C.pxNext_C
        (xListEnd_C (h_val (hrs_mem (t_hrs_' t)) raw_list_ptr)) =
          raw_item_ptr \<and>
      xMINI_LIST_ITEM_C.pxPrevious_C
        (xListEnd_C (h_val (hrs_mem (t_hrs_' t)) raw_list_ptr)) =
          raw_item_ptr \<and>
      xLIST_ITEM_C.pxNext_C
        (h_val (hrs_mem (t_hrs_' t)) raw_item_ptr) =
          raw_sentinel_ptr raw_list_ptr \<and>
      xLIST_ITEM_C.pxPrevious_C
        (h_val (hrs_mem (t_hrs_' t)) raw_item_ptr) =
          raw_sentinel_ptr raw_list_ptr \<and>
      pvContainer_C
        (h_val (hrs_mem (t_hrs_' t)) raw_item_ptr) =
          PTR_COERCE(xLIST_C \<rightarrow> unit) raw_list_ptr \<and>
      xLIST_ITEM_C.xItemValue_C
        (h_val (hrs_mem (t_hrs_' t)) raw_item_ptr) = k \<and>
      pvOwner_C
        (h_val (hrs_mem (t_hrs_' t)) raw_item_ptr) = owner \<and>
      (\<forall>a \<in> {raw_sentinel_tail_addr..+8}.
        hrs_mem (t_hrs_' t) a =
          hrs_mem
            (t_hrs_' (raw_insert_end_prestate base d h k owner)) a) \<and>
      hrs_mem (t_hrs_' t) raw_canary_addr =
        hrs_mem
          (t_hrs_' (raw_insert_end_prestate base d h k owner))
          raw_canary_addr \<and>
      hrs_htd (t_hrs_' t) =
        hrs_htd
          (t_hrs_' (raw_insert_end_prestate base d h k owner))
    \<rbrace>"
proof -
  let ?f = "vListInsertEnd' raw_list_ptr raw_item_ptr"
  let ?s0 = "raw_insert_end_prestate base d h k owner"
  have grouped:
    "?f \<bullet> ?s0
     \<lbrace>\<lambda>r t.
       (r = Result () \<and>
        uxNumberOfItems_C
          (h_val (hrs_mem (t_hrs_' t)) raw_list_ptr) = 1 \<and>
        pxIndex_C
          (h_val (hrs_mem (t_hrs_' t)) raw_list_ptr) = raw_item_ptr) \<and>
       (r = Result () \<and>
        xMINI_LIST_ITEM_C.pxNext_C
          (xListEnd_C (h_val (hrs_mem (t_hrs_' t)) raw_list_ptr)) =
            raw_item_ptr \<and>
        xMINI_LIST_ITEM_C.pxPrevious_C
          (xListEnd_C (h_val (hrs_mem (t_hrs_' t)) raw_list_ptr)) =
            raw_item_ptr) \<and>
       (r = Result () \<and>
        xLIST_ITEM_C.pxNext_C
          (h_val (hrs_mem (t_hrs_' t)) raw_item_ptr) =
            raw_sentinel_ptr raw_list_ptr \<and>
        xLIST_ITEM_C.pxPrevious_C
          (h_val (hrs_mem (t_hrs_' t)) raw_item_ptr) =
            raw_sentinel_ptr raw_list_ptr) \<and>
       (r = Result () \<and>
        pvContainer_C
          (h_val (hrs_mem (t_hrs_' t)) raw_item_ptr) =
            PTR_COERCE(xLIST_C \<rightarrow> unit) raw_list_ptr) \<and>
       (r = Result () \<and>
        xLIST_ITEM_C.xItemValue_C
          (h_val (hrs_mem (t_hrs_' t)) raw_item_ptr) = k \<and>
        pvOwner_C
          (h_val (hrs_mem (t_hrs_' t)) raw_item_ptr) = owner) \<and>
       (r = Result () \<and>
        (\<forall>a \<in> {raw_sentinel_tail_addr..+8}.
          hrs_mem (t_hrs_' t) a = hrs_mem (t_hrs_' ?s0) a)) \<and>
       (r = Result () \<and>
        hrs_mem (t_hrs_' t) raw_canary_addr =
          hrs_mem (t_hrs_' ?s0) raw_canary_addr) \<and>
       (r = Result () \<and>
        hrs_htd (t_hrs_' t) = hrs_htd (t_hrs_' ?s0))
     \<rbrace>"
    using raw_vListInsertEnd_empty_count_index[
        where base=base and d=d and h=h and k=k and owner=owner]
      raw_vListInsertEnd_empty_sentinel_links[
        where base=base and d=d and h=h and k=k and owner=owner]
      raw_vListInsertEnd_empty_item_links[
        where base=base and d=d and h=h and k=k and owner=owner]
      raw_vListInsertEnd_empty_container[
        where base=base and d=d and h=h and k=k and owner=owner]
      raw_vListInsertEnd_empty_key_owner[
        where base=base and d=d and h=h and k=k and owner=owner]
      raw_vListInsertEnd_empty_tail8[
        where base=base and d=d and h=h and k=k and owner=owner]
      raw_vListInsertEnd_empty_canary[
        where base=base and d=d and h=h and k=k and owner=owner]
      raw_vListInsertEnd_empty_htd[
        where base=base and d=d and h=h and k=k and owner=owner]
    by (simp only: runs_to_conj)
  show ?thesis
    apply (rule runs_to_weaken[OF grouped])
    apply simp
    done
qed

end
