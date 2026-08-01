theory List_V611_Raw_R4_Master
  imports "EAL6_FreeRTOS_V611_List_Raw_R4_Far_Frame.List_V611_Raw_R4_Far_Frame"
begin

text \<open>
  R4 master: mechanically conjoin the five checker-green postcondition
  groups.  This theory neither unfolds vListRemove'_def nor invokes a VCG.
\<close>

theorem raw_vListRemove_singleton_master:
  "vListRemove' raw_item_ptr \<bullet>
     (raw_singleton_prestate base d h k owner)
   \<lbrace>\<lambda>r t.
      r = Result () \<and>
      uxNumberOfItems_C
        (h_val (hrs_mem (t_hrs_' t)) raw_list_ptr) = 0 \<and>
      pxIndex_C
        (h_val (hrs_mem (t_hrs_' t)) raw_list_ptr) =
          raw_sentinel_ptr raw_list_ptr \<and>
      xMINI_LIST_ITEM_C.pxNext_C
        (xListEnd_C (h_val (hrs_mem (t_hrs_' t)) raw_list_ptr)) =
          raw_sentinel_ptr raw_list_ptr \<and>
      xMINI_LIST_ITEM_C.pxPrevious_C
        (xListEnd_C (h_val (hrs_mem (t_hrs_' t)) raw_list_ptr)) =
          raw_sentinel_ptr raw_list_ptr \<and>
      pvContainer_C
        (h_val (hrs_mem (t_hrs_' t)) raw_item_ptr) = NULL \<and>
      xLIST_ITEM_C.pxNext_C
        (h_val (hrs_mem (t_hrs_' t)) raw_item_ptr) =
          raw_sentinel_ptr raw_list_ptr \<and>
      xLIST_ITEM_C.pxPrevious_C
        (h_val (hrs_mem (t_hrs_' t)) raw_item_ptr) =
          raw_sentinel_ptr raw_list_ptr \<and>
      xLIST_ITEM_C.xItemValue_C
        (h_val (hrs_mem (t_hrs_' t)) raw_item_ptr) = k \<and>
      pvOwner_C
        (h_val (hrs_mem (t_hrs_' t)) raw_item_ptr) = owner \<and>
      (\<forall>a \<in> {raw_sentinel_tail_addr..+8}.
        hrs_mem (t_hrs_' t) a =
          hrs_mem
            (t_hrs_' (raw_singleton_prestate base d h k owner)) a) \<and>
      hrs_mem (t_hrs_' t) raw_canary_addr =
        hrs_mem
          (t_hrs_' (raw_singleton_prestate base d h k owner))
          raw_canary_addr \<and>
      hrs_htd (t_hrs_' t) =
        hrs_htd
          (t_hrs_' (raw_singleton_prestate base d h k owner))
    \<rbrace>"
proof -
  let ?f = "vListRemove' raw_item_ptr"
  let ?s0 = "raw_singleton_prestate base d h k owner"
  have grouped:
    "?f \<bullet> ?s0
     \<lbrace>\<lambda>r t.
       (r = Result () \<and>
        uxNumberOfItems_C
          (h_val (hrs_mem (t_hrs_' t)) raw_list_ptr) = 0 \<and>
        pxIndex_C
          (h_val (hrs_mem (t_hrs_' t)) raw_list_ptr) =
            raw_sentinel_ptr raw_list_ptr) \<and>
       (r = Result () \<and>
        xMINI_LIST_ITEM_C.pxNext_C
          (xListEnd_C (h_val (hrs_mem (t_hrs_' t)) raw_list_ptr)) =
            raw_sentinel_ptr raw_list_ptr \<and>
        xMINI_LIST_ITEM_C.pxPrevious_C
          (xListEnd_C (h_val (hrs_mem (t_hrs_' t)) raw_list_ptr)) =
            raw_sentinel_ptr raw_list_ptr \<and>
        pvContainer_C
          (h_val (hrs_mem (t_hrs_' t)) raw_item_ptr) = NULL) \<and>
       (r = Result () \<and>
        xLIST_ITEM_C.pxNext_C
          (h_val (hrs_mem (t_hrs_' t)) raw_item_ptr) =
            raw_sentinel_ptr raw_list_ptr \<and>
        xLIST_ITEM_C.pxPrevious_C
          (h_val (hrs_mem (t_hrs_' t)) raw_item_ptr) =
            raw_sentinel_ptr raw_list_ptr \<and>
        xLIST_ITEM_C.xItemValue_C
          (h_val (hrs_mem (t_hrs_' t)) raw_item_ptr) = k \<and>
        pvOwner_C
          (h_val (hrs_mem (t_hrs_' t)) raw_item_ptr) = owner) \<and>
       (r = Result () \<and>
        (\<forall>a \<in> {raw_sentinel_tail_addr..+8}.
          hrs_mem (t_hrs_' t) a = hrs_mem (t_hrs_' ?s0) a)) \<and>
       (r = Result () \<and>
        hrs_mem (t_hrs_' t) raw_canary_addr =
          hrs_mem (t_hrs_' ?s0) raw_canary_addr \<and>
        hrs_htd (t_hrs_' t) = hrs_htd (t_hrs_' ?s0))
     \<rbrace>"
    using raw_vListRemove_singleton_count_index[
        where base=base and d=d and h=h and k=k and owner=owner]
      raw_vListRemove_singleton_topology_container[
        where base=base and d=d and h=h and k=k and owner=owner]
      raw_vListRemove_singleton_item_frame[
        where base=base and d=d and h=h and k=k and owner=owner]
      raw_vListRemove_singleton_tail8[
        where base=base and d=d and h=h and k=k and owner=owner]
      raw_vListRemove_singleton_canary_htd[
        where base=base and d=d and h=h and k=k and owner=owner]
    by (simp only: runs_to_conj)
  show ?thesis
    apply (rule runs_to_weaken[OF grouped])
    apply simp
    done
qed

end
