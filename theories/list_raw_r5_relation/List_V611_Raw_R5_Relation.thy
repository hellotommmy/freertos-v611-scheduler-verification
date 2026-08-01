theory List_V611_Raw_R5_Relation
  imports
    "EAL6_FreeRTOS_V611_List_Raw_R3_Master.List_V611_Raw_R3_Master"
    "EAL6_FreeRTOS_V611_Model.XList_Model"
begin

text \<open>
  R5 begins the semantic bridge from the raw byte heap to the independently
  reconstructed pure list model.  The embedded mini-list item is observed
  through its real prefix fields; it is never assumed to be a separately
  allocated full list item.
\<close>

type_synonym raw_node_id = "xLIST_ITEM_C ptr"
type_synonym raw_key = "32 word"

definition raw_end_item :: "xLIST_C ptr \<Rightarrow> raw_node_id" where
  "raw_end_item lp = raw_sentinel_ptr lp"

definition raw_next_at ::
  "heap_mem \<Rightarrow> xLIST_C ptr \<Rightarrow> raw_node_id \<Rightarrow> raw_node_id"
where
  "raw_next_at h lp p =
     (if p = raw_end_item lp then
        xMINI_LIST_ITEM_C.pxNext_C (xListEnd_C (h_val h lp))
      else xLIST_ITEM_C.pxNext_C (h_val h p))"

definition raw_prev_at ::
  "heap_mem \<Rightarrow> xLIST_C ptr \<Rightarrow> raw_node_id \<Rightarrow> raw_node_id"
where
  "raw_prev_at h lp p =
     (if p = raw_end_item lp then
        xMINI_LIST_ITEM_C.pxPrevious_C (xListEnd_C (h_val h lp))
      else xLIST_ITEM_C.pxPrevious_C (h_val h p))"

definition raw_key_at :: "heap_mem \<Rightarrow> raw_node_id \<Rightarrow> raw_key" where
  "raw_key_at h p = xLIST_ITEM_C.xItemValue_C (h_val h p)"

definition raw_cursor_at ::
  "heap_mem \<Rightarrow> xLIST_C ptr \<Rightarrow> raw_node_id option"
where
  "raw_cursor_at h lp =
     (let p = pxIndex_C (h_val h lp)
      in if p = raw_end_item lp then None else Some p)"

definition raw_edge_pairs ::
  "xLIST_C ptr \<Rightarrow> raw_node_id list \<Rightarrow>
   (raw_node_id \<times> raw_node_id) list"
where
  "raw_edge_pairs lp rs =
     zip (raw_end_item lp # rs) (rs @ [raw_end_item lp])"

definition raw_ring_links ::
  "heap_mem \<Rightarrow> xLIST_C ptr \<Rightarrow> raw_node_id list \<Rightarrow> bool"
where
  "raw_ring_links h lp rs \<longleftrightarrow>
     list_all
       (\<lambda>(p,q). raw_next_at h lp p = q \<and> raw_prev_at h lp q = p)
       (raw_edge_pairs lp rs)"

definition raw_list_region :: "xLIST_C ptr \<Rightarrow> addr set" where
  "raw_list_region lp = {ptr_val lp..+size_of TYPE(xLIST_C)}"

definition raw_item_region :: "raw_node_id \<Rightarrow> addr set" where
  "raw_item_region p = {ptr_val p..+size_of TYPE(xLIST_ITEM_C)}"

definition raw_xlist_layout ::
  "xLIST_C ptr \<Rightarrow> raw_node_id list \<Rightarrow> bool"
where
  "raw_xlist_layout lp rs \<longleftrightarrow>
     c_guard lp \<and>
     c_guard (raw_end_item lp) \<and>
     raw_end_item lp \<notin> set rs \<and>
     (\<forall>p \<in> set rs.
        c_guard p \<and> raw_item_region p \<inter> raw_list_region lp = {}) \<and>
     (\<forall>p \<in> set rs. \<forall>q \<in> set rs.
        p \<noteq> q \<longrightarrow> raw_item_region p \<inter> raw_item_region q = {})"

definition raw_xlist_view ::
  "heap_mem \<Rightarrow> xLIST_C ptr \<Rightarrow>
   (raw_node_id, raw_key) xlist_abs \<Rightarrow> bool"
where
  "raw_xlist_view h lp xs \<longleftrightarrow>
     xlist_wf xs \<and>
     unat (uxNumberOfItems_C (h_val h lp)) = length (ring xs) \<and>
     cursor xs = raw_cursor_at h lp \<and>
     raw_ring_links h lp (ring xs) \<and>
     (\<forall>p \<in> set (ring xs).
        item_key xs p = raw_key_at h p \<and>
        pvContainer_C (h_val h p) = PTR_COERCE(xLIST_C \<rightarrow> unit) lp)"

definition raw_xlist_rel ::
  "heap_mem \<Rightarrow> xLIST_C ptr \<Rightarrow>
   (raw_node_id, raw_key) xlist_abs \<Rightarrow> bool"
where
  "raw_xlist_rel h lp xs \<longleftrightarrow>
     raw_xlist_layout lp (ring xs) \<and> raw_xlist_view h lp xs"

definition raw_empty_abs ::
  "(raw_node_id \<Rightarrow> raw_key) \<Rightarrow> (raw_node_id, raw_key) xlist_abs"
where
  "raw_empty_abs keys =
     \<lparr>ring = [], cursor = None, item_key = keys\<rparr>"

definition raw_singleton_abs ::
  "raw_node_id \<Rightarrow> (raw_node_id \<Rightarrow> raw_key) \<Rightarrow> raw_key
   \<Rightarrow> (raw_node_id, raw_key) xlist_abs"
where
  "raw_singleton_abs p keys k =
     list_insert_end_abs p k (raw_empty_abs keys)"

lemma raw_singleton_abs_fields[simp]:
  "ring (raw_singleton_abs p keys k) = [p] \<and>
   cursor (raw_singleton_abs p keys k) = Some p \<and>
   item_key (raw_singleton_abs p keys k) p = k"
  by (simp add: raw_singleton_abs_def raw_empty_abs_def
      list_insert_end_abs_def)

lemma raw_fixed_empty_layout:
  "raw_xlist_layout raw_list_ptr []"
  using raw_sentinel_ptr_guard
  by (simp add: raw_xlist_layout_def raw_end_item_def)

lemma raw_fixed_singleton_layout:
  "raw_xlist_layout raw_list_ptr [raw_item_ptr]"
proof -
  have disjoint:
    "raw_item_region raw_item_ptr \<inter> raw_list_region raw_list_ptr = {}"
    using raw_list_item_intervals_disjoint
    by (simp add: raw_item_region_def raw_list_region_def raw_item_ptr_def
        raw_list_ptr_def size_of_def)
  have distinct: "raw_sentinel_ptr raw_list_ptr \<noteq> raw_item_ptr"
    by (simp add: raw_item_ptr_def)
  show ?thesis
    using disjoint distinct raw_list_ptr_guard raw_item_ptr_guard
      raw_sentinel_ptr_guard
    by (simp add: raw_xlist_layout_def raw_end_item_def)
qed

lemma raw_xlist_rel_emptyI:
  assumes layout: "raw_xlist_layout lp []"
    and count: "uxNumberOfItems_C (h_val h lp) = 0"
    and index: "pxIndex_C (h_val h lp) = raw_end_item lp"
    and end_next: "xMINI_LIST_ITEM_C.pxNext_C (xListEnd_C (h_val h lp)) =
      raw_end_item lp"
    and end_previous: "xMINI_LIST_ITEM_C.pxPrevious_C (xListEnd_C (h_val h lp)) =
      raw_end_item lp"
  shows "raw_xlist_rel h lp (raw_empty_abs keys)"
  using assms
  by (simp add: raw_xlist_rel_def raw_xlist_view_def raw_empty_abs_def
      xlist_wf_def raw_cursor_at_def raw_ring_links_def raw_edge_pairs_def
      raw_next_at_def raw_prev_at_def)

lemma raw_xlist_rel_singletonI:
  assumes layout: "raw_xlist_layout lp [p]"
    and count: "uxNumberOfItems_C (h_val h lp) = 1"
    and index: "pxIndex_C (h_val h lp) = p"
    and end_next: "xMINI_LIST_ITEM_C.pxNext_C (xListEnd_C (h_val h lp)) = p"
    and end_previous:
      "xMINI_LIST_ITEM_C.pxPrevious_C (xListEnd_C (h_val h lp)) = p"
    and item_next: "xLIST_ITEM_C.pxNext_C (h_val h p) = raw_end_item lp"
    and item_previous:
      "xLIST_ITEM_C.pxPrevious_C (h_val h p) = raw_end_item lp"
    and key: "xLIST_ITEM_C.xItemValue_C (h_val h p) = k"
    and container:
      "pvContainer_C (h_val h p) = PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
  shows "raw_xlist_rel h lp (raw_singleton_abs p keys k)"
proof -
  have ne: "p \<noteq> raw_end_item lp"
    using layout by (auto simp: raw_xlist_layout_def)
  show ?thesis
    using assms ne
    by (simp add: raw_xlist_rel_def raw_xlist_view_def
        raw_singleton_abs_def raw_empty_abs_def list_insert_end_abs_def
        xlist_wf_def raw_cursor_at_def raw_ring_links_def raw_edge_pairs_def
        raw_next_at_def raw_prev_at_def raw_key_at_def)
qed

lemma raw_insert_end_prestate_rep_empty:
  "raw_xlist_rel
     (hrs_mem (t_hrs_' (raw_insert_end_prestate base d h k owner)))
     raw_list_ptr (raw_empty_abs keys)"
proof (rule raw_xlist_rel_emptyI)
  show "raw_xlist_layout raw_list_ptr []"
    by (rule raw_fixed_empty_layout)
next
  show "uxNumberOfItems_C
      (h_val
        (hrs_mem (t_hrs_' (raw_insert_end_prestate base d h k owner)))
        raw_list_ptr) = 0"
    using raw_insert_end_prestate_fields[
      where base=base and d=d and h=h and k=k and owner=owner]
    by simp
next
  show "pxIndex_C
      (h_val
        (hrs_mem (t_hrs_' (raw_insert_end_prestate base d h k owner)))
        raw_list_ptr) = raw_end_item raw_list_ptr"
    using raw_insert_end_prestate_fields[
      where base=base and d=d and h=h and k=k and owner=owner]
    by (simp add: raw_end_item_def)
next
  show "xMINI_LIST_ITEM_C.pxNext_C
      (xListEnd_C
        (h_val
          (hrs_mem (t_hrs_' (raw_insert_end_prestate base d h k owner)))
          raw_list_ptr)) = raw_end_item raw_list_ptr"
    using raw_insert_end_prestate_fields[
      where base=base and d=d and h=h and k=k and owner=owner]
    by (simp add: raw_end_item_def)
next
  show "xMINI_LIST_ITEM_C.pxPrevious_C
      (xListEnd_C
        (h_val
          (hrs_mem (t_hrs_' (raw_insert_end_prestate base d h k owner)))
          raw_list_ptr)) = raw_end_item raw_list_ptr"
    using raw_insert_end_prestate_fields[
      where base=base and d=d and h=h and k=k and owner=owner]
    by (simp add: raw_end_item_def)
qed

theorem raw_vListInsertEnd_empty_relation_post:
  "vListInsertEnd' raw_list_ptr raw_item_ptr \<bullet>
     (raw_insert_end_prestate base d h k owner)
   \<lbrace>\<lambda>r t.
      r = Result () \<and>
      raw_xlist_rel (hrs_mem (t_hrs_' t)) raw_list_ptr
        (raw_singleton_abs raw_item_ptr keys k)
    \<rbrace>"
proof -
  note master = raw_vListInsertEnd_empty_master[
    where base=base and d=d and h=h and k=k and owner=owner]
  show ?thesis
  apply (rule runs_to_weaken[OF master])
  apply clarsimp
  apply (rule raw_xlist_rel_singletonI)
  apply (rule raw_fixed_singleton_layout)
  apply (simp_all add: raw_end_item_def)
  done
qed

theorem raw_vListInsertEnd_empty_refines:
  "vListInsertEnd' raw_list_ptr raw_item_ptr \<bullet>
     (raw_insert_end_prestate base d h k owner)
   \<lbrace>\<lambda>r t.
      r = Result () \<and>
      raw_xlist_rel (hrs_mem (t_hrs_' t)) raw_list_ptr
        (list_insert_end_abs raw_item_ptr k (raw_empty_abs keys))
    \<rbrace>"
  using raw_vListInsertEnd_empty_relation_post[
    where base=base and d=d and h=h and k=k and owner=owner and keys=keys]
  by (simp only: raw_singleton_abs_def)

end
