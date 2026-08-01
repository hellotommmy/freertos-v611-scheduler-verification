theory List_V611_Raw_R5_Interface
  imports "EAL6_FreeRTOS_V611_List_Raw_R5_Relation.List_V611_Raw_R5_Relation"
begin

text \<open>
  R5 interface bricks.  These expose only the observable part of the abstract
  record, make the detached-input obligation explicit, and establish the
  finite-cycle facts needed before attempting a general-N raw VCG.
\<close>

definition raw_live_xlist_eq ::
  "(raw_node_id, raw_key) xlist_abs \<Rightarrow>
   (raw_node_id, raw_key) xlist_abs \<Rightarrow> bool"
where
  "raw_live_xlist_eq xs ys \<longleftrightarrow>
     ring xs = ring ys \<and>
     cursor xs = cursor ys \<and>
     (\<forall>p \<in> set (ring xs). item_key xs p = item_key ys p)"

lemma raw_live_xlist_eq_refl[simp]: "raw_live_xlist_eq xs xs"
  by (simp add: raw_live_xlist_eq_def)

lemma raw_live_xlist_eq_sym:
  "raw_live_xlist_eq xs ys \<Longrightarrow> raw_live_xlist_eq ys xs"
  by (auto simp: raw_live_xlist_eq_def)

lemma raw_live_xlist_eq_trans:
  "raw_live_xlist_eq xs ys \<Longrightarrow> raw_live_xlist_eq ys zs
   \<Longrightarrow> raw_live_xlist_eq xs zs"
  by (auto simp: raw_live_xlist_eq_def)

lemma raw_empty_abs_live_eq[simp]:
  "raw_live_xlist_eq (raw_empty_abs keys) (raw_empty_abs keys')"
  by (simp add: raw_live_xlist_eq_def raw_empty_abs_def)

definition raw_detached_item ::
  "heap_mem \<Rightarrow> xLIST_C ptr \<Rightarrow> raw_node_id \<Rightarrow>
   raw_key \<Rightarrow> unit ptr \<Rightarrow> bool"
where
  "raw_detached_item h lp p k owner \<longleftrightarrow>
     c_guard p \<and>
     p \<noteq> raw_end_item lp \<and>
     raw_item_region p \<inter> raw_list_region lp = {} \<and>
     raw_key_at h p = k \<and>
     pvOwner_C (h_val h p) = owner \<and>
     pvContainer_C (h_val h p) = NULL"

lemma raw_fixed_item_list_regions_disjoint:
  "raw_item_region raw_item_ptr \<inter> raw_list_region raw_list_ptr = {}"
  using raw_list_item_intervals_disjoint
  by (simp add: raw_item_region_def raw_list_region_def raw_item_ptr_def
      raw_list_ptr_def size_of_def)

lemma raw_insert_end_prestate_detached:
  "raw_detached_item
     (hrs_mem (t_hrs_' (raw_insert_end_prestate base d h k owner)))
     raw_list_ptr raw_item_ptr k owner"
proof -
  note fields = raw_insert_end_prestate_fields[
    where base=base and d=d and h=h and k=k and owner=owner]
  have ne: "raw_item_ptr \<noteq> raw_end_item raw_list_ptr"
    by (simp add: raw_end_item_def raw_item_ptr_def)
  show ?thesis
    using fields ne raw_item_ptr_guard raw_fixed_item_list_regions_disjoint
    by (simp add: raw_detached_item_def raw_key_at_def)
qed

lemma raw_xlist_rel_distinct_cycle_nodes:
  assumes "raw_xlist_rel h lp xs"
  shows "distinct (raw_end_item lp # ring xs)"
  using assms
  by (auto simp: raw_xlist_rel_def raw_xlist_view_def raw_xlist_layout_def
      xlist_wf_def)

lemma raw_edge_pairs_length[simp]:
  "length (raw_edge_pairs lp rs) = Suc (length rs)"
  by (simp add: raw_edge_pairs_def)

lemma raw_edge_pairs_sources[simp]:
  "map fst (raw_edge_pairs lp rs) = raw_end_item lp # rs"
  by (simp add: raw_edge_pairs_def)

lemma raw_edge_pairs_targets[simp]:
  "map snd (raw_edge_pairs lp rs) = rs @ [raw_end_item lp]"
  by (simp add: raw_edge_pairs_def)

lemma raw_ring_links_empty_iff:
  "raw_ring_links h lp [] \<longleftrightarrow>
     xMINI_LIST_ITEM_C.pxNext_C (xListEnd_C (h_val h lp)) =
       raw_end_item lp \<and>
     xMINI_LIST_ITEM_C.pxPrevious_C (xListEnd_C (h_val h lp)) =
       raw_end_item lp"
  by (simp add: raw_ring_links_def raw_edge_pairs_def raw_next_at_def
      raw_prev_at_def)

lemma raw_ring_links_singleton_iff:
  assumes "p \<noteq> raw_end_item lp"
  shows "raw_ring_links h lp [p] \<longleftrightarrow>
     xMINI_LIST_ITEM_C.pxNext_C (xListEnd_C (h_val h lp)) = p \<and>
     xLIST_ITEM_C.pxPrevious_C (h_val h p) = raw_end_item lp \<and>
     xLIST_ITEM_C.pxNext_C (h_val h p) = raw_end_item lp \<and>
     xMINI_LIST_ITEM_C.pxPrevious_C (xListEnd_C (h_val h lp)) = p"
  using assms
  by (simp add: raw_ring_links_def raw_edge_pairs_def raw_next_at_def
      raw_prev_at_def)

lemma raw_xlist_rel_countD:
  "raw_xlist_rel h lp xs \<Longrightarrow>
   unat (uxNumberOfItems_C (h_val h lp)) = length (ring xs)"
  by (simp add: raw_xlist_rel_def raw_xlist_view_def)

lemma raw_xlist_rel_cursorD:
  "raw_xlist_rel h lp xs \<Longrightarrow> cursor xs = raw_cursor_at h lp"
  by (simp add: raw_xlist_rel_def raw_xlist_view_def)

lemma raw_xlist_rel_live_itemD:
  assumes rel: "raw_xlist_rel h lp xs" and member: "p \<in> set (ring xs)"
  shows "item_key xs p = raw_key_at h p \<and>
    pvContainer_C (h_val h p) = PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
  using assms by (auto simp: raw_xlist_rel_def raw_xlist_view_def)

definition raw_fresh_for_insert ::
  "xLIST_C ptr \<Rightarrow> raw_node_id list \<Rightarrow> raw_node_id \<Rightarrow> bool"
where
  "raw_fresh_for_insert lp rs p \<longleftrightarrow>
     c_guard p \<and>
     p \<noteq> raw_end_item lp \<and>
     p \<notin> set rs \<and>
     raw_item_region p \<inter> raw_list_region lp = {} \<and>
     (\<forall>q \<in> set rs. raw_item_region p \<inter> raw_item_region q = {})"

definition raw_count_can_increment ::
  "(raw_node_id, raw_key) xlist_abs \<Rightarrow> bool"
where
  "raw_count_can_increment xs \<longleftrightarrow>
     length (ring xs) < unat (max_word :: 32 word)"

lemma raw_xlist_layout_extend_set:
  assumes layout: "raw_xlist_layout lp rs"
    and fresh: "raw_fresh_for_insert lp rs p"
    and set_rs': "set rs' = insert p (set rs)"
  shows "raw_xlist_layout lp rs'"
  using assms
  by (auto simp: raw_xlist_layout_def raw_fresh_for_insert_def Int_commute)

end
