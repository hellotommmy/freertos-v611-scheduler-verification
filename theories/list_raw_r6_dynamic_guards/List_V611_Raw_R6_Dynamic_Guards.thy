theory List_V611_Raw_R6_Dynamic_Guards
  imports "EAL6_FreeRTOS_V611_List_Raw_R6_Generic_Prefix.List_V611_Raw_R6_Generic_Prefix"
begin

text \<open>
  Dynamic pointer-guard interface for general-N list operations.  The facts
  are derived from raw_xlist_rel and the arbitrary-cycle layer; no generated
  C body is opened here.  They replace the fixed 0x1000/0x2000 guard witnesses
  at the entrance to the next source VCG.
\<close>

lemma raw_xlist_rel_cycle_node_guard:
  assumes rel: "raw_xlist_rel h lp xs"
    and member:
      "u \<in> insert (raw_end_item lp) (set (ring xs))"
  shows "c_guard u"
  using rel member
  by (auto simp: raw_xlist_rel_def raw_xlist_layout_def)

lemma raw_xlist_rel_index_in_cycle:
  assumes rel: "raw_xlist_rel h lp xs"
  shows
    "pxIndex_C (h_val h lp) \<in>
       insert (raw_end_item lp) (set (ring xs))"
proof -
  have wf: "xlist_wf xs"
    using rel
    by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have cursor:
    "cursor xs = raw_cursor_at h lp"
    using rel by (rule raw_xlist_rel_cursorD)
  show ?thesis
  proof (cases "pxIndex_C (h_val h lp) = raw_end_item lp")
    case True
    then show ?thesis by simp
  next
    case False
    have cursor_at_index:
      "cursor xs = Some (pxIndex_C (h_val h lp))"
      using cursor False by (simp add: raw_cursor_at_def)
    have "pxIndex_C (h_val h lp) \<in> set (ring xs)"
      using wf cursor_at_index by (auto simp: xlist_wf_def)
    then show ?thesis by simp
  qed
qed

lemma raw_ring_links_next_closed:
  assumes links: "raw_ring_links h lp rs"
    and member: "u \<in> insert (raw_end_item lp) (set rs)"
  shows "raw_next_at h lp u \<in> insert (raw_end_item lp) (set rs)"
proof -
  have source:
    "u \<in> set (map fst (raw_edge_pairs lp rs))"
    using member by simp
  have source_image:
    "u \<in> fst ` set (raw_edge_pairs lp rs)"
    using source by (simp only: set_map)
  then obtain uv where uv_member:
      "uv \<in> set (raw_edge_pairs lp rs)" and
      uv_source: "fst uv = u"
    by blast
  obtain a v where uv: "uv = (a, v)"
    by (cases uv) simp
  have pair: "(u, v) \<in> set (raw_edge_pairs lp rs)"
    using uv_member uv_source uv by simp
  have edge: "raw_next_at h lp u = v"
    using links pair
    by (auto simp: raw_ring_links_def list_all_iff)
  have target_image:
    "v \<in> snd ` set (raw_edge_pairs lp rs)"
  proof -
    have "snd (u, v) \<in> snd ` set (raw_edge_pairs lp rs)"
      by (rule imageI[OF pair])
    then show ?thesis by simp
  qed
  have target:
    "v \<in> set (map snd (raw_edge_pairs lp rs))"
    using target_image by (simp only: set_map)
  show ?thesis
    using edge target by simp
qed

lemma raw_ring_links_prev_closed:
  assumes links: "raw_ring_links h lp rs"
    and member: "u \<in> insert (raw_end_item lp) (set rs)"
  shows "raw_prev_at h lp u \<in> insert (raw_end_item lp) (set rs)"
proof -
  have target:
    "u \<in> set (map snd (raw_edge_pairs lp rs))"
    using member by simp
  have target_image:
    "u \<in> snd ` set (raw_edge_pairs lp rs)"
    using target by (simp only: set_map)
  then obtain vu where vu_member:
      "vu \<in> set (raw_edge_pairs lp rs)" and
      vu_target: "snd vu = u"
    by blast
  obtain v b where vu: "vu = (v, b)"
    by (cases vu) simp
  have pair: "(v, u) \<in> set (raw_edge_pairs lp rs)"
    using vu_member vu_target vu by simp
  have edge: "raw_prev_at h lp u = v"
    using links pair
    by (auto simp: raw_ring_links_def list_all_iff)
  have source_image:
    "v \<in> fst ` set (raw_edge_pairs lp rs)"
  proof -
    have "fst (v, u) \<in> fst ` set (raw_edge_pairs lp rs)"
      by (rule imageI[OF pair])
    then show ?thesis by simp
  qed
  have source:
    "v \<in> set (map fst (raw_edge_pairs lp rs))"
    using source_image by (simp only: set_map)
  show ?thesis
    using edge source by simp
qed

lemma raw_full_next_is_sentinel_safe:
  "xLIST_ITEM_C.pxNext_C (h_val h u) = raw_next_at h lp u"
proof (cases "u = raw_end_item lp")
  case True
  then show ?thesis
    using raw_sentinel_next_prefix_generic[where h=h and lp=lp]
    by (simp add: raw_next_at_def raw_end_item_def)
next
  case False
  then show ?thesis by (simp add: raw_next_at_def)
qed

lemma raw_full_previous_is_sentinel_safe:
  "xLIST_ITEM_C.pxPrevious_C (h_val h u) = raw_prev_at h lp u"
proof (cases "u = raw_end_item lp")
  case True
  then show ?thesis
    using raw_sentinel_previous_prefix_generic[where h=h and lp=lp]
    by (simp add: raw_prev_at_def raw_end_item_def)
next
  case False
  then show ?thesis by (simp add: raw_prev_at_def)
qed

theorem raw_vListInsertEnd_dynamic_guards:
  assumes rel: "raw_xlist_rel h lp xs"
    and fresh: "raw_fresh_for_insert lp (ring xs) p"
  shows
    "c_guard lp \<and>
     c_guard p \<and>
     c_guard (pxIndex_C (h_val h lp)) \<and>
     c_guard
       (xLIST_ITEM_C.pxNext_C
         (h_val h (pxIndex_C (h_val h lp))))"
proof -
  let ?i = "pxIndex_C (h_val h lp)"
  have lp_guard: "c_guard lp"
    using rel
    by (simp add: raw_xlist_rel_def raw_xlist_layout_def)
  have p_guard: "c_guard p"
    using fresh by (simp add: raw_fresh_for_insert_def)
  have index_member:
    "?i \<in> insert (raw_end_item lp) (set (ring xs))"
    by (rule raw_xlist_rel_index_in_cycle[OF rel])
  have index_guard: "c_guard ?i"
    by (rule raw_xlist_rel_cycle_node_guard[OF rel index_member])
  have links: "raw_ring_links h lp (ring xs)"
    using rel
    by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have next_member:
    "raw_next_at h lp ?i \<in>
       insert (raw_end_item lp) (set (ring xs))"
    by (rule raw_ring_links_next_closed[OF links index_member])
  have next_guard: "c_guard (raw_next_at h lp ?i)"
    by (rule raw_xlist_rel_cycle_node_guard[OF rel next_member])
  have next_eq:
    "xLIST_ITEM_C.pxNext_C (h_val h ?i) = raw_next_at h lp ?i"
    by (rule raw_full_next_is_sentinel_safe)
  show ?thesis
    using lp_guard p_guard index_guard next_guard next_eq by simp
qed

theorem raw_vListRemove_dynamic_guards:
  assumes rel: "raw_xlist_rel h lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "c_guard p \<and>
     c_guard (xLIST_ITEM_C.pxNext_C (h_val h p)) \<and>
     c_guard (xLIST_ITEM_C.pxPrevious_C (h_val h p)) \<and>
     c_guard
       (PTR_COERCE(unit \<rightarrow> xLIST_C)
         (pvContainer_C (h_val h p)))"
proof -
  have cycle_member:
    "p \<in> insert (raw_end_item lp) (set (ring xs))"
    using member by simp
  have p_guard: "c_guard p"
    by (rule raw_xlist_rel_cycle_node_guard[OF rel cycle_member])
  have links: "raw_ring_links h lp (ring xs)"
    using rel
    by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have next_member:
    "raw_next_at h lp p \<in>
       insert (raw_end_item lp) (set (ring xs))"
    by (rule raw_ring_links_next_closed[OF links cycle_member])
  have prev_member:
    "raw_prev_at h lp p \<in>
       insert (raw_end_item lp) (set (ring xs))"
    by (rule raw_ring_links_prev_closed[OF links cycle_member])
  have next_guard: "c_guard (raw_next_at h lp p)"
    by (rule raw_xlist_rel_cycle_node_guard[OF rel next_member])
  have prev_guard: "c_guard (raw_prev_at h lp p)"
    by (rule raw_xlist_rel_cycle_node_guard[OF rel prev_member])
  have next_eq:
    "xLIST_ITEM_C.pxNext_C (h_val h p) = raw_next_at h lp p"
    by (rule raw_full_next_is_sentinel_safe)
  have prev_eq:
    "xLIST_ITEM_C.pxPrevious_C (h_val h p) = raw_prev_at h lp p"
    by (rule raw_full_previous_is_sentinel_safe)
  have container:
    "pvContainer_C (h_val h p) =
       PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
    using raw_xlist_rel_live_itemD[OF rel member] by blast
  have lp_guard: "c_guard lp"
    using rel
    by (simp add: raw_xlist_rel_def raw_xlist_layout_def)
  show ?thesis
    using p_guard next_guard prev_guard next_eq prev_eq container lp_guard
    by simp
qed

end
