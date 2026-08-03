theory Scheduler_Family_Insert_End_Storage_Frame
  imports
    "EAL6_FreeRTOS_V611_Scheduler_List_Family_Frame_Capstone.Scheduler_List_Family_Frame_Capstone"
begin

lemma insert_family_h_val_region_cong:
  fixes p :: "'a::mem_type ptr"
  assumes frame: "\<And>a. a \<in> {ptr_val p..+size_of TYPE('a)} \<Longrightarrow>
      h' a = h a"
  shows "h_val h' p = h_val h p"
proof -
  have lists:
    "heap_list h' (size_of TYPE('a)) (ptr_val p) =
     heap_list h (size_of TYPE('a)) (ptr_val p)"
    by (rule heap_list_h_eq2; rule frame)
  show ?thesis using lists by (simp add: h_val_def)
qed

lemma insert_family_storage_root_h_val_cong:
  assumes frame: "\<And>a. a \<in> raw_xlist_storage lp xs \<Longrightarrow>
      h' a = h a"
  shows "h_val h' lp = h_val h lp"
  apply (rule insert_family_h_val_region_cong)
  apply (rule frame)
  by (simp add: raw_xlist_storage_def raw_list_region_def)

lemma insert_family_storage_item_h_val_cong:
  assumes frame: "\<And>a. a \<in> raw_xlist_storage lp xs \<Longrightarrow>
      h' a = h a"
    and member: "p \<in> set (ring xs)"
  shows "h_val h' p = h_val h p"
  apply (rule insert_family_h_val_region_cong)
  apply (rule frame)
  using member by (auto simp: raw_xlist_storage_def raw_item_region_def)

lemma insert_family_raw_next_at_cong:
  assumes root_same: "h_val h' lp = h_val h lp"
    and item_same:
      "\<And>p. p \<in> set rs \<Longrightarrow> h_val h' p = h_val h p"
    and cycle: "p \<in> insert (raw_end_item lp) (set rs)"
  shows "raw_next_at h' lp p = raw_next_at h lp p"
  using cycle root_same item_same
  by (auto simp: raw_next_at_def)

lemma insert_family_raw_prev_at_cong:
  assumes root_same: "h_val h' lp = h_val h lp"
    and item_same:
      "\<And>p. p \<in> set rs \<Longrightarrow> h_val h' p = h_val h p"
    and cycle: "p \<in> insert (raw_end_item lp) (set rs)"
  shows "raw_prev_at h' lp p = raw_prev_at h lp p"
  using cycle root_same item_same
  by (auto simp: raw_prev_at_def)

lemma insert_family_raw_edge_pair_in_cycle:
  assumes edge: "(p,q) \<in> set (raw_edge_pairs lp rs)"
  shows
    "p \<in> insert (raw_end_item lp) (set rs) \<and>
     q \<in> insert (raw_end_item lp) (set rs)"
proof -
  have left: "p \<in> set (raw_end_item lp # rs)"
    by (rule in_set_zip1; use edge in
        \<open>simp add: raw_edge_pairs_def\<close>)
  have right: "q \<in> set (rs @ [raw_end_item lp])"
    by (rule in_set_zip2; use edge in
        \<open>simp add: raw_edge_pairs_def\<close>)
  show ?thesis using left right by auto
qed

lemma insert_family_raw_ring_links_h_val_cong:
  assumes links: "raw_ring_links h lp rs"
    and root_same: "h_val h' lp = h_val h lp"
    and item_same:
      "\<And>p. p \<in> set rs \<Longrightarrow> h_val h' p = h_val h p"
  shows "raw_ring_links h' lp rs"
proof -
  have old:
    "\<And>p q. (p,q) \<in> set (raw_edge_pairs lp rs) \<Longrightarrow>
       raw_next_at h lp p = q \<and> raw_prev_at h lp q = p"
    using links by (auto simp: raw_ring_links_def list_all_iff)
  show ?thesis
    unfolding raw_ring_links_def list_all_iff
  proof (intro ballI)
    fix edge
    assume edge_mem: "edge \<in> set (raw_edge_pairs lp rs)"
    obtain p q where edge_eq: "edge = (p,q)" by (cases edge)
    have cycle:
      "p \<in> insert (raw_end_item lp) (set rs) \<and>
       q \<in> insert (raw_end_item lp) (set rs)"
      using insert_family_raw_edge_pair_in_cycle[of p q lp rs]
        edge_mem edge_eq by simp
    have next_same:
      "raw_next_at h' lp p = raw_next_at h lp p"
      by (rule insert_family_raw_next_at_cong[OF root_same item_same];
          use cycle in blast)
    have previous:
      "raw_prev_at h' lp q = raw_prev_at h lp q"
      by (rule insert_family_raw_prev_at_cong[OF root_same item_same];
          use cycle in blast)
    show "case edge of (p,q) \<Rightarrow>
        raw_next_at h' lp p = q \<and> raw_prev_at h' lp q = p"
      using old[of p q] edge_mem edge_eq next_same previous by simp
  qed
qed

theorem insert_family_raw_xlist_rel_h_val_cong:
  assumes rel: "raw_xlist_rel h lp xs"
    and root_same: "h_val h' lp = h_val h lp"
    and item_same:
      "\<And>p. p \<in> set (ring xs) \<Longrightarrow> h_val h' p = h_val h p"
  shows "raw_xlist_rel h' lp xs"
proof -
  have links:
    "raw_ring_links h' lp (ring xs)"
    by (rule insert_family_raw_ring_links_h_val_cong[
          OF _ root_same item_same])
       (use rel in
        \<open>simp add: raw_xlist_rel_def raw_xlist_view_def\<close>)
  show ?thesis
    using rel root_same item_same links
    by (auto simp: raw_xlist_rel_def raw_xlist_view_def
        raw_cursor_at_def raw_key_at_def)
qed

theorem insert_family_raw_xlist_rel_storage_frame:
  assumes rel: "raw_xlist_rel h lp xs"
    and frame: "\<And>a. a \<in> raw_xlist_storage lp xs \<Longrightarrow>
      h' a = h a"
  shows "raw_xlist_rel h' lp xs"
proof (rule insert_family_raw_xlist_rel_h_val_cong[OF rel])
  show "h_val h' lp = h_val h lp"
    by (rule insert_family_storage_root_h_val_cong[OF frame])
next
  fix p
  assume member: "p \<in> set (ring xs)"
  show "h_val h' p = h_val h p"
    by (rule insert_family_storage_item_h_val_cong[OF frame member])
qed

end
