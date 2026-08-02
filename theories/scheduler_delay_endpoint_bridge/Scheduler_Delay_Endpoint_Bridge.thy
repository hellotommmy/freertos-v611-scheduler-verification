theory Scheduler_Delay_Endpoint_Bridge
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Remove_Unlinked_Ownership.Scheduler_Remove_Unlinked_Ownership"
    "EAL6_FreeRTOS_V611_Scheduler_Universal_Delay_Phases.Scheduler_Universal_Delay_Phases"
begin

text \<open>
  Root-aware bridge from raw list sentinels and items to the delay phase
  endpoint type.  All roots, rings, keys, item positions, and addresses remain
  quantified.  Slot witnesses are computed from the represented ring; they
  are never premises.
\<close>

definition raw_delay_endpoint ::
  "xLIST_C ptr \<Rightarrow> raw_node_id \<Rightarrow>
   (raw_node_id, xLIST_C ptr) delay_link_endpoint"
where
  "raw_delay_endpoint lp p =
     (if p = raw_end_item lp then DelayEnd lp else DelayNode p)"

lemma raw_delay_endpoint_end [simp]:
  "raw_delay_endpoint lp (raw_end_item lp) = DelayEnd lp"
  by (simp add: raw_delay_endpoint_def)

lemma raw_delay_endpoint_item [simp]:
  assumes item: "p \<noteq> raw_end_item lp"
  shows "raw_delay_endpoint lp p = DelayNode p"
  using item by (simp add: raw_delay_endpoint_def)

theorem raw_distinct_sentinels_map_to_distinct_delay_ends:
  assumes roots: "lp \<noteq> lq"
  shows
    "raw_delay_endpoint lp (raw_end_item lp) \<noteq>
       raw_delay_endpoint lq (raw_end_item lq)"
  using roots by simp

lemma raw_delay_endpoint_last:
  assumes end_absent: "raw_end_item lp \<notin> set before"
  shows
    "raw_delay_endpoint lp (last (raw_end_item lp # before)) =
       (case rev before of
          [] \<Rightarrow> DelayEnd lp
        | x # _ \<Rightarrow> DelayNode x)"
proof (cases "rev before")
  case Nil
  then have "before = []" by simp
  then show ?thesis by simp
next
  case (Cons x xs)
  have before_eq: "before = rev xs @ [x]"
    using Cons by (metis rev.simps(2) rev_rev_ident)
  have x_ne: "x \<noteq> raw_end_item lp"
  proof
    assume equal: "x = raw_end_item lp"
    have "raw_end_item lp \<in> set before"
      using before_eq equal by simp
    with end_absent show False by simp
  qed
  show ?thesis
    using x_ne before_eq Cons by simp
qed

lemma raw_delay_endpoint_hd:
  assumes end_absent: "raw_end_item lp \<notin> set after"
  shows
    "raw_delay_endpoint lp (hd (after @ [raw_end_item lp])) =
       (case after of
          [] \<Rightarrow> DelayEnd lp
        | x # _ \<Rightarrow> DelayNode x)"
proof (cases after)
  case Nil
  show ?thesis using Nil by simp
next
  case (Cons x xs)
  have x_ne: "x \<noteq> raw_end_item lp"
  proof
    assume equal: "x = raw_end_item lp"
    have "raw_end_item lp \<in> set after"
      using Cons equal by simp
    with end_absent show False by simp
  qed
  show ?thesis
    using x_ne Cons by simp
qed

theorem raw_remove_slot_to_delay_existing_ring_slot:
  assumes rel: "raw_xlist_rel h lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "\<exists>before after c q.
       ring xs = before @ p # after \<and>
       c = raw_delay_endpoint lp (raw_prev_at h lp p) \<and>
       q = raw_delay_endpoint lp (raw_next_at h lp p) \<and>
       delay_existing_ring_slot lp p xs c q"
proof -
  from member obtain before after where
      split: "ring xs = before @ p # after"
    by (meson split_list)
  let ?end = "raw_end_item lp"
  let ?c0 = "last (?end # before)"
  let ?q0 = "hd (after @ [?end])"
  have end_absent: "?end \<notin> set (ring xs)"
    using rel by (simp add: raw_xlist_rel_def raw_xlist_layout_def)
  have end_before: "?end \<notin> set before"
    and end_after: "?end \<notin> set after"
    using end_absent split by auto
  have links: "raw_ring_links h lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have left_edge:
      "raw_next_at h lp ?c0 = p \<and> raw_prev_at h lp p = ?c0"
    using raw_ring_links_boundary[of h lp before "p # after"] links split
    by simp
  have right_edge:
      "raw_next_at h lp p = ?q0 \<and> raw_prev_at h lp ?q0 = p"
    using raw_ring_links_boundary[of h lp "before @ [p]" after] links split
    by simp
  have c_endpoint:
      "raw_delay_endpoint lp ?c0 =
        (case rev before of
           [] \<Rightarrow> DelayEnd lp
         | x # _ \<Rightarrow> DelayNode x)"
    by (rule raw_delay_endpoint_last[OF end_before])
  have q_endpoint:
      "raw_delay_endpoint lp ?q0 =
        (case after of
           [] \<Rightarrow> DelayEnd lp
         | x # _ \<Rightarrow> DelayNode x)"
    by (rule raw_delay_endpoint_hd[OF end_after])
  have slot:
      "delay_existing_ring_slot lp p xs
        (raw_delay_endpoint lp ?c0) (raw_delay_endpoint lp ?q0)"
    unfolding delay_existing_ring_slot_def
    apply (rule exI[where x=before])
    apply (rule exI[where x=after])
    using split c_endpoint q_endpoint by simp
  show ?thesis
    apply (rule exI[where x=before])
    apply (rule exI[where x=after])
    apply (rule exI[where x="raw_delay_endpoint lp ?c0"])
    apply (rule exI[where x="raw_delay_endpoint lp ?q0"])
    using split left_edge right_edge slot by simp
qed

theorem raw_ordered_scan_to_delay_ordered_scan_slot:
  fixes h :: heap_mem
    and lp :: "xLIST_C ptr"
    and xs :: "(raw_node_id, raw_key) xlist_abs"
    and p :: raw_node_id
    and k :: raw_key
    and before :: "raw_node_id list"
    and c0 q0 :: raw_node_id
  assumes ordered: "raw_ordered_xlist_rel h lp xs"
    and fresh: "raw_fresh_for_insert lp (ring xs) p"
  defines "k \<equiv> raw_key_at h p"
      and "before \<equiv> ordered_scan_prefix (item_key xs) k (ring xs)"
      and "c0 \<equiv> last (raw_end_item lp # before)"
      and "q0 \<equiv> raw_next_at h lp c0"
  shows
    "delay_ordered_scan_slot lp p k xs
       (raw_delay_endpoint lp c0) (raw_delay_endpoint lp q0)"
proof -
  let ?after = "ordered_scan_suffix (item_key xs) k (ring xs)"
  have rel: "raw_xlist_rel h lp xs"
    using ordered by (simp add: raw_ordered_xlist_rel_def)
  have split: "before @ ?after = ring xs"
    unfolding before_def by (rule ordered_scan_prefix_suffix)
  have end_absent: "raw_end_item lp \<notin> set (ring xs)"
    using rel by (simp add: raw_xlist_rel_def raw_xlist_layout_def)
  have end_before: "raw_end_item lp \<notin> set before"
  proof
    assume member: "raw_end_item lp \<in> set before"
    have "raw_end_item lp \<in> set (before @ ?after)"
      using member by simp
    then have "raw_end_item lp \<in> set (ring xs)"
      using split by simp
    with end_absent show False by simp
  qed
  have end_after: "raw_end_item lp \<notin> set ?after"
  proof
    assume member: "raw_end_item lp \<in> set ?after"
    have "raw_end_item lp \<in> set (before @ ?after)"
      using member by simp
    then have "raw_end_item lp \<in> set (ring xs)"
      using split by simp
    with end_absent show False by simp
  qed
  have links: "raw_ring_links h lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have boundary:
      "raw_next_at h lp c0 =
        hd (?after @ [raw_end_item lp])"
    using raw_ring_links_boundary[of h lp before ?after] links split
    unfolding c0_def by simp
  have c_endpoint:
      "raw_delay_endpoint lp c0 =
        (case rev before of
           [] \<Rightarrow> DelayEnd lp
         | x # _ \<Rightarrow> DelayNode x)"
    unfolding c0_def by (rule raw_delay_endpoint_last[OF end_before])
  have q_endpoint:
      "raw_delay_endpoint lp q0 =
        (case ?after of
           [] \<Rightarrow> DelayEnd lp
         | x # _ \<Rightarrow> DelayNode x)"
    unfolding q0_def boundary
    by (rule raw_delay_endpoint_hd[OF end_after])
  have p_absent: "p \<notin> set (ring xs)"
    using fresh by (simp add: raw_fresh_for_insert_def)
  have before_le: "\<forall>x\<in>set before. item_key xs x \<le> k"
    unfolding before_def
  proof (intro ballI)
    fix x
    assume member:
      "x \<in> set (ordered_scan_prefix (item_key xs) k (ring xs))"
    show "item_key xs x \<le> k"
      by (rule ordered_scan_prefix_all_le[OF member])
  qed
  have after_gt:
      "case ?after of [] \<Rightarrow> True | x # _ \<Rightarrow> k < item_key xs x"
  proof (cases ?after)
    case Nil
    show ?thesis using Nil by simp
  next
    case (Cons x rest)
    have "k < item_key xs x"
      by (rule ordered_scan_suffix_head_gt[OF Cons])
    then show ?thesis using Cons by simp
  qed
  show ?thesis
    unfolding delay_ordered_scan_slot_def
    apply (rule conjI)
     apply (rule p_absent)
    apply (rule exI[where x=before])
    apply (rule exI[where x=
        "ordered_scan_suffix (item_key xs) k (ring xs)"])
    using p_absent split before_le after_gt c_endpoint q_endpoint
    by simp
qed

text \<open>
  This is an entry allocation/representation invariant.  Its clauses say,
  respectively: the in-transit item is guarded; it is not any protected
  root's embedded sentinel; its storage is disjoint from every protected list
  object; and its storage is disjoint from every other represented ring item.
  Membership absence and container NULL are intentionally not clauses here.
\<close>

definition raw_family_insert_geometry ::
  "xLIST_C ptr set \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   raw_node_id \<Rightarrow> bool"
where
  "raw_family_insert_geometry roots fam p \<longleftrightarrow>
     c_guard p \<and>
     (\<forall>lp\<in>roots.
        p \<noteq> raw_end_item lp \<and>
        raw_item_region p \<inter> raw_list_region lp = {} \<and>
        (\<forall>q\<in>set (ring (fam lp)).
           q \<noteq> p \<longrightarrow>
           raw_item_region p \<inter> raw_item_region q = {}))"

lemma raw_family_insert_geometry_remove_owner:
  assumes geometry: "raw_family_insert_geometry roots fam p"
  shows
    "raw_family_insert_geometry roots
       (fam(owner := list_remove_abs p (fam owner))) p"
proof -
  have guarded: "c_guard p"
    and per_root:
      "\<forall>lp\<in>roots.
         p \<noteq> raw_end_item lp \<and>
         raw_item_region p \<inter> raw_list_region lp = {} \<and>
         (\<forall>q\<in>set (ring (fam lp)).
            q \<noteq> p \<longrightarrow>
            raw_item_region p \<inter> raw_item_region q = {})"
    using geometry by (simp_all add: raw_family_insert_geometry_def)
  show ?thesis
    unfolding raw_family_insert_geometry_def
  proof (rule conjI)
    show "c_guard p" by (rule guarded)
  next
    show
      "\<forall>lp\<in>roots.
         p \<noteq> raw_end_item lp \<and>
         raw_item_region p \<inter> raw_list_region lp = {} \<and>
         (\<forall>q\<in>set (ring ((fam(owner :=
            list_remove_abs p (fam owner))) lp)).
            q \<noteq> p \<longrightarrow>
            raw_item_region p \<inter> raw_item_region q = {})"
    proof (intro ballI)
      fix lp
      assume lp_root: "lp \<in> roots"
      from per_root lp_root have not_end: "p \<noteq> raw_end_item lp"
        and item_list:
          "raw_item_region p \<inter> raw_list_region lp = {}"
        and item_items:
          "\<forall>q\<in>set (ring (fam lp)).
             q \<noteq> p \<longrightarrow>
             raw_item_region p \<inter> raw_item_region q = {}"
        by blast+
      have post_items:
        "\<forall>q\<in>set (ring ((fam(owner :=
           list_remove_abs p (fam owner))) lp)).
           q \<noteq> p \<longrightarrow>
           raw_item_region p \<inter> raw_item_region q = {}"
      proof (intro ballI impI)
        fix q
        assume q_post:
            "q \<in> set (ring ((fam(owner :=
               list_remove_abs p (fam owner))) lp))"
          and q_ne: "q \<noteq> p"
        have q_old: "q \<in> set (ring (fam lp))"
        proof (cases "lp = owner")
          case True
          have q_removed:
              "q \<in> set (remove1 p (ring (fam owner)))"
            using q_post True by (simp add: list_remove_abs_def)
          have "q \<in> set (ring (fam owner))"
            by (rule subsetD[OF set_remove1_subset q_removed])
          then show ?thesis using True by simp
        next
          case False
          show ?thesis using q_post False by simp
        qed
        show "raw_item_region p \<inter> raw_item_region q = {}"
          by (rule item_items[rule_format, OF q_old q_ne])
      qed
      show
        "p \<noteq> raw_end_item lp \<and>
         raw_item_region p \<inter> raw_list_region lp = {} \<and>
         (\<forall>q\<in>set (ring ((fam(owner :=
            list_remove_abs p (fam owner))) lp)).
            q \<noteq> p \<longrightarrow>
            raw_item_region p \<inter> raw_item_region q = {})"
        using not_end item_list post_items by blast
    qed
  qed
qed

theorem raw_family_globally_unlinked_fresh_for_target:
  assumes family: "raw_family_rel h roots fam"
    and unlinked: "raw_family_globally_unlinked h roots fam p"
    and target: "target \<in> roots"
    and geometry: "raw_family_insert_geometry roots fam p"
  shows "raw_fresh_for_insert target (ring (fam target)) p"
proof -
  have absent: "p \<notin> set (ring (fam target))"
    using unlinked target
    by (auto simp: raw_family_globally_unlinked_def raw_family_members_def)
  have guarded: "c_guard p"
    and not_end: "p \<noteq> raw_end_item target"
    and item_list:
      "raw_item_region p \<inter> raw_list_region target = {}"
    and item_items:
      "\<forall>q\<in>set (ring (fam target)).
         q \<noteq> p \<longrightarrow>
         raw_item_region p \<inter> raw_item_region q = {}"
    using geometry target
    by (auto simp: raw_family_insert_geometry_def)
  show ?thesis
    using guarded not_end absent item_list item_items
    by (auto simp: raw_fresh_for_insert_def)
qed

end
