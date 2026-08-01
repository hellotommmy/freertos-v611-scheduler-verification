theory List_V611_Raw_R6_Insert_Post_Transformer
  imports
    "EAL6_FreeRTOS_V611_List_Raw_R6_Insert_Source_Effects.List_V611_Raw_R6_Insert_Source_Effects"
    "EAL6_FreeRTOS_V611_List_Raw_R6_Remove_Topology_Effect.List_V611_Raw_R6_Remove_Topology_Effect"
    "EAL6_FreeRTOS_V611_List_Raw_R6_Remove_Payload_Effect.List_V611_Raw_R6_Remove_Payload_Effect"
begin

text \<open>
  Pure post-transformer projection for general-N vListInsertEnd.  The source
  VCG and exact seven-stage heap equality live in the parent insertion-source
  theory.  This theory only projects that exact heap into count, cursor,
  topology, new-item payload, and old-item frame observations, then feeds
  those observations to the already checked representation assembler.
\<close>

definition raw_insert_effect ::
  "heap_mem \<Rightarrow> heap_mem \<Rightarrow> xLIST_C ptr \<Rightarrow>
   (raw_node_id, raw_key) xlist_abs \<Rightarrow> raw_node_id \<Rightarrow> bool"
where
  "raw_insert_effect h h' lp xs p \<longleftrightarrow>
     uxNumberOfItems_C (h_val h' lp) =
       uxNumberOfItems_C (h_val h lp) + 1 \<and>
     pxIndex_C (h_val h' lp) = p \<and>
     raw_ring_links h' lp
       (ring (list_insert_end_abs p (raw_key_at h p) xs)) \<and>
     raw_key_at h' p = raw_key_at h p \<and>
     pvContainer_C (h_val h' p) =
       PTR_COERCE(xLIST_C \<rightarrow> unit) lp \<and>
     (\<forall>q \<in> set (ring xs).
        raw_key_at h' q = raw_key_at h q \<and>
        pvContainer_C (h_val h' q) = pvContainer_C (h_val h q))"

lemma raw_xlist_insert_count_transfer:
  assumes rel: "raw_xlist_rel h lp xs"
    and can_increment: "raw_count_can_increment xs"
    and count_word:
      "uxNumberOfItems_C (h_val h' lp) =
       uxNumberOfItems_C (h_val h lp) + 1"
  shows
    "unat (uxNumberOfItems_C (h_val h' lp)) =
     length (ring (list_insert_end_abs p k xs))"
proof -
  let ?n = "uxNumberOfItems_C (h_val h lp)"
  have old_count: "unat ?n = length (ring xs)"
    by (rule raw_xlist_rel_countD[OF rel])
  have old_not_max: "?n \<noteq> (max_word :: 32 word)"
  proof
    assume "?n = (max_word :: 32 word)"
    then have "length (ring xs) = unat (max_word :: 32 word)"
      using old_count by simp
    then show False
      using can_increment by (simp add: raw_count_can_increment_def)
  qed
  have successor:
    "unat (?n + 1) = Suc (unat ?n)"
    using old_not_max
    by (metis add.commute max_word_wrap unatSuc)
  have wf: "xlist_wf xs"
    using rel by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  show ?thesis
    using count_word successor old_count list_insert_end_ring_length[OF wf]
    by simp
qed

lemma raw_xlist_insert_cursor_transfer:
  assumes fresh: "raw_fresh_for_insert lp (ring xs) p"
    and index: "pxIndex_C (h_val h' lp) = p"
  shows
    "raw_cursor_at h' lp = cursor (list_insert_end_abs p k xs)"
proof -
  have not_end: "p \<noteq> raw_end_item lp"
    using fresh by (simp add: raw_fresh_for_insert_def)
  show ?thesis
    using index not_end
    by (simp add: raw_cursor_at_def list_insert_end_abs_def)
qed

theorem raw_insert_effect_refines:
  assumes rel: "raw_xlist_rel h lp xs"
    and fresh: "raw_fresh_for_insert lp (ring xs) p"
    and can_increment: "raw_count_can_increment xs"
    and effect: "raw_insert_effect h h' lp xs p"
  shows
    "raw_xlist_rel h' lp
       (list_insert_end_abs p (raw_key_at h p) xs)"
proof -
  have count_word:
    "uxNumberOfItems_C (h_val h' lp) =
     uxNumberOfItems_C (h_val h lp) + 1"
    using effect by (simp add: raw_insert_effect_def)
  have count:
    "unat (uxNumberOfItems_C (h_val h' lp)) =
     length (ring (list_insert_end_abs p (raw_key_at h p) xs))"
    by (rule raw_xlist_insert_count_transfer[
          OF rel can_increment count_word])
  have index: "pxIndex_C (h_val h' lp) = p"
    using effect by (simp add: raw_insert_effect_def)
  have cursor:
    "raw_cursor_at h' lp =
     cursor (list_insert_end_abs p (raw_key_at h p) xs)"
    by (rule raw_xlist_insert_cursor_transfer[OF fresh index])
  have links:
    "raw_ring_links h' lp
       (ring (list_insert_end_abs p (raw_key_at h p) xs))"
    using effect by (simp add: raw_insert_effect_def)
  have new_key: "raw_key_at h' p = raw_key_at h p"
    using effect by (simp add: raw_insert_effect_def)
  have new_container:
    "pvContainer_C (h_val h' p) =
     PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
    using effect by (simp add: raw_insert_effect_def)
  have old_frame:
    "\<And>q. q \<in> set (ring xs) \<Longrightarrow>
      raw_key_at h' q = raw_key_at h q \<and>
      pvContainer_C (h_val h' q) = pvContainer_C (h_val h q)"
    using effect by (auto simp: raw_insert_effect_def)
  show ?thesis
    by (rule raw_xlist_rel_insert_endI[
          OF rel fresh count cursor links new_key new_container old_frame])
qed

lemma raw_fresh_next_heap_preserves_cycle_observations:
  assumes fresh: "raw_fresh_for_insert lp rs p"
    and member: "u \<in> insert (raw_end_item lp) (set rs)"
  shows
    "raw_next_at (raw_insert_next_heap h p v) lp u =
       raw_next_at h lp u \<and>
     raw_prev_at (raw_insert_next_heap h p v) lp u =
       raw_prev_at h lp u"
proof (cases "u = raw_end_item lp")
  case True
  have item_list:
    "raw_item_region p \<inter> raw_list_region lp = {}"
    using fresh by (simp add: raw_fresh_for_insert_def)
  have field_list:
    "raw_pointer_field_region (raw_next_field_ptr p) \<inter>
     raw_list_region lp = {}"
    using raw_next_field_region_subset_item[where u=p] item_list by blast
  have list_same:
    "h_val (raw_insert_next_heap h p v) lp = h_val h lp"
    unfolding raw_insert_next_heap_def
    by (rule raw_pointer_field_update_preserves_disjoint_list[
          OF field_list])
  show ?thesis
    using True list_same by (simp add: raw_next_at_def raw_prev_at_def)
next
  case False
  have live: "u \<in> set rs"
    using member False by simp
  have item_disjoint:
    "raw_item_region p \<inter> raw_item_region u = {}"
    using fresh live by (simp add: raw_fresh_for_insert_def)
  have field_disjoint:
    "raw_pointer_field_region (raw_next_field_ptr p) \<inter>
     raw_item_region u = {}"
    using raw_next_field_region_subset_item[where u=p] item_disjoint
    by blast
  have item_same:
    "h_val (raw_insert_next_heap h p v) u = h_val h u"
    unfolding raw_insert_next_heap_def
    by (rule raw_pointer_field_update_preserves_disjoint_item[
          OF field_disjoint])
  show ?thesis
    using False item_same by (simp add: raw_next_at_def raw_prev_at_def)
qed

lemma raw_fresh_previous_heap_preserves_cycle_observations:
  assumes fresh: "raw_fresh_for_insert lp rs p"
    and member: "u \<in> insert (raw_end_item lp) (set rs)"
  shows
    "raw_next_at (raw_insert_previous_heap h p v) lp u =
       raw_next_at h lp u \<and>
     raw_prev_at (raw_insert_previous_heap h p v) lp u =
       raw_prev_at h lp u"
proof (cases "u = raw_end_item lp")
  case True
  have item_list:
    "raw_item_region p \<inter> raw_list_region lp = {}"
    using fresh by (simp add: raw_fresh_for_insert_def)
  have field_list:
    "raw_pointer_field_region (raw_previous_field_ptr p) \<inter>
     raw_list_region lp = {}"
    using raw_previous_field_region_subset_item[where u=p] item_list
    by blast
  have list_same:
    "h_val (raw_insert_previous_heap h p v) lp = h_val h lp"
    unfolding raw_insert_previous_heap_def
    by (rule raw_pointer_field_update_preserves_disjoint_list[
          OF field_list])
  show ?thesis
    using True list_same by (simp add: raw_next_at_def raw_prev_at_def)
next
  case False
  have live: "u \<in> set rs"
    using member False by simp
  have item_disjoint:
    "raw_item_region p \<inter> raw_item_region u = {}"
    using fresh live by (simp add: raw_fresh_for_insert_def)
  have field_disjoint:
    "raw_pointer_field_region (raw_previous_field_ptr p) \<inter>
     raw_item_region u = {}"
    using raw_previous_field_region_subset_item[where u=p] item_disjoint
    by blast
  have item_same:
    "h_val (raw_insert_previous_heap h p v) u = h_val h u"
    unfolding raw_insert_previous_heap_def
    by (rule raw_pointer_field_update_preserves_disjoint_item[
          OF field_disjoint])
  show ?thesis
    using False item_same by (simp add: raw_next_at_def raw_prev_at_def)
qed

lemma raw_cycle_next_heap_preserves_fresh_item:
  assumes fresh: "raw_fresh_for_insert lp rs p"
    and writer: "u \<in> insert (raw_end_item lp) (set rs)"
  shows "h_val (raw_insert_next_heap h u v) p = h_val h p"
proof (cases "u = raw_end_item lp")
  case True
  have item_list:
    "raw_item_region p \<inter> raw_list_region lp = {}"
    using fresh by (simp add: raw_fresh_for_insert_def)
  have field_list:
    "raw_pointer_field_region (raw_next_field_ptr u) \<subseteq>
     raw_list_region lp"
    using True raw_end_next_field_region_subset_list[where lp=lp]
    by simp
  have field_item:
    "raw_pointer_field_region (raw_next_field_ptr u) \<inter>
     raw_item_region p = {}"
    using field_list item_list by blast
  show ?thesis
    unfolding raw_insert_next_heap_def
    by (rule raw_pointer_field_update_preserves_disjoint_item[
          OF field_item])
next
  case False
  have old: "u \<in> set rs"
    using writer False by simp
  have item_disjoint:
    "raw_item_region p \<inter> raw_item_region u = {}"
    using fresh old by (simp add: raw_fresh_for_insert_def)
  have field_item:
    "raw_pointer_field_region (raw_next_field_ptr u) \<inter>
     raw_item_region p = {}"
    using raw_next_field_region_subset_item[where u=u] item_disjoint
    by blast
  show ?thesis
    unfolding raw_insert_next_heap_def
    by (rule raw_pointer_field_update_preserves_disjoint_item[
          OF field_item])
qed

lemma raw_cycle_previous_heap_preserves_fresh_item:
  assumes fresh: "raw_fresh_for_insert lp rs p"
    and writer: "u \<in> insert (raw_end_item lp) (set rs)"
  shows "h_val (raw_insert_previous_heap h u v) p = h_val h p"
proof (cases "u = raw_end_item lp")
  case True
  have item_list:
    "raw_item_region p \<inter> raw_list_region lp = {}"
    using fresh by (simp add: raw_fresh_for_insert_def)
  have field_list:
    "raw_pointer_field_region (raw_previous_field_ptr u) \<subseteq>
     raw_list_region lp"
    using True raw_end_previous_field_region_subset_list[where lp=lp]
    by simp
  have field_item:
    "raw_pointer_field_region (raw_previous_field_ptr u) \<inter>
     raw_item_region p = {}"
    using field_list item_list by blast
  show ?thesis
    unfolding raw_insert_previous_heap_def
    by (rule raw_pointer_field_update_preserves_disjoint_item[
          OF field_item])
next
  case False
  have old: "u \<in> set rs"
    using writer False by simp
  have item_disjoint:
    "raw_item_region p \<inter> raw_item_region u = {}"
    using fresh old by (simp add: raw_fresh_for_insert_def)
  have field_item:
    "raw_pointer_field_region (raw_previous_field_ptr u) \<inter>
     raw_item_region p = {}"
    using raw_previous_field_region_subset_item[where u=u] item_disjoint
    by blast
  show ?thesis
    unfolding raw_insert_previous_heap_def
    by (rule raw_pointer_field_update_preserves_disjoint_item[
          OF field_item])
qed

lemma raw_cycle_previous_heap_next_frame:
  assumes layout: "raw_xlist_layout lp rs"
    and writer: "u \<in> insert (raw_end_item lp) (set rs)"
    and observer: "v \<in> insert (raw_end_item lp) (set rs)"
  shows
    "raw_next_at (raw_insert_previous_heap h u x) lp v =
     raw_next_at h lp v"
proof (cases "u = v")
  case True
  have guard: "c_guard u"
    using layout writer by (auto simp: raw_xlist_layout_def)
  show ?thesis
    unfolding raw_insert_previous_heap_def
    using True raw_next_at_survives_same_node_previous_field_update[
      OF guard, where q=x and h=h and lp=lp]
    by simp
next
  case False
  have observations:
    "raw_next_at (heap_update (raw_previous_field_ptr u) x h) lp v =
       raw_next_at h lp v \<and>
     raw_prev_at (heap_update (raw_previous_field_ptr u) x h) lp v =
       raw_prev_at h lp v"
    by (rule raw_cycle_observations_survive_other_previous_field_update[
          OF layout writer observer False])
  show ?thesis
    using observations by (simp add: raw_insert_previous_heap_def)
qed

lemma raw_cycle_previous_heap_previous_frame:
  assumes layout: "raw_xlist_layout lp rs"
    and writer: "u \<in> insert (raw_end_item lp) (set rs)"
    and observer: "v \<in> insert (raw_end_item lp) (set rs)"
    and different: "v \<noteq> u"
  shows
    "raw_prev_at (raw_insert_previous_heap h u x) lp v =
     raw_prev_at h lp v"
proof -
  have observations:
    "raw_next_at (heap_update (raw_previous_field_ptr u) x h) lp v =
       raw_next_at h lp v \<and>
     raw_prev_at (heap_update (raw_previous_field_ptr u) x h) lp v =
       raw_prev_at h lp v"
    by (rule raw_cycle_observations_survive_other_previous_field_update[
          OF layout writer observer])
       (use different in auto)
  show ?thesis
    using observations by (simp add: raw_insert_previous_heap_def)
qed

lemma raw_cycle_next_heap_next_frame:
  assumes layout: "raw_xlist_layout lp rs"
    and writer: "u \<in> insert (raw_end_item lp) (set rs)"
    and observer: "v \<in> insert (raw_end_item lp) (set rs)"
    and different: "v \<noteq> u"
  shows
    "raw_next_at (raw_insert_next_heap h u x) lp v =
     raw_next_at h lp v"
proof -
  have observations:
    "raw_next_at (heap_update (raw_next_field_ptr u) x h) lp v =
       raw_next_at h lp v \<and>
     raw_prev_at (heap_update (raw_next_field_ptr u) x h) lp v =
       raw_prev_at h lp v"
    by (rule raw_cycle_observations_survive_other_next_field_update[
          OF layout writer observer])
       (use different in auto)
  show ?thesis
    using observations by (simp add: raw_insert_next_heap_def)
qed

lemma raw_cycle_next_heap_previous_frame:
  assumes layout: "raw_xlist_layout lp rs"
    and writer: "u \<in> insert (raw_end_item lp) (set rs)"
    and observer: "v \<in> insert (raw_end_item lp) (set rs)"
  shows
    "raw_prev_at (raw_insert_next_heap h u x) lp v =
     raw_prev_at h lp v"
proof (cases "u = v")
  case True
  have guard: "c_guard u"
    using layout writer by (auto simp: raw_xlist_layout_def)
  show ?thesis
    unfolding raw_insert_next_heap_def
    using True raw_prev_at_survives_same_node_next_field_update[
      OF guard, where q=x and h=h and lp=lp]
    by simp
next
  case False
  have observations:
    "raw_next_at (heap_update (raw_next_field_ptr u) x h) lp v =
       raw_next_at h lp v \<and>
     raw_prev_at (heap_update (raw_next_field_ptr u) x h) lp v =
       raw_prev_at h lp v"
    by (rule raw_cycle_observations_survive_other_next_field_update[
          OF layout writer observer False])
  show ?thesis
    using observations by (simp add: raw_insert_next_heap_def)
qed

lemma raw_insert_link_prefix_ring_links:
  assumes rel: "raw_xlist_rel h lp xs"
    and fresh: "raw_fresh_for_insert lp (ring xs) p"
    and c_def: "c = raw_cursor_node lp xs"
    and q_def: "q = raw_next_at h lp c"
    and h1_def: "h1 = raw_insert_next_heap h p q"
    and h2_def: "h2 = raw_insert_previous_heap h1 p c"
    and h3_def: "h3 = raw_insert_previous_heap h2 q p"
    and h4_def: "h4 = raw_insert_next_heap h3 c p"
  shows
    "raw_ring_links h4 lp
       (ring (list_insert_end_abs p (raw_key_at h p) xs))"
proof -
  let ?cycle = "insert (raw_end_item lp) (set (ring xs))"
  have wf: "xlist_wf xs"
    using rel by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have layout: "raw_xlist_layout lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def)
  have links: "raw_ring_links h lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have distinct_cycle: "distinct (raw_end_item lp # ring xs)"
    by (rule raw_xlist_rel_distinct_cycle_nodes[OF rel])
  have c_cycle: "c \<in> ?cycle"
    unfolding c_def by (rule raw_cursor_node_in_cycle[OF wf])
  have q_cycle: "q \<in> ?cycle"
    unfolding q_def by (rule raw_ring_links_next_closed[OF links c_cycle])
  have p_guard: "c_guard p"
    using fresh by (simp add: raw_fresh_for_insert_def)
  have c_guard: "c_guard c"
    by (rule raw_xlist_rel_cycle_node_guard[OF rel c_cycle])
  have q_guard: "c_guard q"
    by (rule raw_xlist_rel_cycle_node_guard[OF rel q_cycle])
  have p_not_cycle: "p \<notin> ?cycle"
    using fresh by (simp add: raw_fresh_for_insert_def)
  have p_ne_c: "p \<noteq> c" and p_ne_q: "p \<noteq> q"
    using p_not_cycle c_cycle q_cycle by auto

  have h1_next: "raw_next_at h1 lp p = q"
    unfolding h1_def raw_insert_next_heap_def
    by (rule raw_next_at_after_same_node_next_field_update[OF p_guard])
  have h2_next: "raw_next_at h2 lp p = q"
    unfolding h2_def raw_insert_previous_heap_def
    using raw_next_at_survives_same_node_previous_field_update[
        OF p_guard, where q=c and h=h1 and lp=lp]
      h1_next
    by simp
  have h2_previous: "raw_prev_at h2 lp p = c"
    unfolding h2_def raw_insert_previous_heap_def
    by (rule raw_prev_at_after_same_node_previous_field_update[OF p_guard])
  have h3_p_same: "h_val h3 p = h_val h2 p"
    unfolding h3_def
    by (rule raw_cycle_previous_heap_preserves_fresh_item[
          OF fresh q_cycle])
  have h4_p_same: "h_val h4 p = h_val h3 p"
    unfolding h4_def
    by (rule raw_cycle_next_heap_preserves_fresh_item[OF fresh c_cycle])
  have p_not_end: "p \<noteq> raw_end_item lp"
    using fresh by (simp add: raw_fresh_for_insert_def)
  have exit_next: "raw_next_at h4 lp p = q"
    using h4_p_same h3_p_same h2_next p_not_end
    by (simp add: raw_next_at_def)
  have entry_previous: "raw_prev_at h4 lp p = c"
    using h4_p_same h3_p_same h2_previous p_not_end
    by (simp add: raw_prev_at_def)

  have h3_q_previous: "raw_prev_at h3 lp q = p"
    unfolding h3_def raw_insert_previous_heap_def
    by (rule raw_prev_at_after_same_node_previous_field_update[OF q_guard])
  have exit_previous: "raw_prev_at h4 lp q = p"
  proof -
    have frame: "raw_prev_at h4 lp q = raw_prev_at h3 lp q"
      unfolding h4_def
      by (rule raw_cycle_next_heap_previous_frame[
            OF layout c_cycle q_cycle])
    show ?thesis using frame h3_q_previous by simp
  qed
  have entry_next: "raw_next_at h4 lp c = p"
    unfolding h4_def raw_insert_next_heap_def
    by (rule raw_next_at_after_same_node_next_field_update[OF c_guard])

  have two_fresh_observations:
    "\<And>u. u \<in> ?cycle \<Longrightarrow>
      raw_next_at h2 lp u = raw_next_at h lp u \<and>
      raw_prev_at h2 lp u = raw_prev_at h lp u"
  proof -
    fix u
    assume u_cycle: "u \<in> ?cycle"
    have first:
      "raw_next_at h1 lp u = raw_next_at h lp u \<and>
       raw_prev_at h1 lp u = raw_prev_at h lp u"
      unfolding h1_def
      by (rule raw_fresh_next_heap_preserves_cycle_observations[
            OF fresh u_cycle])
    have second:
      "raw_next_at h2 lp u = raw_next_at h1 lp u \<and>
       raw_prev_at h2 lp u = raw_prev_at h1 lp u"
      unfolding h2_def
      by (rule raw_fresh_previous_heap_preserves_cycle_observations[
            OF fresh u_cycle])
    show
      "raw_next_at h2 lp u = raw_next_at h lp u \<and>
       raw_prev_at h2 lp u = raw_prev_at h lp u"
      using first second by simp
  qed
  have next_frame:
    "\<And>u. u \<in> ?cycle \<Longrightarrow> u \<noteq> c \<Longrightarrow>
      raw_next_at h4 lp u = raw_next_at h lp u"
  proof -
    fix u
    assume u_cycle: "u \<in> ?cycle" and u_ne_c: "u \<noteq> c"
    have initial: "raw_next_at h2 lp u = raw_next_at h lp u"
      using two_fresh_observations[OF u_cycle] by simp
    have after_previous: "raw_next_at h3 lp u = raw_next_at h2 lp u"
      unfolding h3_def
      by (rule raw_cycle_previous_heap_next_frame[
            OF layout q_cycle u_cycle])
    have after_next: "raw_next_at h4 lp u = raw_next_at h3 lp u"
      unfolding h4_def
      by (rule raw_cycle_next_heap_next_frame[
            OF layout c_cycle u_cycle u_ne_c])
    show "raw_next_at h4 lp u = raw_next_at h lp u"
      using initial after_previous after_next by simp
  qed
  have previous_frame:
    "\<And>v. v \<in> ?cycle \<Longrightarrow> v \<noteq> q \<Longrightarrow>
      raw_prev_at h4 lp v = raw_prev_at h lp v"
  proof -
    fix v
    assume v_cycle: "v \<in> ?cycle" and v_ne_q: "v \<noteq> q"
    have initial: "raw_prev_at h2 lp v = raw_prev_at h lp v"
      using two_fresh_observations[OF v_cycle] by simp
    have after_previous: "raw_prev_at h3 lp v = raw_prev_at h2 lp v"
      unfolding h3_def
      by (rule raw_cycle_previous_heap_previous_frame[
            OF layout q_cycle v_cycle v_ne_q])
    have after_next: "raw_prev_at h4 lp v = raw_prev_at h3 lp v"
      unfolding h4_def
      by (rule raw_cycle_next_heap_previous_frame[
            OF layout c_cycle v_cycle])
    show "raw_prev_at h4 lp v = raw_prev_at h lp v"
      using initial after_previous after_next by simp
  qed
  show ?thesis
    apply (rule raw_ring_links_splice[OF wf distinct_cycle links])
    using entry_next entry_previous exit_next exit_previous
      next_frame previous_frame c_def q_def
    apply simp_all
    done
qed

lemma raw_cycle_observations_survive_container_update:
  assumes layout: "raw_xlist_layout lp rs"
    and item: "p \<in> set rs"
    and observer: "u \<in> insert (raw_end_item lp) (set rs)"
  shows
    "raw_next_at
       (heap_update p
         (pvContainer_C_update f (h_val h p)) h) lp u =
       raw_next_at h lp u \<and>
     raw_prev_at
       (heap_update p (pvContainer_C_update f (h_val h p)) h) lp u =
       raw_prev_at h lp u"
proof (cases "u = p")
  case True
  have guard: "c_guard p"
    using layout item by (auto simp: raw_xlist_layout_def)
  have not_end: "p \<noteq> raw_end_item lp"
    using layout item by (auto simp: raw_xlist_layout_def)
  show ?thesis
    using True guard not_end
    by (simp add: raw_next_at_def raw_prev_at_def h_val_heap_update)
next
  case different: False
  show ?thesis
  proof (cases "u = raw_end_item lp")
    case True
    have disjoint:
      "raw_item_region p \<inter> raw_list_region lp = {}"
      using layout item by (auto simp: raw_xlist_layout_def)
    have list_same:
      "h_val
         (heap_update p (pvContainer_C_update f (h_val h p)) h) lp = h_val h lp"
      by (rule raw_item_update_preserves_disjoint_list[OF disjoint])
    show ?thesis
      using True list_same by (simp add: raw_next_at_def raw_prev_at_def)
  next
    case False
    have live: "u \<in> set rs"
      using observer False by simp
    have disjoint:
      "raw_item_region p \<inter> raw_item_region u = {}"
      using layout item live different
      by (auto simp: raw_xlist_layout_def)
    have item_same:
      "h_val
         (heap_update p (pvContainer_C_update f (h_val h p)) h) u = h_val h u"
      by (rule raw_item_update_preserves_disjoint_item[OF disjoint])
    show ?thesis
      using False item_same by (simp add: raw_next_at_def raw_prev_at_def)
  qed
qed

lemma raw_ring_links_survives_container_update:
  assumes layout: "raw_xlist_layout lp rs"
    and item: "p \<in> set rs"
    and links: "raw_ring_links h lp rs"
  shows
    "raw_ring_links
       (heap_update p
         (pvContainer_C_update f (h_val h p)) h) lp rs"
proof (rule raw_ring_links_observation_cong[OF links])
  fix u
  assume observer: "u \<in> insert (raw_end_item lp) (set rs)"
  show
    "raw_next_at
       (heap_update p (pvContainer_C_update f (h_val h p)) h) lp u =
       raw_next_at h lp u \<and>
     raw_prev_at
       (heap_update p (pvContainer_C_update f (h_val h p)) h) lp u =
       raw_prev_at h lp u"
    by (rule raw_cycle_observations_survive_container_update[
          OF layout item observer])
qed

lemma raw_insert_concrete_heap_ring_links:
  assumes rel: "raw_xlist_rel h lp xs"
    and fresh: "raw_fresh_for_insert lp (ring xs) p"
  shows
    "raw_ring_links (raw_insert_concrete_heap h lp xs p) lp
       (ring (list_insert_end_abs p (raw_key_at h p) xs))"
proof -
  let ?c = "raw_cursor_node lp xs"
  let ?q = "raw_next_at h lp ?c"
  let ?h1 = "raw_insert_next_heap h p ?q"
  let ?h2 = "raw_insert_previous_heap ?h1 p ?c"
  let ?h3 = "raw_insert_previous_heap ?h2 ?q p"
  let ?h4 = "raw_insert_next_heap ?h3 ?c p"
  let ?h5 = "raw_insert_index_heap ?h4 lp p"
  let ?h6 = "raw_insert_container_heap ?h5 lp p"
  let ?ys = "list_insert_end_abs p (raw_key_at h p) xs"
  have old_wf: "xlist_wf xs"
    using rel by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have old_layout: "raw_xlist_layout lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def)
  have set_eq: "set (ring ?ys) = insert p (set (ring xs))"
    by (rule list_insert_end_ring_set[OF old_wf])
  have new_layout: "raw_xlist_layout lp (ring ?ys)"
    by (rule raw_xlist_layout_extend_set[OF old_layout fresh set_eq])
  have p_member: "p \<in> set (ring ?ys)"
    using set_eq by simp
  have link_prefix: "raw_ring_links ?h4 lp (ring ?ys)"
    apply (rule raw_insert_link_prefix_ring_links[OF rel fresh])
    apply simp_all
    done
  have index_links: "raw_ring_links ?h5 lp (ring ?ys)"
    unfolding raw_insert_index_heap_def
    by (rule raw_ring_links_survives_index_update[
          OF new_layout link_prefix])
  have container_links: "raw_ring_links ?h6 lp (ring ?ys)"
    unfolding raw_insert_container_heap_def
    by (rule raw_ring_links_survives_container_update[
          OF new_layout p_member index_links])
  have count_links:
    "raw_ring_links (raw_insert_count_heap ?h6 lp) lp (ring ?ys)"
    unfolding raw_insert_count_heap_def
    by (rule raw_ring_links_survives_count_update[
          OF new_layout container_links])
  show ?thesis
    using count_links
    by (simp add: raw_insert_concrete_heap_def Let_def)
qed

lemma raw_insert_previous_heap_preserves_list:
  assumes fresh: "raw_fresh_for_insert lp rs p"
  shows
    "h_val (raw_insert_previous_heap h p q) lp = h_val h lp"
proof -
  have item_list:
    "raw_item_region p \<inter> raw_list_region lp = {}"
    using fresh by (simp add: raw_fresh_for_insert_def)
  have field_list:
    "raw_pointer_field_region (raw_previous_field_ptr p) \<inter>
     raw_list_region lp = {}"
    using raw_previous_field_region_subset_item[where u=p] item_list
    by blast
  show ?thesis
    unfolding raw_insert_previous_heap_def
    by (rule raw_pointer_field_update_preserves_disjoint_list[
          OF field_list])
qed

lemma raw_insert_concrete_heap_count_effect:
  assumes rel: "raw_xlist_rel h lp xs"
    and fresh: "raw_fresh_for_insert lp (ring xs) p"
  shows
    "uxNumberOfItems_C
       (h_val (raw_insert_concrete_heap h lp xs p) lp) =
     uxNumberOfItems_C (h_val h lp) + 1"
proof -
  let ?c = "raw_cursor_node lp xs"
  let ?q = "raw_next_at h lp ?c"
  let ?h1 = "raw_insert_next_heap h p ?q"
  let ?h2 = "raw_insert_previous_heap ?h1 p ?c"
  let ?h3 = "raw_insert_previous_heap ?h2 ?q p"
  let ?h4 = "raw_insert_next_heap ?h3 ?c p"
  let ?h5 = "raw_insert_index_heap ?h4 lp p"
  let ?h6 = "raw_insert_container_heap ?h5 lp p"
  have wf: "xlist_wf xs"
    using rel by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have layout: "raw_xlist_layout lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def)
  have links: "raw_ring_links h lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have c_cycle:
    "?c \<in> insert (raw_end_item lp) (set (ring xs))"
    by (rule raw_cursor_node_in_cycle[OF wf])
  have q_cycle:
    "?q \<in> insert (raw_end_item lp) (set (ring xs))"
    by (rule raw_ring_links_next_closed[OF links c_cycle])
  have guard: "c_guard lp"
    using layout by (simp add: raw_xlist_layout_def)
  have item_list:
    "raw_item_region p \<inter> raw_list_region lp = {}"
    using fresh by (simp add: raw_fresh_for_insert_def)
  have first_list: "h_val ?h1 lp = h_val h lp"
    by (rule raw_insert_next_heap_preserves_list[OF fresh])
  have second_list: "h_val ?h2 lp = h_val ?h1 lp"
    by (rule raw_insert_previous_heap_preserves_list[OF fresh])
  have third_count:
    "uxNumberOfItems_C (h_val ?h3 lp) =
     uxNumberOfItems_C (h_val ?h2 lp)"
    unfolding raw_insert_previous_heap_def
    by (rule raw_previous_field_update_preserves_count[
          OF layout q_cycle])
  have fourth_count:
    "uxNumberOfItems_C (h_val ?h4 lp) =
     uxNumberOfItems_C (h_val ?h3 lp)"
    unfolding raw_insert_next_heap_def
    by (rule raw_next_field_update_preserves_count[
          OF layout c_cycle])
  have index_count:
    "uxNumberOfItems_C (h_val ?h5 lp) =
     uxNumberOfItems_C (h_val ?h4 lp)"
    unfolding raw_insert_index_heap_def
    using guard by (simp add: h_val_heap_update)
  have container_list: "h_val ?h6 lp = h_val ?h5 lp"
    unfolding raw_insert_container_heap_def
    by (rule raw_item_update_preserves_disjoint_list[OF item_list])
  have final_count:
    "uxNumberOfItems_C
       (h_val (raw_insert_count_heap ?h6 lp) lp) =
     uxNumberOfItems_C (h_val ?h6 lp) + 1"
    unfolding raw_insert_count_heap_def
    using guard by (simp add: h_val_heap_update)
  show ?thesis
    using first_list second_list third_count fourth_count index_count
      container_list final_count
    by (simp add: raw_insert_concrete_heap_def Let_def)
qed

lemma raw_insert_concrete_heap_index_effect:
  assumes rel: "raw_xlist_rel h lp xs"
    and fresh: "raw_fresh_for_insert lp (ring xs) p"
  shows
    "pxIndex_C (h_val (raw_insert_concrete_heap h lp xs p) lp) = p"
proof -
  let ?c = "raw_cursor_node lp xs"
  let ?q = "raw_next_at h lp ?c"
  let ?h1 = "raw_insert_next_heap h p ?q"
  let ?h2 = "raw_insert_previous_heap ?h1 p ?c"
  let ?h3 = "raw_insert_previous_heap ?h2 ?q p"
  let ?h4 = "raw_insert_next_heap ?h3 ?c p"
  let ?h5 = "raw_insert_index_heap ?h4 lp p"
  let ?h6 = "raw_insert_container_heap ?h5 lp p"
  have layout: "raw_xlist_layout lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def)
  have guard: "c_guard lp"
    using layout by (simp add: raw_xlist_layout_def)
  have item_list:
    "raw_item_region p \<inter> raw_list_region lp = {}"
    using fresh by (simp add: raw_fresh_for_insert_def)
  have index_readback: "pxIndex_C (h_val ?h5 lp) = p"
    unfolding raw_insert_index_heap_def
    using guard by (simp add: h_val_heap_update)
  have container_list: "h_val ?h6 lp = h_val ?h5 lp"
    unfolding raw_insert_container_heap_def
    by (rule raw_item_update_preserves_disjoint_list[OF item_list])
  have count_index:
    "pxIndex_C (h_val (raw_insert_count_heap ?h6 lp) lp) =
     pxIndex_C (h_val ?h6 lp)"
    unfolding raw_insert_count_heap_def
    using guard by (simp add: h_val_heap_update)
  show ?thesis
    using index_readback container_list count_index
    by (simp add: raw_insert_concrete_heap_def Let_def)
qed

lemma raw_fresh_next_heap_preserves_old_item:
  assumes fresh: "raw_fresh_for_insert lp rs p"
    and live: "q \<in> set rs"
  shows "h_val (raw_insert_next_heap h p v) q = h_val h q"
proof -
  have items: "raw_item_region p \<inter> raw_item_region q = {}"
    using fresh live by (simp add: raw_fresh_for_insert_def)
  have field_item:
    "raw_pointer_field_region (raw_next_field_ptr p) \<inter>
     raw_item_region q = {}"
    using raw_next_field_region_subset_item[where u=p] items by blast
  show ?thesis
    unfolding raw_insert_next_heap_def
    by (rule raw_pointer_field_update_preserves_disjoint_item[
          OF field_item])
qed

lemma raw_fresh_previous_heap_preserves_old_item:
  assumes fresh: "raw_fresh_for_insert lp rs p"
    and live: "q \<in> set rs"
  shows "h_val (raw_insert_previous_heap h p v) q = h_val h q"
proof -
  have items: "raw_item_region p \<inter> raw_item_region q = {}"
    using fresh live by (simp add: raw_fresh_for_insert_def)
  have field_item:
    "raw_pointer_field_region (raw_previous_field_ptr p) \<inter>
     raw_item_region q = {}"
    using raw_previous_field_region_subset_item[where u=p] items by blast
  show ?thesis
    unfolding raw_insert_previous_heap_def
    by (rule raw_pointer_field_update_preserves_disjoint_item[
          OF field_item])
qed

lemma raw_list_update_preserves_fresh_item:
  assumes fresh: "raw_fresh_for_insert lp rs p"
  shows "h_val (heap_update lp (v :: xLIST_C) h) p = h_val h p"
proof -
  have disjoint: "raw_item_region p \<inter> raw_list_region lp = {}"
    using fresh by (simp add: raw_fresh_for_insert_def)
  show ?thesis
    by (rule
      List_V611_Raw_R6_Remove_Topology_Effect.raw_list_update_preserves_disjoint_item[
        OF disjoint])
qed

lemma raw_insert_concrete_heap_new_payload_effect:
  assumes rel: "raw_xlist_rel h lp xs"
    and fresh: "raw_fresh_for_insert lp (ring xs) p"
  shows
    "raw_key_at (raw_insert_concrete_heap h lp xs p) p = raw_key_at h p \<and>
     pvContainer_C (h_val (raw_insert_concrete_heap h lp xs p) p) =
       PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
proof -
  let ?c = "raw_cursor_node lp xs"
  let ?q = "raw_next_at h lp ?c"
  let ?h1 = "raw_insert_next_heap h p ?q"
  let ?h2 = "raw_insert_previous_heap ?h1 p ?c"
  let ?h3 = "raw_insert_previous_heap ?h2 ?q p"
  let ?h4 = "raw_insert_next_heap ?h3 ?c p"
  let ?h5 = "raw_insert_index_heap ?h4 lp p"
  let ?h6 = "raw_insert_container_heap ?h5 lp p"
  have wf: "xlist_wf xs"
    using rel by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have layout: "raw_xlist_layout lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def)
  have links: "raw_ring_links h lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have c_cycle:
    "?c \<in> insert (raw_end_item lp) (set (ring xs))"
    by (rule raw_cursor_node_in_cycle[OF wf])
  have q_cycle:
    "?q \<in> insert (raw_end_item lp) (set (ring xs))"
    by (rule raw_ring_links_next_closed[OF links c_cycle])
  have p_guard: "c_guard p"
    using fresh by (simp add: raw_fresh_for_insert_def)
  have first_key: "raw_key_at ?h1 p = raw_key_at h p"
    unfolding raw_insert_next_heap_def
    using raw_next_field_update_to_whole[
        OF p_guard, where q = ?q and h = h]
      p_guard
    by (simp add: raw_key_at_def h_val_heap_update)
  have second_key: "raw_key_at ?h2 p = raw_key_at ?h1 p"
    unfolding raw_insert_previous_heap_def
    using raw_previous_field_update_to_whole[
        OF p_guard, where q = ?c and h = ?h1]
      p_guard
    by (simp add: raw_key_at_def h_val_heap_update)
  have third_item: "h_val ?h3 p = h_val ?h2 p"
    by (rule raw_cycle_previous_heap_preserves_fresh_item[
          OF fresh q_cycle])
  have fourth_item: "h_val ?h4 p = h_val ?h3 p"
    by (rule raw_cycle_next_heap_preserves_fresh_item[OF fresh c_cycle])
  have index_item: "h_val ?h5 p = h_val ?h4 p"
    unfolding raw_insert_index_heap_def
    by (rule raw_list_update_preserves_fresh_item[OF fresh])
  have container_readback:
    "raw_key_at ?h6 p = raw_key_at ?h5 p \<and>
     pvContainer_C (h_val ?h6 p) =
       PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
    unfolding raw_insert_container_heap_def
    using p_guard
    by (simp add: raw_key_at_def h_val_heap_update)
  have count_item:
    "h_val (raw_insert_count_heap ?h6 lp) p = h_val ?h6 p"
    unfolding raw_insert_count_heap_def
    by (rule raw_list_update_preserves_fresh_item[OF fresh])
  show ?thesis
    using first_key second_key third_item fourth_item index_item
      container_readback count_item
    by (simp add: raw_insert_concrete_heap_def raw_key_at_def Let_def)
qed

lemma raw_insert_concrete_heap_old_payload_frame:
  assumes rel: "raw_xlist_rel h lp xs"
    and fresh: "raw_fresh_for_insert lp (ring xs) p"
    and live: "q0 \<in> set (ring xs)"
  shows
    "raw_key_at (raw_insert_concrete_heap h lp xs p) q0 = raw_key_at h q0 \<and>
     pvContainer_C (h_val (raw_insert_concrete_heap h lp xs p) q0) =
       pvContainer_C (h_val h q0)"
proof -
  let ?c = "raw_cursor_node lp xs"
  let ?q = "raw_next_at h lp ?c"
  let ?h1 = "raw_insert_next_heap h p ?q"
  let ?h2 = "raw_insert_previous_heap ?h1 p ?c"
  let ?h3 = "raw_insert_previous_heap ?h2 ?q p"
  let ?h4 = "raw_insert_next_heap ?h3 ?c p"
  let ?h5 = "raw_insert_index_heap ?h4 lp p"
  let ?h6 = "raw_insert_container_heap ?h5 lp p"
  have wf: "xlist_wf xs"
    using rel by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have layout: "raw_xlist_layout lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def)
  have links: "raw_ring_links h lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have c_cycle:
    "?c \<in> insert (raw_end_item lp) (set (ring xs))"
    by (rule raw_cursor_node_in_cycle[OF wf])
  have q_cycle:
    "?q \<in> insert (raw_end_item lp) (set (ring xs))"
    by (rule raw_ring_links_next_closed[OF links c_cycle])
  have first_item: "h_val ?h1 q0 = h_val h q0"
    by (rule raw_fresh_next_heap_preserves_old_item[OF fresh live])
  have second_item: "h_val ?h2 q0 = h_val ?h1 q0"
    by (rule raw_fresh_previous_heap_preserves_old_item[OF fresh live])
  have third_payload:
    "raw_key_at ?h3 q0 = raw_key_at ?h2 q0 \<and>
     pvContainer_C (h_val ?h3 q0) = pvContainer_C (h_val ?h2 q0)"
    unfolding raw_insert_previous_heap_def
    by (rule
      List_V611_Raw_R6_Remove_Payload_Effect.raw_cycle_previous_field_update_preserves_payload[
        OF layout q_cycle live])
  have fourth_payload:
    "raw_key_at ?h4 q0 = raw_key_at ?h3 q0 \<and>
     pvContainer_C (h_val ?h4 q0) = pvContainer_C (h_val ?h3 q0)"
    unfolding raw_insert_next_heap_def
    by (rule
      List_V611_Raw_R6_Remove_Payload_Effect.raw_cycle_next_field_update_preserves_payload[
        OF layout c_cycle live])
  have index_item: "h_val ?h5 q0 = h_val ?h4 q0"
    unfolding raw_insert_index_heap_def
    by (rule
      List_V611_Raw_R6_Remove_Payload_Effect.raw_layout_list_update_preserves_live_item[
        OF layout live])
  have p_ne_q0: "p \<noteq> q0"
    using fresh live by (auto simp: raw_fresh_for_insert_def)
  have item_disjoint:
    "raw_item_region p \<inter> raw_item_region q0 = {}"
    using fresh live by (simp add: raw_fresh_for_insert_def)
  have container_item: "h_val ?h6 q0 = h_val ?h5 q0"
    unfolding raw_insert_container_heap_def
    by (rule raw_item_update_preserves_disjoint_item[OF item_disjoint])
  have count_item:
    "h_val (raw_insert_count_heap ?h6 lp) q0 = h_val ?h6 q0"
    unfolding raw_insert_count_heap_def
    by (rule
      List_V611_Raw_R6_Remove_Payload_Effect.raw_layout_list_update_preserves_live_item[
        OF layout live])
  show ?thesis
    using first_item second_item third_payload fourth_payload index_item
      container_item count_item
    by (simp add: raw_insert_concrete_heap_def raw_key_at_def Let_def)
qed

theorem raw_insert_concrete_heap_effect:
  assumes rel: "raw_xlist_rel h lp xs"
    and fresh: "raw_fresh_for_insert lp (ring xs) p"
  shows
    "raw_insert_effect h (raw_insert_concrete_heap h lp xs p) lp xs p"
proof -
  have count:
    "uxNumberOfItems_C
       (h_val (raw_insert_concrete_heap h lp xs p) lp) =
     uxNumberOfItems_C (h_val h lp) + 1"
    by (rule raw_insert_concrete_heap_count_effect[OF rel fresh])
  have index:
    "pxIndex_C (h_val (raw_insert_concrete_heap h lp xs p) lp) = p"
    by (rule raw_insert_concrete_heap_index_effect[OF rel fresh])
  have links:
    "raw_ring_links (raw_insert_concrete_heap h lp xs p) lp
       (ring (list_insert_end_abs p (raw_key_at h p) xs))"
    by (rule raw_insert_concrete_heap_ring_links[OF rel fresh])
  have new_payload:
    "raw_key_at (raw_insert_concrete_heap h lp xs p) p = raw_key_at h p \<and>
     pvContainer_C (h_val (raw_insert_concrete_heap h lp xs p) p) =
       PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
    by (rule raw_insert_concrete_heap_new_payload_effect[OF rel fresh])
  have old_frame:
    "\<forall>q \<in> set (ring xs).
       raw_key_at (raw_insert_concrete_heap h lp xs p) q = raw_key_at h q \<and>
       pvContainer_C (h_val (raw_insert_concrete_heap h lp xs p) q) =
         pvContainer_C (h_val h q)"
    by (intro ballI raw_insert_concrete_heap_old_payload_frame[OF rel fresh])
  show ?thesis
    using count index links new_payload old_frame
    by (simp add: raw_insert_effect_def)
qed

theorem raw_insert_concrete_heap_refines:
  assumes rel: "raw_xlist_rel h lp xs"
    and fresh: "raw_fresh_for_insert lp (ring xs) p"
    and can_increment: "raw_count_can_increment xs"
  shows
    "raw_xlist_rel (raw_insert_concrete_heap h lp xs p) lp
       (list_insert_end_abs p (raw_key_at h p) xs)"
  by (rule raw_insert_effect_refines[
        OF rel fresh can_increment
           raw_insert_concrete_heap_effect[OF rel fresh]])

theorem raw_vListInsertEnd_general_refines_via_transformer:
  assumes rel:
    "raw_xlist_rel (hrs_mem (t_hrs_' s)) lp xs"
    and fresh: "raw_fresh_for_insert lp (ring xs) p"
    and can_increment: "raw_count_can_increment xs"
  shows
    "vListInsertEnd' lp p \<bullet> s
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       raw_xlist_rel (hrs_mem (t_hrs_' t)) lp
         (list_insert_end_abs p
           (raw_key_at (hrs_mem (t_hrs_' s)) p) xs)
     \<rbrace>"
proof -
  note heap_effect = raw_vListInsertEnd_general_heap_effect[OF rel fresh]
  note post = raw_insert_concrete_heap_refines[
    OF rel fresh can_increment]
  show ?thesis
    apply (rule runs_to_weaken[OF heap_effect])
    using post by auto
qed

end
