theory Scheduler_Ordered_Insert_General_Refinement
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Ordered_Insert_General_Source.Scheduler_Ordered_Insert_General_Source"
    "EAL6_FreeRTOS_V611_List_Raw_R6_Splice.List_V611_Raw_R6_Splice"
    "EAL6_FreeRTOS_V611_List_Raw_R6_Insert_Post_Transformer.List_V611_Raw_R6_Insert_Post_Transformer"
begin

text \<open>
  Universal post-refinement for the non-specialised ordered-insertion
  transformer.  The prefix is computed from the actual item key and the
  complete pre-ring; no ring length, key, insertion point, task, or scheduler
  priority is fixed here.
\<close>

lemma raw_path_edges_boundary:
  "(last (start # before), hd (after @ [finish])) \<in>
     set (raw_path_edges start (before @ after) finish)"
proof (induction before arbitrary: start)
  case Nil
  have first:
    "(start, hd (after @ [finish])) \<in>
       set (raw_path_edges start after finish)"
    by (rule raw_path_edges_first)
  show ?case using first by simp
next
  case (Cons x xs)
  have tail:
    "(last (x # xs), hd (after @ [finish])) \<in>
       set (raw_path_edges x (xs @ after) finish)"
    by (rule Cons.IH)
  show ?case using tail by simp
qed

lemma raw_ring_links_boundary:
  assumes links: "raw_ring_links h lp (before @ after)"
  shows
    "raw_next_at h lp (last (raw_end_item lp # before)) =
       hd (after @ [raw_end_item lp]) \<and>
     raw_prev_at h lp (hd (after @ [raw_end_item lp])) =
       last (raw_end_item lp # before)"
proof -
  have path:
    "list_all
      (\<lambda>(u, v). raw_next_at h lp u = v \<and> raw_prev_at h lp v = u)
      (raw_path_edges (raw_end_item lp) (before @ after)
        (raw_end_item lp))"
    using links by (simp add: raw_ring_links_path_iff)
  have edge:
    "(last (raw_end_item lp # before),
       hd (after @ [raw_end_item lp])) \<in>
      set (raw_path_edges (raw_end_item lp) (before @ after)
        (raw_end_item lp))"
    by (rule raw_path_edges_boundary)
  show ?thesis using path edge by (auto simp: list_all_iff)
qed

lemma ordered_scan_prefix_fun_upd_fresh:
  assumes fresh: "p \<notin> set rs"
  shows
    "ordered_scan_prefix (key(p := k)) k rs =
       ordered_scan_prefix key k rs"
  using fresh
proof (induction rs)
  case Nil
  show ?case by (simp add: ordered_scan_prefix_def)
next
  case (Cons x rs)
  have p_ne: "p \<noteq> x" and tail_fresh: "p \<notin> set rs"
    using Cons.prems by auto
  have tail:
    "ordered_scan_prefix (key(p := k)) k rs =
     ordered_scan_prefix key k rs"
    by (rule Cons.IH[OF tail_fresh])
  show ?case using p_ne tail by (simp add: ordered_scan_prefix_def)
qed

lemma ordered_scan_suffix_fun_upd_fresh:
  assumes fresh: "p \<notin> set rs"
  shows
    "ordered_scan_suffix (key(p := k)) k rs =
       ordered_scan_suffix key k rs"
  using fresh
proof (induction rs)
  case Nil
  show ?case by (simp add: ordered_scan_suffix_def)
next
  case (Cons x rs)
  have p_ne: "p \<noteq> x" and tail_fresh: "p \<notin> set rs"
    using Cons.prems by auto
  have tail:
    "ordered_scan_suffix (key(p := k)) k rs =
     ordered_scan_suffix key k rs"
    by (rule Cons.IH[OF tail_fresh])
  show ?case using p_ne tail by (simp add: ordered_scan_suffix_def)
qed

lemma raw_cycle_previous_heap_sentinel_key_frame:
  assumes layout: "raw_xlist_layout lp rs"
    and writer: "u \<in> insert (raw_end_item lp) (set rs)"
  shows
    "raw_key_at (raw_insert_previous_heap h u v) (raw_end_item lp) =
       raw_key_at h (raw_end_item lp)"
proof (cases "u = raw_end_item lp")
  case True
  have guard: "c_guard u"
    using layout writer by (auto simp: raw_xlist_layout_def)
  show ?thesis
    unfolding raw_insert_previous_heap_def
    using raw_previous_field_update_to_whole[
        OF guard, where q = v and h = h]
      guard True
    by (simp add: raw_key_at_def h_val_heap_update)
next
  case False
  have live: "u \<in> set rs" using writer False by simp
  have disjoint:
    "raw_pointer_field_region (raw_previous_field_ptr u) \<inter>
       raw_list_region lp = {}"
  proof -
    have item_disjoint: "raw_item_region u \<inter> raw_list_region lp = {}"
      using layout live by (auto simp: raw_xlist_layout_def)
    show ?thesis
      using raw_previous_field_region_subset_item[where u = u]
        item_disjoint by blast
  qed
  have list_same:
    "h_val (raw_insert_previous_heap h u v) lp = h_val h lp"
    unfolding raw_insert_previous_heap_def
    by (rule raw_pointer_field_update_preserves_disjoint_list[OF disjoint])
  show ?thesis by (rule raw_ordered_sentinel_key_cong[OF list_same])
qed

lemma raw_cycle_next_heap_sentinel_key_frame:
  assumes layout: "raw_xlist_layout lp rs"
    and writer: "u \<in> insert (raw_end_item lp) (set rs)"
  shows
    "raw_key_at (raw_insert_next_heap h u v) (raw_end_item lp) =
       raw_key_at h (raw_end_item lp)"
proof (cases "u = raw_end_item lp")
  case True
  have guard: "c_guard u"
    using layout writer by (auto simp: raw_xlist_layout_def)
  show ?thesis
    unfolding raw_insert_next_heap_def
    using raw_next_field_update_to_whole[OF guard, where q = v and h = h]
      guard True
    by (simp add: raw_key_at_def h_val_heap_update)
next
  case False
  have live: "u \<in> set rs" using writer False by simp
  have disjoint:
    "raw_pointer_field_region (raw_next_field_ptr u) \<inter>
       raw_list_region lp = {}"
  proof -
    have item_disjoint: "raw_item_region u \<inter> raw_list_region lp = {}"
      using layout live by (auto simp: raw_xlist_layout_def)
    show ?thesis
      using raw_next_field_region_subset_item[where u = u]
        item_disjoint by blast
  qed
  have list_same:
    "h_val (raw_insert_next_heap h u v) lp = h_val h lp"
    unfolding raw_insert_next_heap_def
    by (rule raw_pointer_field_update_preserves_disjoint_list[OF disjoint])
  show ?thesis by (rule raw_ordered_sentinel_key_cong[OF list_same])
qed

lemma raw_ordered_insert_general_link_prefix_ring_links:
  fixes k :: raw_key
    and before after :: "raw_node_id list"
    and c q :: raw_node_id
    and h1 h2 h3 h4 :: heap_mem
  assumes rel: "raw_xlist_rel h lp xs"
    and fresh: "raw_fresh_for_insert lp (ring xs) p"
  defines
    "k \<equiv> raw_key_at h p"
    and "before \<equiv> ordered_scan_prefix (item_key xs) k (ring xs)"
    and "after \<equiv> ordered_scan_suffix (item_key xs) k (ring xs)"
    and "c \<equiv> last (raw_end_item lp # before)"
    and "q \<equiv> raw_next_at h lp c"
    and "h1 \<equiv> raw_insert_next_heap h p q"
    and "h2 \<equiv> raw_insert_previous_heap h1 q p"
    and "h3 \<equiv> raw_insert_previous_heap h2 p c"
    and "h4 \<equiv> raw_insert_next_heap h3 c p"
  shows "raw_ring_links h4 lp (before @ p # after)"
proof -
  let ?cycle = "insert (raw_end_item lp) (set (ring xs))"
  have split: "before @ after = ring xs"
    unfolding before_def after_def
    by (rule ordered_scan_prefix_suffix)
  have layout: "raw_xlist_layout lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def)
  have links: "raw_ring_links h lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have split_links: "raw_ring_links h lp (before @ after)"
    using links split by simp
  have distinct_cycle: "distinct (raw_end_item lp # (before @ after))"
    using raw_xlist_rel_distinct_cycle_nodes[OF rel] split by simp
  have c_cycle: "c \<in> ?cycle"
    unfolding c_def before_def by (rule ordered_scan_predecessor_in_cycle)
  have q_cycle: "q \<in> ?cycle"
    unfolding q_def by (rule raw_ring_links_next_closed[OF links c_cycle])
  have boundary:
    "q = hd (after @ [raw_end_item lp])"
    unfolding q_def c_def
    using raw_ring_links_boundary[OF split_links] by simp
  have p_guard: "c_guard p"
    using fresh by (simp add: raw_fresh_for_insert_def)
  have c_guard: "c_guard c"
    by (rule raw_xlist_rel_cycle_node_guard[OF rel c_cycle])
  have q_guard: "c_guard q"
    by (rule raw_xlist_rel_cycle_node_guard[OF rel q_cycle])
  have p_not_cycle: "p \<notin> ?cycle"
    using fresh by (simp add: raw_fresh_for_insert_def)
  have p_ne_end: "p \<noteq> raw_end_item lp"
    using fresh by (simp add: raw_fresh_for_insert_def)

  have h1_next: "raw_next_at h1 lp p = q"
    unfolding h1_def raw_insert_next_heap_def
    by (rule raw_next_at_after_same_node_next_field_update[OF p_guard])
  have h2_p_same: "h_val h2 p = h_val h1 p"
    unfolding h2_def
    by (rule raw_cycle_previous_heap_preserves_fresh_item[OF fresh q_cycle])
  have h3_next: "raw_next_at h3 lp p = q"
  proof -
    have h2_next: "raw_next_at h2 lp p = q"
      using h2_p_same h1_next p_ne_end by (simp add: raw_next_at_def)
    show ?thesis
      unfolding h3_def raw_insert_previous_heap_def
      using raw_next_at_survives_same_node_previous_field_update[
          OF p_guard, where q = c and h = h2 and lp = lp]
        h2_next by simp
  qed
  have h3_previous: "raw_prev_at h3 lp p = c"
    unfolding h3_def raw_insert_previous_heap_def
    by (rule raw_prev_at_after_same_node_previous_field_update[OF p_guard])
  have h4_p_same: "h_val h4 p = h_val h3 p"
    unfolding h4_def
    by (rule raw_cycle_next_heap_preserves_fresh_item[OF fresh c_cycle])
  have exit_next: "raw_next_at h4 lp p = hd (after @ [raw_end_item lp])"
    using h4_p_same h3_next p_ne_end boundary
    by (simp add: raw_next_at_def)
  have entry_previous: "raw_prev_at h4 lp p = c"
    using h4_p_same h3_previous p_ne_end by (simp add: raw_prev_at_def)

  have h2_q_previous: "raw_prev_at h2 lp q = p"
    unfolding h2_def raw_insert_previous_heap_def
    by (rule raw_prev_at_after_same_node_previous_field_update[OF q_guard])
  have h3_q_previous: "raw_prev_at h3 lp q = p"
  proof -
    have obs:
      "raw_next_at h3 lp q = raw_next_at h2 lp q \<and>
       raw_prev_at h3 lp q = raw_prev_at h2 lp q"
      unfolding h3_def
      by (rule raw_fresh_previous_heap_preserves_cycle_observations[
            OF fresh q_cycle])
    show ?thesis using obs h2_q_previous by simp
  qed
  have exit_previous:
    "raw_prev_at h4 lp (hd (after @ [raw_end_item lp])) = p"
  proof -
    have frame: "raw_prev_at h4 lp q = raw_prev_at h3 lp q"
      unfolding h4_def
      by (rule raw_cycle_next_heap_previous_frame[OF layout c_cycle q_cycle])
    show ?thesis using frame h3_q_previous boundary by simp
  qed
  have entry_next: "raw_next_at h4 lp c = p"
    unfolding h4_def raw_insert_next_heap_def
    by (rule raw_next_at_after_same_node_next_field_update[OF c_guard])

  have prefix_observations:
    "\<And>u. u \<in> ?cycle \<Longrightarrow>
      raw_next_at h3 lp u = raw_next_at h lp u \<and>
      (u \<noteq> q \<longrightarrow> raw_prev_at h3 lp u = raw_prev_at h lp u)"
  proof -
    fix u
    assume u_cycle: "u \<in> ?cycle"
    have first:
      "raw_next_at h1 lp u = raw_next_at h lp u \<and>
       raw_prev_at h1 lp u = raw_prev_at h lp u"
      unfolding h1_def
      by (rule raw_fresh_next_heap_preserves_cycle_observations[OF fresh u_cycle])
    have h2_next: "raw_next_at h2 lp u = raw_next_at h1 lp u"
      unfolding h2_def
      by (rule raw_cycle_previous_heap_next_frame[OF layout q_cycle u_cycle])
    have h2_previous:
      "u \<noteq> q \<Longrightarrow> raw_prev_at h2 lp u = raw_prev_at h1 lp u"
      unfolding h2_def
      by (rule raw_cycle_previous_heap_previous_frame[OF layout q_cycle u_cycle])
    have third:
      "raw_next_at h3 lp u = raw_next_at h2 lp u \<and>
       raw_prev_at h3 lp u = raw_prev_at h2 lp u"
      unfolding h3_def
      by (rule raw_fresh_previous_heap_preserves_cycle_observations[OF fresh u_cycle])
    show
      "raw_next_at h3 lp u = raw_next_at h lp u \<and>
       (u \<noteq> q \<longrightarrow> raw_prev_at h3 lp u = raw_prev_at h lp u)"
    proof
      show "raw_next_at h3 lp u = raw_next_at h lp u"
        using first h2_next third by simp
      show
        "u \<noteq> q \<longrightarrow>
         raw_prev_at h3 lp u = raw_prev_at h lp u"
      proof
        assume u_ne_q: "u \<noteq> q"
        have second_previous:
          "raw_prev_at h2 lp u = raw_prev_at h1 lp u"
          by (rule h2_previous[OF u_ne_q])
        show "raw_prev_at h3 lp u = raw_prev_at h lp u"
          using first second_previous third by simp
      qed
    qed
  qed
  have next_frame:
    "\<And>u. u \<in> insert (raw_end_item lp) (set (before @ after)) \<Longrightarrow>
      u \<noteq> c \<Longrightarrow> raw_next_at h4 lp u = raw_next_at h lp u"
  proof -
    fix u
    assume u_split: "u \<in> insert (raw_end_item lp) (set (before @ after))"
      and u_ne_c: "u \<noteq> c"
    have u_cycle: "u \<in> ?cycle" using u_split split by simp
    have initial: "raw_next_at h3 lp u = raw_next_at h lp u"
      using prefix_observations[OF u_cycle] by simp
    have last_frame: "raw_next_at h4 lp u = raw_next_at h3 lp u"
      unfolding h4_def
      by (rule raw_cycle_next_heap_next_frame[
            OF layout c_cycle u_cycle u_ne_c])
    show "raw_next_at h4 lp u = raw_next_at h lp u"
      using initial last_frame by simp
  qed
  have previous_frame:
    "\<And>v. v \<in> insert (raw_end_item lp) (set (before @ after)) \<Longrightarrow>
      v \<noteq> hd (after @ [raw_end_item lp]) \<Longrightarrow>
      raw_prev_at h4 lp v = raw_prev_at h lp v"
  proof -
    fix v
    assume v_split: "v \<in> insert (raw_end_item lp) (set (before @ after))"
      and v_ne: "v \<noteq> hd (after @ [raw_end_item lp])"
    have v_cycle: "v \<in> ?cycle" using v_split split by simp
    have v_ne_q: "v \<noteq> q" using v_ne boundary by simp
    have initial: "raw_prev_at h3 lp v = raw_prev_at h lp v"
      using prefix_observations[OF v_cycle] v_ne_q by simp
    have last_frame: "raw_prev_at h4 lp v = raw_prev_at h3 lp v"
      unfolding h4_def
      by (rule raw_cycle_next_heap_previous_frame[OF layout c_cycle v_cycle])
    show "raw_prev_at h4 lp v = raw_prev_at h lp v"
      using initial last_frame by simp
  qed
  show ?thesis
    apply (rule raw_ring_links_insert_path[OF split_links distinct_cycle])
    using entry_next entry_previous exit_next exit_previous
      next_frame previous_frame c_def
    apply simp_all
    done
qed

lemma raw_ordered_insert_general_heap_ring_links:
  assumes rel: "raw_xlist_rel h lp xs"
    and fresh: "raw_fresh_for_insert lp (ring xs) p"
  shows
    "raw_ring_links (raw_ordered_insert_general_heap h lp xs p) lp
       (ring (list_insert_ordered_abs p (raw_key_at h p) xs))"
proof -
  let ?k = "raw_key_at h p"
  let ?before = "ordered_scan_prefix (item_key xs) ?k (ring xs)"
  let ?after = "ordered_scan_suffix (item_key xs) ?k (ring xs)"
  let ?c = "last (raw_end_item lp # ?before)"
  let ?q = "raw_next_at h lp ?c"
  let ?h1 = "raw_insert_next_heap h p ?q"
  let ?h2 = "raw_insert_previous_heap ?h1 ?q p"
  let ?h3 = "raw_insert_previous_heap ?h2 p ?c"
  let ?h4 = "raw_insert_next_heap ?h3 ?c p"
  let ?h5 = "raw_insert_container_heap ?h4 lp p"
  let ?ys = "list_insert_ordered_abs p ?k xs"
  have old_wf: "xlist_wf xs"
    using rel by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have old_layout: "raw_xlist_layout lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def)
  have new_ring: "ring ?ys = ?before @ p # ?after"
  proof -
    have p_fresh: "p \<notin> set (ring xs)"
      using fresh by (simp add: raw_fresh_for_insert_def)
    have prefix:
      "ordered_scan_prefix ((item_key xs)(p := ?k)) ?k (ring xs) =
       ?before"
      by (rule ordered_scan_prefix_fun_upd_fresh[OF p_fresh])
    have suffix:
      "ordered_scan_suffix ((item_key xs)(p := ?k)) ?k (ring xs) =
       ?after"
      by (rule ordered_scan_suffix_fun_upd_fresh[OF p_fresh])
    show ?thesis
      using stable_key_insert_take_drop[
          where key = "(item_key xs)(p := ?k)" and x = p and xs = "ring xs"]
        prefix suffix
      by (simp add: list_insert_ordered_abs_def)
  qed
  have split: "?before @ ?after = ring xs"
    by (rule ordered_scan_prefix_suffix)
  have set_split:
    "set ?before \<union> set ?after = set (ring xs)"
  proof -
    have "set (?before @ ?after) = set (ring xs)"
      by (rule arg_cong[OF split])
    then show ?thesis by simp
  qed
  have set_eq: "set (ring ?ys) = insert p (set (ring xs))"
  proof -
    have
      "set (ring ?ys) =
       set ?before \<union> insert p (set ?after)"
      using new_ring by simp
    then show ?thesis using set_split by blast
  qed
  have new_layout: "raw_xlist_layout lp (ring ?ys)"
    by (rule raw_xlist_layout_extend_set[OF old_layout fresh set_eq])
  have p_member: "p \<in> set (ring ?ys)" using set_eq by simp
  have prefix_links: "raw_ring_links ?h4 lp (?before @ p # ?after)"
    by (rule raw_ordered_insert_general_link_prefix_ring_links[OF rel fresh])
  have links4: "raw_ring_links ?h4 lp (ring ?ys)"
    using prefix_links new_ring by simp
  have links5: "raw_ring_links ?h5 lp (ring ?ys)"
    unfolding raw_insert_container_heap_def
    by (rule raw_ring_links_survives_container_update[
          OF new_layout p_member links4])
  have links6:
    "raw_ring_links (raw_insert_count_heap ?h5 lp) lp (ring ?ys)"
    unfolding raw_insert_count_heap_def
    by (rule raw_ring_links_survives_count_update[OF new_layout links5])
  show ?thesis
    using links6 by (simp add: raw_ordered_insert_general_heap_def Let_def)
qed

lemma raw_insert_previous_heap_same_node_key_frame:
  assumes guard: "c_guard p"
  shows
    "raw_key_at (raw_insert_previous_heap h p c) p = raw_key_at h p"
proof -
  have whole:
    "raw_insert_previous_heap h p c =
     heap_update p
       (xLIST_ITEM_C.pxPrevious_C_update (\<lambda>_. c) (h_val h p)) h"
    unfolding raw_insert_previous_heap_def
    by (rule raw_previous_field_update_to_whole[OF guard])
  show ?thesis
    using whole guard by (simp add: raw_key_at_def h_val_heap_update)
qed

lemma raw_ordered_insert_general_heap_new_payload_effect:
  assumes rel: "raw_xlist_rel h lp xs"
    and fresh: "raw_fresh_for_insert lp (ring xs) p"
  shows
    "raw_key_at (raw_ordered_insert_general_heap h lp xs p) p =
       raw_key_at h p \<and>
     pvContainer_C
       (h_val (raw_ordered_insert_general_heap h lp xs p) p) =
       PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
proof -
  let ?k = "raw_key_at h p"
  let ?before = "ordered_scan_prefix (item_key xs) ?k (ring xs)"
  let ?c = "last (raw_end_item lp # ?before)"
  let ?q = "raw_next_at h lp ?c"
  let ?h1 = "raw_insert_next_heap h p ?q"
  let ?h2 = "raw_insert_previous_heap ?h1 ?q p"
  let ?h3 = "raw_insert_previous_heap ?h2 p ?c"
  let ?h4 = "raw_insert_next_heap ?h3 ?c p"
  let ?h5 = "raw_insert_container_heap ?h4 lp p"
  have layout: "raw_xlist_layout lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def)
  have links: "raw_ring_links h lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have c_cycle: "?c \<in> insert (raw_end_item lp) (set (ring xs))"
    by (rule ordered_scan_predecessor_in_cycle)
  have q_cycle: "?q \<in> insert (raw_end_item lp) (set (ring xs))"
    by (rule raw_ring_links_next_closed[OF links c_cycle])
  have p_guard: "c_guard p"
    using fresh by (simp add: raw_fresh_for_insert_def)
  have h1_key: "raw_key_at ?h1 p = raw_key_at h p"
    unfolding raw_insert_next_heap_def
    using raw_next_field_update_to_whole[
        OF p_guard, where q = ?q and h = h]
      p_guard
    by (simp add: raw_key_at_def h_val_heap_update)
  have h2_item: "h_val ?h2 p = h_val ?h1 p"
    by (rule raw_cycle_previous_heap_preserves_fresh_item[OF fresh q_cycle])
  have h3_key: "raw_key_at ?h3 p = raw_key_at ?h2 p"
    by (rule raw_insert_previous_heap_same_node_key_frame[OF p_guard])
  have h4_item: "h_val ?h4 p = h_val ?h3 p"
    by (rule raw_cycle_next_heap_preserves_fresh_item[OF fresh c_cycle])
  have h5_payload:
    "raw_key_at ?h5 p = raw_key_at ?h4 p \<and>
     pvContainer_C (h_val ?h5 p) =
       PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
    unfolding raw_insert_container_heap_def
    using p_guard by (simp add: raw_key_at_def h_val_heap_update)
  have h6_item:
    "h_val (raw_insert_count_heap ?h5 lp) p = h_val ?h5 p"
    unfolding raw_insert_count_heap_def
    by (rule raw_list_update_preserves_fresh_item[OF fresh])
  show ?thesis
    using h1_key h2_item h3_key h4_item h5_payload h6_item
    by (simp add: raw_ordered_insert_general_heap_def raw_key_at_def Let_def)
qed

lemma raw_ordered_insert_general_heap_old_payload_frame:
  assumes rel: "raw_xlist_rel h lp xs"
    and fresh: "raw_fresh_for_insert lp (ring xs) p"
    and live: "q0 \<in> set (ring xs)"
  shows
    "raw_key_at (raw_ordered_insert_general_heap h lp xs p) q0 =
       raw_key_at h q0 \<and>
     pvContainer_C
       (h_val (raw_ordered_insert_general_heap h lp xs p) q0) =
       pvContainer_C (h_val h q0)"
proof -
  let ?k = "raw_key_at h p"
  let ?before = "ordered_scan_prefix (item_key xs) ?k (ring xs)"
  let ?c = "last (raw_end_item lp # ?before)"
  let ?q = "raw_next_at h lp ?c"
  let ?h1 = "raw_insert_next_heap h p ?q"
  let ?h2 = "raw_insert_previous_heap ?h1 ?q p"
  let ?h3 = "raw_insert_previous_heap ?h2 p ?c"
  let ?h4 = "raw_insert_next_heap ?h3 ?c p"
  let ?h5 = "raw_insert_container_heap ?h4 lp p"
  have layout: "raw_xlist_layout lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def)
  have links: "raw_ring_links h lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have c_cycle: "?c \<in> insert (raw_end_item lp) (set (ring xs))"
    by (rule ordered_scan_predecessor_in_cycle)
  have q_cycle: "?q \<in> insert (raw_end_item lp) (set (ring xs))"
    by (rule raw_ring_links_next_closed[OF links c_cycle])
  have h1_item: "h_val ?h1 q0 = h_val h q0"
    by (rule raw_fresh_next_heap_preserves_old_item[OF fresh live])
  have h2_payload:
    "raw_key_at ?h2 q0 = raw_key_at ?h1 q0 \<and>
     pvContainer_C (h_val ?h2 q0) = pvContainer_C (h_val ?h1 q0)"
    unfolding raw_insert_previous_heap_def
    by (rule
      List_V611_Raw_R6_Remove_Payload_Effect.raw_cycle_previous_field_update_preserves_payload[
        OF layout q_cycle live])
  have h3_item: "h_val ?h3 q0 = h_val ?h2 q0"
    by (rule raw_fresh_previous_heap_preserves_old_item[OF fresh live])
  have h4_payload:
    "raw_key_at ?h4 q0 = raw_key_at ?h3 q0 \<and>
     pvContainer_C (h_val ?h4 q0) = pvContainer_C (h_val ?h3 q0)"
    unfolding raw_insert_next_heap_def
    by (rule
      List_V611_Raw_R6_Remove_Payload_Effect.raw_cycle_next_field_update_preserves_payload[
        OF layout c_cycle live])
  have item_disjoint: "raw_item_region p \<inter> raw_item_region q0 = {}"
    using fresh live by (simp add: raw_fresh_for_insert_def)
  have h5_item: "h_val ?h5 q0 = h_val ?h4 q0"
    unfolding raw_insert_container_heap_def
    by (rule raw_item_update_preserves_disjoint_item[OF item_disjoint])
  have h6_item:
    "h_val (raw_insert_count_heap ?h5 lp) q0 = h_val ?h5 q0"
    unfolding raw_insert_count_heap_def
    by (rule
      List_V611_Raw_R6_Remove_Payload_Effect.raw_layout_list_update_preserves_live_item[
        OF layout live])
  show ?thesis
    using h1_item h2_payload h3_item h4_payload h5_item h6_item
    by (simp add: raw_ordered_insert_general_heap_def raw_key_at_def Let_def)
qed

lemma raw_ordered_insert_general_heap_sentinel_key_frame:
  assumes rel: "raw_xlist_rel h lp xs"
    and fresh: "raw_fresh_for_insert lp (ring xs) p"
  shows
    "raw_key_at (raw_ordered_insert_general_heap h lp xs p)
       (raw_end_item lp) = raw_key_at h (raw_end_item lp)"
proof -
  let ?k = "raw_key_at h p"
  let ?before = "ordered_scan_prefix (item_key xs) ?k (ring xs)"
  let ?c = "last (raw_end_item lp # ?before)"
  let ?q = "raw_next_at h lp ?c"
  let ?h1 = "raw_insert_next_heap h p ?q"
  let ?h2 = "raw_insert_previous_heap ?h1 ?q p"
  let ?h3 = "raw_insert_previous_heap ?h2 p ?c"
  let ?h4 = "raw_insert_next_heap ?h3 ?c p"
  let ?h5 = "raw_insert_container_heap ?h4 lp p"
  let ?h6 = "raw_insert_count_heap ?h5 lp"
  have layout: "raw_xlist_layout lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def)
  have lp_guard: "c_guard lp"
    using layout by (simp add: raw_xlist_layout_def)
  have links: "raw_ring_links h lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have c_cycle: "?c \<in> insert (raw_end_item lp) (set (ring xs))"
    by (rule ordered_scan_predecessor_in_cycle)
  have q_cycle: "?q \<in> insert (raw_end_item lp) (set (ring xs))"
    by (rule raw_ring_links_next_closed[OF links c_cycle])
  have h1_list: "h_val ?h1 lp = h_val h lp"
    by (rule raw_insert_next_heap_preserves_list[OF fresh])
  have h1_key:
    "raw_key_at ?h1 (raw_end_item lp) = raw_key_at h (raw_end_item lp)"
    by (rule raw_ordered_sentinel_key_cong[OF h1_list])
  have h2_key:
    "raw_key_at ?h2 (raw_end_item lp) = raw_key_at ?h1 (raw_end_item lp)"
    by (rule raw_cycle_previous_heap_sentinel_key_frame[OF layout q_cycle])
  have h3_list: "h_val ?h3 lp = h_val ?h2 lp"
    by (rule raw_insert_previous_heap_preserves_list[OF fresh])
  have h3_key:
    "raw_key_at ?h3 (raw_end_item lp) = raw_key_at ?h2 (raw_end_item lp)"
    by (rule raw_ordered_sentinel_key_cong[OF h3_list])
  have h4_key:
    "raw_key_at ?h4 (raw_end_item lp) = raw_key_at ?h3 (raw_end_item lp)"
    by (rule raw_cycle_next_heap_sentinel_key_frame[OF layout c_cycle])
  have item_list: "raw_item_region p \<inter> raw_list_region lp = {}"
    using fresh by (simp add: raw_fresh_for_insert_def)
  have h5_list: "h_val ?h5 lp = h_val ?h4 lp"
    unfolding raw_insert_container_heap_def
    by (rule raw_item_update_preserves_disjoint_list[OF item_list])
  have h5_key:
    "raw_key_at ?h5 (raw_end_item lp) = raw_key_at ?h4 (raw_end_item lp)"
    by (rule raw_ordered_sentinel_key_cong[OF h5_list])
  have h6_value:
    "h_val ?h6 lp =
       uxNumberOfItems_C_update (\<lambda>n. n + 1) (h_val ?h5 lp)"
    unfolding raw_insert_count_heap_def
    using lp_guard by (simp add: h_val_heap_update)
  have h6_key:
    "raw_key_at ?h6 (raw_end_item lp) = raw_key_at ?h5 (raw_end_item lp)"
    using raw_sentinel_item_value_prefix_generic[where h = ?h6 and lp = lp]
      raw_sentinel_item_value_prefix_generic[where h = ?h5 and lp = lp]
      h6_value
    by (simp add: raw_key_at_def raw_end_item_def)
  show ?thesis
    using h1_key h2_key h3_key h4_key h5_key h6_key
    by (simp add: raw_ordered_insert_general_heap_def Let_def)
qed

definition raw_ordered_insert_general_effect ::
  "heap_mem \<Rightarrow> heap_mem \<Rightarrow> xLIST_C ptr \<Rightarrow>
   (raw_node_id, raw_key) xlist_abs \<Rightarrow> raw_node_id \<Rightarrow> bool"
where
  "raw_ordered_insert_general_effect h h' lp xs p \<longleftrightarrow>
     uxNumberOfItems_C (h_val h' lp) =
       uxNumberOfItems_C (h_val h lp) + 1 \<and>
     pxIndex_C (h_val h' lp) = pxIndex_C (h_val h lp) \<and>
     raw_ring_links h' lp
       (ring (list_insert_ordered_abs p (raw_key_at h p) xs)) \<and>
     raw_key_at h' p = raw_key_at h p \<and>
     pvContainer_C (h_val h' p) =
       PTR_COERCE(xLIST_C \<rightarrow> unit) lp \<and>
     (\<forall>q \<in> set (ring xs).
        raw_key_at h' q = raw_key_at h q \<and>
        pvContainer_C (h_val h' q) = pvContainer_C (h_val h q)) \<and>
     raw_key_at h' (raw_end_item lp) =
       raw_key_at h (raw_end_item lp)"

theorem raw_ordered_insert_general_transformer_effect:
  assumes rel: "raw_xlist_rel h lp xs"
    and fresh: "raw_fresh_for_insert lp (ring xs) p"
  shows
    "raw_ordered_insert_general_effect h
       (raw_ordered_insert_general_heap h lp xs p) lp xs p"
proof -
  have count:
    "uxNumberOfItems_C
       (h_val (raw_ordered_insert_general_heap h lp xs p) lp) =
     uxNumberOfItems_C (h_val h lp) + 1"
    by (rule raw_ordered_insert_general_heap_count_effect[OF rel fresh])
  have index:
    "pxIndex_C
       (h_val (raw_ordered_insert_general_heap h lp xs p) lp) =
     pxIndex_C (h_val h lp)"
    by (rule raw_ordered_insert_general_heap_index_effect[OF rel fresh])
  have links:
    "raw_ring_links (raw_ordered_insert_general_heap h lp xs p) lp
       (ring (list_insert_ordered_abs p (raw_key_at h p) xs))"
    by (rule raw_ordered_insert_general_heap_ring_links[OF rel fresh])
  have payload:
    "raw_key_at (raw_ordered_insert_general_heap h lp xs p) p =
       raw_key_at h p \<and>
     pvContainer_C
       (h_val (raw_ordered_insert_general_heap h lp xs p) p) =
       PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
    by (rule raw_ordered_insert_general_heap_new_payload_effect[OF rel fresh])
  have old_frame:
    "\<forall>q \<in> set (ring xs).
       raw_key_at (raw_ordered_insert_general_heap h lp xs p) q =
         raw_key_at h q \<and>
       pvContainer_C
         (h_val (raw_ordered_insert_general_heap h lp xs p) q) =
         pvContainer_C (h_val h q)"
    by (intro ballI raw_ordered_insert_general_heap_old_payload_frame[
          OF rel fresh])
  have sentinel:
    "raw_key_at (raw_ordered_insert_general_heap h lp xs p)
       (raw_end_item lp) = raw_key_at h (raw_end_item lp)"
    by (rule raw_ordered_insert_general_heap_sentinel_key_frame[OF rel fresh])
  show ?thesis
    using count index links payload old_frame sentinel
    by (simp add: raw_ordered_insert_general_effect_def)
qed

lemma length_stable_key_insert_general[simp]:
  "length (stable_key_insert key p rs) = Suc (length rs)"
  by (induction rs) auto

lemma map_fun_upd_fresh:
  assumes fresh: "p \<notin> set rs"
  shows "map (key(p := k)) rs = map key rs"
  using fresh
proof (induction rs)
  case Nil
  show ?case by simp
next
  case (Cons x rs)
  have x_ne_p: "x \<noteq> p" and tail_fresh: "p \<notin> set rs"
    using Cons.prems by auto
  have tail: "map (key(p := k)) rs = map key rs"
    by (rule Cons.IH[OF tail_fresh])
  show ?case using x_ne_p tail by simp
qed

lemma list_insert_ordered_ring_set[simp]:
  "set (ring (list_insert_ordered_abs p k xs)) =
   insert p (set (ring xs))"
  unfolding list_insert_ordered_abs_def Let_def
  by simp

lemma list_insert_ordered_ring_length[simp]:
  "length (ring (list_insert_ordered_abs p k xs)) =
   Suc (length (ring xs))"
  unfolding list_insert_ordered_abs_def Let_def
  by simp

lemma raw_xlist_ordered_insert_count_transfer:
  assumes rel: "raw_xlist_rel h lp xs"
    and can_increment: "raw_count_can_increment xs"
    and count_word:
      "uxNumberOfItems_C (h_val h' lp) =
       uxNumberOfItems_C (h_val h lp) + 1"
  shows
    "unat (uxNumberOfItems_C (h_val h' lp)) =
     length (ring (list_insert_ordered_abs p k xs))"
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
  have successor: "unat (?n + 1) = Suc (unat ?n)"
    using old_not_max by (metis add.commute max_word_wrap unatSuc)
  show ?thesis using count_word successor old_count by simp
qed

lemma raw_xlist_ordered_insert_cursor_transfer:
  assumes rel: "raw_xlist_rel h lp xs"
    and index:
      "pxIndex_C (h_val h' lp) = pxIndex_C (h_val h lp)"
  shows
    "raw_cursor_at h' lp = cursor (list_insert_ordered_abs p k xs)"
proof -
  have old_cursor: "cursor xs = raw_cursor_at h lp"
    by (rule raw_xlist_rel_cursorD[OF rel])
  have raw_same: "raw_cursor_at h' lp = raw_cursor_at h lp"
    using index by (simp add: raw_cursor_at_def)
  show ?thesis
    using old_cursor raw_same
    by (simp add: list_insert_ordered_abs_def Let_def)
qed

lemma raw_ordered_insert_general_effect_refines:
  assumes ordered: "raw_ordered_xlist_rel h lp xs"
    and fresh: "raw_fresh_for_insert lp (ring xs) p"
    and can_increment: "raw_count_can_increment xs"
    and effect: "raw_ordered_insert_general_effect h h' lp xs p"
  shows
    "raw_ordered_xlist_rel h' lp
       (list_insert_ordered_abs p (raw_key_at h p) xs)"
proof -
  let ?k = "raw_key_at h p"
  let ?ys = "list_insert_ordered_abs p ?k xs"
  have rel: "raw_xlist_rel h lp xs"
    using ordered by (simp add: raw_ordered_xlist_rel_def)
  have old_sentinel: "raw_sentinel_max h lp"
    using ordered by (simp add: raw_ordered_xlist_rel_def)
  have old_sorted: "sorted (map (item_key xs) (ring xs))"
    using ordered by (simp add: raw_ordered_xlist_rel_def)
  have old_wf: "xlist_wf xs"
    using rel by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have p_fresh: "p \<notin> set (ring xs)"
    using fresh by (simp add: raw_fresh_for_insert_def)
  have new_wf: "xlist_wf ?ys"
    by (rule list_insert_ordered_preserves_wf[OF old_wf p_fresh])
  have set_eq: "set (ring ?ys) = insert p (set (ring xs))"
    by (rule list_insert_ordered_ring_set)
  have old_layout: "raw_xlist_layout lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def)
  have new_layout: "raw_xlist_layout lp (ring ?ys)"
    by (rule raw_xlist_layout_extend_set[OF old_layout fresh set_eq])
  have count_word:
    "uxNumberOfItems_C (h_val h' lp) =
     uxNumberOfItems_C (h_val h lp) + 1"
    using effect by (simp add: raw_ordered_insert_general_effect_def)
  have count:
    "unat (uxNumberOfItems_C (h_val h' lp)) = length (ring ?ys)"
    by (rule raw_xlist_ordered_insert_count_transfer[
          OF rel can_increment count_word])
  have index:
    "pxIndex_C (h_val h' lp) = pxIndex_C (h_val h lp)"
    using effect by (simp add: raw_ordered_insert_general_effect_def)
  have cursor: "raw_cursor_at h' lp = cursor ?ys"
    by (rule raw_xlist_ordered_insert_cursor_transfer[OF rel index])
  have links: "raw_ring_links h' lp (ring ?ys)"
    using effect by (simp add: raw_ordered_insert_general_effect_def)
  have new_key: "raw_key_at h' p = ?k"
    using effect by (simp add: raw_ordered_insert_general_effect_def)
  have new_container:
    "pvContainer_C (h_val h' p) = PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
    using effect by (simp add: raw_ordered_insert_general_effect_def)
  have old_frame:
    "\<And>q. q \<in> set (ring xs) \<Longrightarrow>
      raw_key_at h' q = raw_key_at h q \<and>
      pvContainer_C (h_val h' q) = pvContainer_C (h_val h q)"
    using effect by (auto simp: raw_ordered_insert_general_effect_def)
  have live:
    "\<forall>q \<in> set (ring ?ys).
       item_key ?ys q = raw_key_at h' q \<and>
       pvContainer_C (h_val h' q) = PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
  proof (intro ballI)
    fix q
    assume q_new: "q \<in> set (ring ?ys)"
    have cases: "q = p \<or> q \<in> set (ring xs)"
      using q_new set_eq by simp
    then show
      "item_key ?ys q = raw_key_at h' q \<and>
       pvContainer_C (h_val h' q) = PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
    proof
      assume "q = p"
      then show ?thesis
        using new_key new_container
        by (simp add: list_insert_ordered_abs_def Let_def)
    next
      assume q_old: "q \<in> set (ring xs)"
      have q_ne: "q \<noteq> p" using p_fresh q_old by auto
      have old_live:
        "item_key xs q = raw_key_at h q \<and>
         pvContainer_C (h_val h q) = PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
        by (rule raw_xlist_rel_live_itemD[OF rel q_old])
      have frame:
        "raw_key_at h' q = raw_key_at h q \<and>
         pvContainer_C (h_val h' q) = pvContainer_C (h_val h q)"
        by (rule old_frame[OF q_old])
      show ?thesis
        using q_ne old_live frame
        by (simp add: list_insert_ordered_abs_def Let_def)
    qed
  qed
  have raw_rel: "raw_xlist_rel h' lp ?ys"
    unfolding raw_xlist_rel_def raw_xlist_view_def
    using new_layout new_wf count cursor links live by simp
  have sentinel_frame:
    "raw_key_at h' (raw_end_item lp) = raw_key_at h (raw_end_item lp)"
    using effect by (simp add: raw_ordered_insert_general_effect_def)
  have new_sentinel: "raw_sentinel_max h' lp"
    using old_sentinel sentinel_frame by (simp add: raw_sentinel_max_def)
  have updated_old_sorted:
    "sorted (map ((item_key xs)(p := ?k)) (ring xs))"
  proof -
    have map_eq:
      "map ((item_key xs)(p := ?k)) (ring xs) =
       map (item_key xs) (ring xs)"
      by (rule map_fun_upd_fresh[OF p_fresh])
    show ?thesis
      apply (subst map_eq)
      by (rule old_sorted)
  qed
  have new_sorted: "sorted (map (item_key ?ys) (ring ?ys))"
    by (rule list_insert_ordered_is_sorted[OF updated_old_sorted])
  show ?thesis
    using raw_rel new_sentinel new_sorted
    by (simp add: raw_ordered_xlist_rel_def)
qed

theorem raw_ordered_insert_general_transformer_refines:
  assumes ordered: "raw_ordered_xlist_rel h lp xs"
    and fresh: "raw_fresh_for_insert lp (ring xs) p"
    and can_increment: "raw_count_can_increment xs"
  shows
    "raw_ordered_xlist_rel
       (raw_ordered_insert_general_heap h lp xs p) lp
       (list_insert_ordered_abs p (raw_key_at h p) xs)"
proof -
  have rel: "raw_xlist_rel h lp xs"
    using ordered by (simp add: raw_ordered_xlist_rel_def)
  have effect:
    "raw_ordered_insert_general_effect h
       (raw_ordered_insert_general_heap h lp xs p) lp xs p"
    by (rule raw_ordered_insert_general_transformer_effect[OF rel fresh])
  show ?thesis
    by (rule raw_ordered_insert_general_effect_refines[
          OF ordered fresh can_increment effect])
qed

definition raw_ordered_insert_general_write_footprint ::
  "heap_mem \<Rightarrow> xLIST_C ptr \<Rightarrow>
   (raw_node_id, raw_key) xlist_abs \<Rightarrow> raw_node_id \<Rightarrow> addr set"
where
  "raw_ordered_insert_general_write_footprint h lp xs p =
     (let k = raw_key_at h p;
          before = ordered_scan_prefix (item_key xs) k (ring xs);
          c = last (raw_end_item lp # before);
          q = raw_next_at h lp c
      in raw_pointer_field_region (raw_next_field_ptr p) \<union>
         raw_pointer_field_region (raw_previous_field_ptr q) \<union>
         raw_pointer_field_region (raw_previous_field_ptr p) \<union>
         raw_pointer_field_region (raw_next_field_ptr c) \<union>
         raw_item_region p \<union> raw_list_region lp)"

lemma heap_update_raw_pointer_field_external_frame:
  assumes outside: "a \<notin> raw_pointer_field_region f"
  shows "heap_update f (v :: raw_node_id) h a = h a"
  unfolding heap_update_def raw_pointer_field_region_def
  apply (rule heap_update_nmem_same)
  using outside by (simp add: raw_pointer_field_region_def)

lemma heap_update_raw_item_external_frame:
  assumes outside: "a \<notin> raw_item_region p"
  shows "heap_update p (v :: xLIST_ITEM_C) h a = h a"
  unfolding heap_update_def raw_item_region_def
  apply (rule heap_update_nmem_same)
  using outside by (simp add: raw_item_region_def)

lemma heap_update_raw_list_external_frame:
  assumes outside: "a \<notin> raw_list_region lp"
  shows "heap_update lp (v :: xLIST_C) h a = h a"
  unfolding heap_update_def raw_list_region_def
  apply (rule heap_update_nmem_same)
  using outside by (simp add: raw_list_region_def)

theorem raw_ordered_insert_general_heap_external_frame:
  assumes outside:
    "a \<notin> raw_ordered_insert_general_write_footprint h lp xs p"
  shows "raw_ordered_insert_general_heap h lp xs p a = h a"
proof -
  let ?k = "raw_key_at h p"
  let ?before = "ordered_scan_prefix (item_key xs) ?k (ring xs)"
  let ?c = "last (raw_end_item lp # ?before)"
  let ?q = "raw_next_at h lp ?c"
  let ?h1 = "raw_insert_next_heap h p ?q"
  let ?h2 = "raw_insert_previous_heap ?h1 ?q p"
  let ?h3 = "raw_insert_previous_heap ?h2 p ?c"
  let ?h4 = "raw_insert_next_heap ?h3 ?c p"
  let ?h5 = "raw_insert_container_heap ?h4 lp p"
  have out_p_next:
    "a \<notin> raw_pointer_field_region (raw_next_field_ptr p)"
    using outside by (simp add: raw_ordered_insert_general_write_footprint_def Let_def)
  have out_q_previous:
    "a \<notin> raw_pointer_field_region (raw_previous_field_ptr ?q)"
    using outside by (simp add: raw_ordered_insert_general_write_footprint_def Let_def)
  have out_p_previous:
    "a \<notin> raw_pointer_field_region (raw_previous_field_ptr p)"
    using outside by (simp add: raw_ordered_insert_general_write_footprint_def Let_def)
  have out_c_next:
    "a \<notin> raw_pointer_field_region (raw_next_field_ptr ?c)"
    using outside by (simp add: raw_ordered_insert_general_write_footprint_def Let_def)
  have out_item: "a \<notin> raw_item_region p"
    using outside by (simp add: raw_ordered_insert_general_write_footprint_def Let_def)
  have out_list: "a \<notin> raw_list_region lp"
    using outside by (simp add: raw_ordered_insert_general_write_footprint_def Let_def)
  have h1: "?h1 a = h a"
    unfolding raw_insert_next_heap_def
    by (rule heap_update_raw_pointer_field_external_frame[OF out_p_next])
  have h2: "?h2 a = ?h1 a"
    unfolding raw_insert_previous_heap_def
    by (rule heap_update_raw_pointer_field_external_frame[OF out_q_previous])
  have h3: "?h3 a = ?h2 a"
    unfolding raw_insert_previous_heap_def
    by (rule heap_update_raw_pointer_field_external_frame[OF out_p_previous])
  have h4: "?h4 a = ?h3 a"
    unfolding raw_insert_next_heap_def
    by (rule heap_update_raw_pointer_field_external_frame[OF out_c_next])
  have h5: "?h5 a = ?h4 a"
    unfolding raw_insert_container_heap_def
    by (rule heap_update_raw_item_external_frame[OF out_item])
  have h6: "raw_insert_count_heap ?h5 lp a = ?h5 a"
    unfolding raw_insert_count_heap_def
    by (rule heap_update_raw_list_external_frame[OF out_list])
  show ?thesis
    using h1 h2 h3 h4 h5 h6
    by (simp add: raw_ordered_insert_general_heap_def Let_def)
qed

end
