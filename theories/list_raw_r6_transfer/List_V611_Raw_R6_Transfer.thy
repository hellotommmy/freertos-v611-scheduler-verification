theory List_V611_Raw_R6_Transfer
  imports
    "EAL6_FreeRTOS_V611_List_Raw_R6_Dynamic_Guards.List_V611_Raw_R6_Dynamic_Guards"
begin

text \<open>
  Pure transfer bricks for general-N raw rings.  This theory does not open a
  generated C body.  In particular, deletion is phrased in terms of the two
  neighbour writes and pointwise next/previous frames; predecessor and
  successor are permitted to coincide, as in the singleton cycle.
\<close>

lemma raw_xlist_layout_subset:
  assumes layout: "raw_xlist_layout lp rs"
    and subset: "set rs' \<subseteq> set rs"
  shows "raw_xlist_layout lp rs'"
  using assms
  unfolding raw_xlist_layout_def
  by blast

lemma predecessor_aux_nth_distinct:
  assumes distinct: "distinct (previous # xs)"
    and bound: "i < length xs"
  shows
    "predecessor_aux previous (xs ! i) xs =
       Some (if i = 0 then previous else xs ! (i - 1))"
  using assms
proof (induction xs arbitrary: previous i)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases i)
    case 0
    then show ?thesis by simp
  next
    case (Suc j)
    have tail_distinct: "distinct (x # xs)"
      using Cons.prems(1) by simp
    have j_bound: "j < length xs"
      using Cons.prems(2) Suc by simp
    have x_ne_target: "x \<noteq> xs ! j"
      using tail_distinct nth_mem[OF j_bound] by auto
    have ih:
      "predecessor_aux x (xs ! j) xs =
         Some (if j = 0 then x else xs ! (j - 1))"
      by (rule Cons.IH[OF tail_distinct j_bound])
    show ?thesis
      using Suc x_ne_target ih by (cases j) simp_all
  qed
qed

lemma predecessor_nth_distinct:
  assumes distinct: "distinct xs"
    and bound: "i < length xs"
  shows
    "predecessor (xs ! i) xs =
       (if i = 0 then None else Some (xs ! (i - 1)))"
proof (cases xs)
  case Nil
  with bound show ?thesis by simp
next
  case (Cons x ys)
  show ?thesis
  proof (cases i)
    case 0
    with Cons show ?thesis by simp
  next
    case (Suc j)
    have tail_distinct: "distinct (x # ys)"
      using distinct Cons by simp
    have j_bound: "j < length ys"
      using bound Cons Suc by simp
    have x_ne_target: "x \<noteq> ys ! j"
      using tail_distinct nth_mem[OF j_bound] by auto
    have aux:
      "predecessor_aux x (ys ! j) ys =
         Some (if j = 0 then x else ys ! (j - 1))"
      by (rule predecessor_aux_nth_distinct[OF tail_distinct j_bound])
    show ?thesis
      using Cons Suc x_ne_target aux by (cases j) simp_all
  qed
qed

lemma raw_ring_links_member_previous:
  assumes links: "raw_ring_links h lp rs"
    and distinct: "distinct rs"
    and member: "p \<in> set rs"
  shows
    "raw_prev_at h lp p =
       (case predecessor p rs of
          None \<Rightarrow> raw_end_item lp
        | Some q \<Rightarrow> q)"
proof -
  obtain i where bound: "i < length rs" and p: "p = rs ! i"
    using member by (auto simp: in_set_conv_nth)
  have edge:
    "raw_prev_at h lp (raw_cycle_targets lp rs ! i) =
       raw_cycle_nodes lp rs ! i"
    by (rule raw_ring_links_nth_previous[OF links], use bound in simp)
  have target: "raw_cycle_targets lp rs ! i = p"
    using bound p
    by (simp add: raw_cycle_targets_def nth_append)
  have previous:
    "raw_prev_at h lp p = raw_cycle_nodes lp rs ! i"
    using edge target by simp
  have pred:
    "predecessor p rs =
       (if i = 0 then None else Some (rs ! (i - 1)))"
    using predecessor_nth_distinct[OF distinct bound] p by simp
  show ?thesis
    using previous pred
    by (cases i) (simp_all add: raw_cycle_nodes_def)
qed

corollary raw_xlist_rel_member_previous:
  assumes rel: "raw_xlist_rel h lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "raw_prev_at h lp p =
       (case predecessor p (ring xs) of
          None \<Rightarrow> raw_end_item lp
        | Some q \<Rightarrow> q)"
proof (rule raw_ring_links_member_previous)
  show "raw_ring_links h lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  show "distinct (ring xs)"
    using rel
    by (simp add: raw_xlist_rel_def raw_xlist_view_def xlist_wf_def)
  show "p \<in> set (ring xs)" by (rule member)
qed

fun raw_path_edges ::
  "'a \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'a) list"
where
  "raw_path_edges start [] finish = [(start, finish)]"
| "raw_path_edges start (x # xs) finish =
     (start, x) # raw_path_edges x xs finish"

lemma raw_path_edges_zip:
  "raw_path_edges start xs finish =
     zip (start # xs) (xs @ [finish])"
  by (induction xs arbitrary: start) simp_all

lemma raw_path_edges_sources[simp]:
  "map fst (raw_path_edges start xs finish) = start # xs"
  by (induction xs arbitrary: start) simp_all

lemma raw_path_edges_targets[simp]:
  "map snd (raw_path_edges start xs finish) = xs @ [finish]"
  by (induction xs arbitrary: start) simp_all

lemma raw_path_edges_sourceD:
  assumes "(u, v) \<in> set (raw_path_edges start xs finish)"
  shows "u \<in> set (start # xs)"
proof -
  have image_member:
    "fst (u, v) \<in> fst ` set (raw_path_edges start xs finish)"
    by (rule imageI[OF assms])
  have "u \<in> set (map fst (raw_path_edges start xs finish))"
    using image_member by (simp only: set_map fst_conv)
  then show ?thesis by simp
qed

lemma raw_path_edges_targetD:
  assumes "(u, v) \<in> set (raw_path_edges start xs finish)"
  shows "v \<in> set (xs @ [finish])"
proof -
  have image_member:
    "snd (u, v) \<in> snd ` set (raw_path_edges start xs finish)"
    by (rule imageI[OF assms])
  have "v \<in> set (map snd (raw_path_edges start xs finish))"
    using image_member by (simp only: set_map snd_conv)
  then show ?thesis by simp
qed

lemma raw_path_edges_entry:
  "(last (start # before), p) \<in>
     set (raw_path_edges start (before @ p # after) finish)"
  by (induction before arbitrary: start) auto

lemma raw_path_edges_exit:
  "(p, hd (after @ [finish])) \<in>
     set (raw_path_edges start (before @ p # after) finish)"
  by (induction before arbitrary: start) (cases after, auto)+

lemma raw_path_edges_delete_cases:
  assumes distinct: "distinct (start # (before @ p # after))"
    and finish_fresh: "finish \<notin> set (before @ p # after)"
  shows
    "\<forall>uv \<in> set (raw_path_edges start (before @ after) finish).
       uv = (last (start # before), hd (after @ [finish])) \<or>
       (uv \<in> set (raw_path_edges start (before @ p # after) finish) \<and>
        fst uv \<noteq> last (start # before) \<and>
        snd uv \<noteq> hd (after @ [finish]))"
  using assms
proof (induction before arbitrary: start)
  case Nil
  show ?case
  proof (cases after)
    case Nil_after: Nil
    then show ?thesis by simp
  next
    case (Cons y ys)
    have start_not_source: "start \<notin> set (y # ys)"
      using Nil.prems(1) Cons by simp
    have y_not_target: "y \<notin> set (ys @ [finish])"
      using Nil.prems Cons by (auto simp: neq_commute)
    have tail_safe:
      "\<forall>uv \<in> set (raw_path_edges y ys finish).
         fst uv \<noteq> start \<and> snd uv \<noteq> y"
    proof (intro ballI conjI)
      fix uv
      assume tail: "uv \<in> set (raw_path_edges y ys finish)"
      obtain u v where uv: "uv = (u, v)"
        by (cases uv) simp
      have pair_tail: "(u, v) \<in> set (raw_path_edges y ys finish)"
        using tail uv by simp
      have source: "u \<in> set (y # ys)"
        by (rule raw_path_edges_sourceD[OF pair_tail])
      have target: "v \<in> set (ys @ [finish])"
        by (rule raw_path_edges_targetD[OF pair_tail])
      have u_ne: "u \<noteq> start"
        using source start_not_source by blast
      have v_ne: "v \<noteq> y"
        using target y_not_target by blast
      show "fst uv \<noteq> start"
        using u_ne uv by simp
      show "snd uv \<noteq> y"
        using v_ne uv by simp
    qed
    show ?thesis using tail_safe Cons by auto
  qed
next
  case (Cons x xs)
  have tail_distinct: "distinct (x # (xs @ p # after))"
    using Cons.prems(1) by simp
  have tail_finish_fresh: "finish \<notin> set (xs @ p # after)"
    using Cons.prems(2) by simp
  have ih:
    "\<forall>uv \<in> set (raw_path_edges x (xs @ after) finish).
       uv = (last (x # xs), hd (after @ [finish])) \<or>
       (uv \<in> set (raw_path_edges x (xs @ p # after) finish) \<and>
        fst uv \<noteq> last (x # xs) \<and>
        snd uv \<noteq> hd (after @ [finish]))"
    by (rule Cons.IH[OF tail_distinct tail_finish_fresh])
  have start_ne_last: "start \<noteq> last (x # xs)"
  proof -
    have "last (x # xs) \<in> set (x # xs)" by simp
    moreover have "start \<notin> set (x # xs)"
      using Cons.prems(1) by simp
    ultimately show ?thesis by blast
  qed
  have x_ne_head: "x \<noteq> hd (after @ [finish])"
    using Cons.prems by (cases after) auto
  show ?case
  proof (intro ballI)
    fix uv
    assume new:
      "uv \<in> set (raw_path_edges start ((x # xs) @ after) finish)"
    show
      "uv = (last (start # x # xs), hd (after @ [finish])) \<or>
       uv \<in> set (raw_path_edges start ((x # xs) @ p # after) finish) \<and>
       fst uv \<noteq> last (start # x # xs) \<and>
       snd uv \<noteq> hd (after @ [finish])"
    proof (cases "uv = (start, x)")
      case True
      then show ?thesis using start_ne_last x_ne_head by simp
    next
      case False
      have tail: "uv \<in> set (raw_path_edges x (xs @ after) finish)"
        using new False by simp
      have ih_case:
        "uv = (last (x # xs), hd (after @ [finish])) \<or>
         (uv \<in> set (raw_path_edges x (xs @ p # after) finish) \<and>
          fst uv \<noteq> last (x # xs) \<and>
          snd uv \<noteq> hd (after @ [finish]))"
        using ih tail by blast
      then show ?thesis by auto
    qed
  qed
qed

lemma raw_ring_links_path_iff:
  "raw_ring_links h lp rs \<longleftrightarrow>
   list_all
     (\<lambda>(u, v). raw_next_at h lp u = v \<and> raw_prev_at h lp v = u)
     (raw_path_edges (raw_end_item lp) rs (raw_end_item lp))"
  by (simp add: raw_ring_links_def raw_edge_pairs_def raw_path_edges_zip)

lemma raw_ring_links_delete:
  assumes links: "raw_ring_links h lp rs"
    and distinct: "distinct (raw_end_item lp # rs)"
    and member: "p \<in> set rs"
    and bridge_next:
      "raw_next_at h' lp (raw_prev_at h lp p) = raw_next_at h lp p"
    and bridge_previous:
      "raw_prev_at h' lp (raw_next_at h lp p) = raw_prev_at h lp p"
    and next_frame:
      "\<And>u. u \<in> insert (raw_end_item lp) (set rs) \<Longrightarrow>
        u \<noteq> raw_prev_at h lp p \<Longrightarrow>
        raw_next_at h' lp u = raw_next_at h lp u"
    and previous_frame:
      "\<And>v. v \<in> insert (raw_end_item lp) (set rs) \<Longrightarrow>
        v \<noteq> raw_next_at h lp p \<Longrightarrow>
        raw_prev_at h' lp v = raw_prev_at h lp v"
  shows "raw_ring_links h' lp (remove1 p rs)"
proof -
  let ?e = "raw_end_item lp"
  let ?a = "raw_prev_at h lp p"
  let ?b = "raw_next_at h lp p"
  obtain before after where split: "rs = before @ p # after"
    and p_fresh: "p \<notin> set before"
    using split_list_first[OF member] by blast
  have remove_before: "remove1 p before = before"
    using p_fresh by (induction before) auto
  have remove: "remove1 p rs = before @ after"
    using split remove_before p_fresh by (simp add: remove1_append)
  have split_distinct: "distinct (?e # (before @ p # after))"
    using distinct split by simp
  have end_fresh: "?e \<notin> set (before @ p # after)"
    using split_distinct by simp
  have old_path:
    "list_all
      (\<lambda>(u, v). raw_next_at h lp u = v \<and> raw_prev_at h lp v = u)
      (raw_path_edges ?e (before @ p # after) ?e)"
    using links split by (simp add: raw_ring_links_path_iff)
  have old_edge:
    "\<And>u v. (u, v) \<in>
       set (raw_path_edges ?e (before @ p # after) ?e) \<Longrightarrow>
       raw_next_at h lp u = v \<and> raw_prev_at h lp v = u"
    using old_path by (auto simp: list_all_iff)
  let ?ap = "last (?e # before)"
  let ?bp = "hd (after @ [?e])"
  have entry:
    "(?ap, p) \<in> set (raw_path_edges ?e (before @ p # after) ?e)"
    by (rule raw_path_edges_entry)
  have exit:
    "(p, ?bp) \<in> set (raw_path_edges ?e (before @ p # after) ?e)"
    by (rule raw_path_edges_exit)
  have a_eq: "?a = ?ap"
    using old_edge[OF entry] by simp
  have b_eq: "?b = ?bp"
    using old_edge[OF exit] by simp
  have cases:
    "\<forall>uv \<in> set (raw_path_edges ?e (before @ after) ?e).
       uv = (?ap, ?bp) \<or>
       (uv \<in> set (raw_path_edges ?e (before @ p # after) ?e) \<and>
        fst uv \<noteq> ?ap \<and> snd uv \<noteq> ?bp)"
    by (rule raw_path_edges_delete_cases[OF split_distinct end_fresh])
  have new_path:
    "list_all
      (\<lambda>(u, v). raw_next_at h' lp u = v \<and> raw_prev_at h' lp v = u)
      (raw_path_edges ?e (before @ after) ?e)"
    unfolding list_all_iff
  proof (intro ballI)
    fix uv
    assume uv_new:
      "uv \<in> set (raw_path_edges ?e (before @ after) ?e)"
    obtain u v where uv: "uv = (u, v)"
      by (cases uv) simp
    show "case uv of
      (u, v) \<Rightarrow> raw_next_at h' lp u = v \<and> raw_prev_at h' lp v = u"
    proof (cases "uv = (?ap, ?bp)")
      case True
      then show ?thesis
        using bridge_next bridge_previous a_eq b_eq uv by simp
    next
      case False
      have old:
        "uv \<in> set (raw_path_edges ?e (before @ p # after) ?e)"
        and u_ne: "fst uv \<noteq> ?ap"
        and v_ne: "snd uv \<noteq> ?bp"
        using cases uv_new False by blast+
      have old_fields:
        "raw_next_at h lp u = v \<and> raw_prev_at h lp v = u"
        using old_edge old uv by simp
      have pair_old:
        "(u, v) \<in> set (raw_path_edges ?e (before @ p # after) ?e)"
        using old uv by simp
      have u_cycle: "u \<in> insert ?e (set rs)"
      proof -
        have "u \<in> set (?e # (before @ p # after))"
          by (rule raw_path_edges_sourceD[OF pair_old])
        then show ?thesis using split by simp
      qed
      have v_cycle: "v \<in> insert ?e (set rs)"
      proof -
        have "v \<in> set ((before @ p # after) @ [?e])"
          by (rule raw_path_edges_targetD[OF pair_old])
        then show ?thesis using split by auto
      qed
      have next_frame_eq:
        "raw_next_at h' lp u = raw_next_at h lp u"
        using next_frame[OF u_cycle] u_ne a_eq uv by simp
      have previous_frame_eq:
        "raw_prev_at h' lp v = raw_prev_at h lp v"
        using previous_frame[OF v_cycle] v_ne b_eq uv by simp
      show ?thesis
        using old_fields next_frame_eq previous_frame_eq uv by simp
    qed
  qed
  show ?thesis
    using new_path remove by (simp add: raw_ring_links_path_iff)
qed

text \<open>
  The insertion counterpart should replace the old cursor edge c -> q by
  c -> p -> q and preserve every other edge.  Its intended public statement
  is the following raw-ring-only lemma, parameterised by the abstract cursor
  choice (this is a comment, not an unchecked theorem command):

  theorem raw_ring_links_splice:
    defines
      "c = (case cursor xs of None => raw_end_item lp | Some u => u)"
    defines "q = raw_next_at h lp c"
    assumes "xlist_wf xs"
      and "raw_ring_links h lp (ring xs)"
      and "p \<notin> insert (raw_end_item lp) (set (ring xs))"
      and "raw_next_at h' lp p = q"
      and "raw_prev_at h' lp p = c"
      and "raw_next_at h' lp c = p"
      and "raw_prev_at h' lp q = p"
      and "!!u. u : insert (raw_end_item lp) (set (ring xs)) ==>
             u ~= c ==> raw_next_at h' lp u = raw_next_at h lp u"
      and "!!u. u : insert (raw_end_item lp) (set (ring xs)) ==>
             u ~= q ==> raw_prev_at h' lp u = raw_prev_at h lp u"
    shows
      "raw_ring_links h' lp (ring (list_insert_end_abs p k xs))"

  It is deliberately deferred until the deletion transfer above has been
  checker-audited.
\<close>

end
