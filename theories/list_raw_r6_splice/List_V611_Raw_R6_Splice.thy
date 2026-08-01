theory List_V611_Raw_R6_Splice
  imports "EAL6_FreeRTOS_V611_List_Raw_R6_Transfer.List_V611_Raw_R6_Transfer"
begin

text \<open>
  Pure insertion transfer.  A path edge a -> b is replaced by a -> p -> b;
  every other edge is framed.  The proof is independent of concrete witness
  addresses and does not open a generated C body.
\<close>

lemma raw_path_edges_first:
  "(start, hd (xs @ [finish])) \<in>
     set (raw_path_edges start xs finish)"
  by (cases xs) simp_all

lemma insert_after_at_first_occurrence:
  assumes "c \<notin> set before"
  shows
    "insert_after c p (before @ c # after) =
       before @ c # p # after"
  using assms by (induction before) auto

lemma raw_path_edges_insert_cases:
  assumes distinct: "distinct (start # (before @ after))"
    and finish_fresh: "finish \<notin> set (before @ after)"
  shows
    "\<forall>uv \<in> set (raw_path_edges start (before @ p # after) finish).
       uv = (last (start # before), p) \<or>
       uv = (p, hd (after @ [finish])) \<or>
       (uv \<in> set (raw_path_edges start (before @ after) finish) \<and>
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
      show "fst uv \<noteq> start" using u_ne uv by simp
      show "snd uv \<noteq> y" using v_ne uv by simp
    qed
    show ?thesis using tail_safe Cons by auto
  qed
next
  case (Cons x xs)
  have tail_distinct: "distinct (x # (xs @ after))"
    using Cons.prems(1) by simp
  have tail_finish_fresh: "finish \<notin> set (xs @ after)"
    using Cons.prems(2) by simp
  have ih:
    "\<forall>uv \<in> set (raw_path_edges x (xs @ p # after) finish).
       uv = (last (x # xs), p) \<or>
       uv = (p, hd (after @ [finish])) \<or>
       (uv \<in> set (raw_path_edges x (xs @ after) finish) \<and>
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
      "uv \<in> set (raw_path_edges start ((x # xs) @ p # after) finish)"
    show
      "uv = (last (start # x # xs), p) \<or>
       uv = (p, hd (after @ [finish])) \<or>
       (uv \<in> set (raw_path_edges start ((x # xs) @ after) finish) \<and>
        fst uv \<noteq> last (start # x # xs) \<and>
        snd uv \<noteq> hd (after @ [finish]))"
    proof (cases "uv = (start, x)")
      case True
      then show ?thesis using start_ne_last x_ne_head by simp
    next
      case False
      have tail:
        "uv \<in> set (raw_path_edges x (xs @ p # after) finish)"
        using new False by simp
      have ih_case:
        "uv = (last (x # xs), p) \<or>
         uv = (p, hd (after @ [finish])) \<or>
         (uv \<in> set (raw_path_edges x (xs @ after) finish) \<and>
          fst uv \<noteq> last (x # xs) \<and>
          snd uv \<noteq> hd (after @ [finish]))"
        using ih tail by blast
      then show ?thesis by auto
    qed
  qed
qed

lemma raw_ring_links_insert_path:
  assumes links: "raw_ring_links h lp (before @ after)"
    and distinct:
      "distinct (raw_end_item lp # (before @ after))"
    and entry_next:
      "raw_next_at h' lp (last (raw_end_item lp # before)) = p"
    and entry_previous:
      "raw_prev_at h' lp p = last (raw_end_item lp # before)"
    and exit_next:
      "raw_next_at h' lp p = hd (after @ [raw_end_item lp])"
    and exit_previous:
      "raw_prev_at h' lp (hd (after @ [raw_end_item lp])) = p"
    and next_frame:
      "\<And>u. u \<in> insert (raw_end_item lp) (set (before @ after)) \<Longrightarrow>
        u \<noteq> last (raw_end_item lp # before) \<Longrightarrow>
        raw_next_at h' lp u = raw_next_at h lp u"
    and previous_frame:
      "\<And>v. v \<in> insert (raw_end_item lp) (set (before @ after)) \<Longrightarrow>
        v \<noteq> hd (after @ [raw_end_item lp]) \<Longrightarrow>
        raw_prev_at h' lp v = raw_prev_at h lp v"
  shows "raw_ring_links h' lp (before @ p # after)"
proof -
  let ?e = "raw_end_item lp"
  let ?a = "last (?e # before)"
  let ?b = "hd (after @ [?e])"
  have end_fresh: "?e \<notin> set (before @ after)"
    using distinct by simp
  have old_path:
    "list_all
      (\<lambda>(u, v). raw_next_at h lp u = v \<and> raw_prev_at h lp v = u)
      (raw_path_edges ?e (before @ after) ?e)"
    using links by (simp add: raw_ring_links_path_iff)
  have old_edge:
    "\<And>u v. (u, v) \<in> set (raw_path_edges ?e (before @ after) ?e) \<Longrightarrow>
       raw_next_at h lp u = v \<and> raw_prev_at h lp v = u"
    using old_path by (auto simp: list_all_iff)
  have cases:
    "\<forall>uv \<in> set (raw_path_edges ?e (before @ p # after) ?e).
       uv = (?a, p) \<or> uv = (p, ?b) \<or>
       (uv \<in> set (raw_path_edges ?e (before @ after) ?e) \<and>
        fst uv \<noteq> ?a \<and> snd uv \<noteq> ?b)"
    by (rule raw_path_edges_insert_cases[OF distinct end_fresh])
  have new_path:
    "list_all
      (\<lambda>(u, v). raw_next_at h' lp u = v \<and> raw_prev_at h' lp v = u)
      (raw_path_edges ?e (before @ p # after) ?e)"
    unfolding list_all_iff
  proof (intro ballI)
    fix uv
    assume uv_new:
      "uv \<in> set (raw_path_edges ?e (before @ p # after) ?e)"
    obtain u v where uv: "uv = (u, v)"
      by (cases uv) simp
    show "case uv of
      (u, v) \<Rightarrow> raw_next_at h' lp u = v \<and> raw_prev_at h' lp v = u"
    proof (cases "uv = (?a, p)")
      case True
      then show ?thesis using entry_next entry_previous uv by simp
    next
      case not_entry: False
      show ?thesis
      proof (cases "uv = (p, ?b)")
        case True
        then show ?thesis using exit_next exit_previous uv by simp
      next
        case not_exit: False
        have old:
          "uv \<in> set (raw_path_edges ?e (before @ after) ?e)"
          and u_ne: "fst uv \<noteq> ?a"
          and v_ne: "snd uv \<noteq> ?b"
          using cases uv_new not_entry not_exit by blast+
        have pair_old:
          "(u, v) \<in> set (raw_path_edges ?e (before @ after) ?e)"
          using old uv by simp
        have old_fields:
          "raw_next_at h lp u = v \<and> raw_prev_at h lp v = u"
          by (rule old_edge[OF pair_old])
        have u_cycle: "u \<in> insert ?e (set (before @ after))"
        proof -
          have "u \<in> set (?e # (before @ after))"
            by (rule raw_path_edges_sourceD[OF pair_old])
          then show ?thesis by simp
        qed
        have v_cycle: "v \<in> insert ?e (set (before @ after))"
        proof -
          have "v \<in> set ((before @ after) @ [?e])"
            by (rule raw_path_edges_targetD[OF pair_old])
          then show ?thesis by auto
        qed
        have next_frame_eq:
          "raw_next_at h' lp u = raw_next_at h lp u"
          using next_frame[OF u_cycle] u_ne uv by simp
        have previous_frame_eq:
          "raw_prev_at h' lp v = raw_prev_at h lp v"
          using previous_frame[OF v_cycle] v_ne uv by simp
        show ?thesis
          using old_fields next_frame_eq previous_frame_eq uv by simp
      qed
    qed
  qed
  show ?thesis
    using new_path by (simp add: raw_ring_links_path_iff)
qed

definition raw_cursor_node ::
  "xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs \<Rightarrow> raw_node_id"
where
  "raw_cursor_node lp xs =
     (case cursor xs of None \<Rightarrow> raw_end_item lp | Some c \<Rightarrow> c)"

lemma raw_cursor_node_in_cycle:
  assumes wf: "xlist_wf xs"
  shows
    "raw_cursor_node lp xs \<in>
       insert (raw_end_item lp) (set (ring xs))"
  using wf
  by (cases "cursor xs")
     (auto simp: raw_cursor_node_def xlist_wf_def)

theorem raw_ring_links_splice:
  assumes wf: "xlist_wf xs"
    and distinct_cycle:
      "distinct (raw_end_item lp # ring xs)"
    and links: "raw_ring_links h lp (ring xs)"
    and entry_next:
      "raw_next_at h' lp (raw_cursor_node lp xs) = p"
    and entry_previous:
      "raw_prev_at h' lp p = raw_cursor_node lp xs"
    and exit_next:
      "raw_next_at h' lp p =
         raw_next_at h lp (raw_cursor_node lp xs)"
    and exit_previous:
      "raw_prev_at h' lp
         (raw_next_at h lp (raw_cursor_node lp xs)) = p"
    and next_frame:
      "\<And>u. u \<in> insert (raw_end_item lp) (set (ring xs)) \<Longrightarrow>
        u \<noteq> raw_cursor_node lp xs \<Longrightarrow>
        raw_next_at h' lp u = raw_next_at h lp u"
    and previous_frame:
      "\<And>v. v \<in> insert (raw_end_item lp) (set (ring xs)) \<Longrightarrow>
        v \<noteq> raw_next_at h lp (raw_cursor_node lp xs) \<Longrightarrow>
        raw_prev_at h' lp v = raw_prev_at h lp v"
  shows
    "raw_ring_links h' lp (ring (list_insert_end_abs p k xs))"
proof (cases "cursor xs")
  case None
  let ?e = "raw_end_item lp"
  let ?b = "hd (ring xs @ [?e])"
  have old_path:
    "list_all
      (\<lambda>(u, v). raw_next_at h lp u = v \<and> raw_prev_at h lp v = u)
      (raw_path_edges ?e (ring xs) ?e)"
    using links by (simp add: raw_ring_links_path_iff)
  have first: "(?e, ?b) \<in> set (raw_path_edges ?e (ring xs) ?e)"
    by (rule raw_path_edges_first)
  have successor: "raw_next_at h lp ?e = ?b"
    using old_path first by (auto simp: list_all_iff)
  have inserted:
    "ring (list_insert_end_abs p k xs) = p # ring xs"
    using None by (simp add: list_insert_end_abs_def)
  have transfer: "raw_ring_links h' lp ([] @ p # ring xs)"
  proof (rule raw_ring_links_insert_path)
    show "raw_ring_links h lp ([] @ ring xs)" using links by simp
    show "distinct (?e # ([] @ ring xs))" using distinct_cycle by simp
    show "raw_next_at h' lp (last (?e # [])) = p"
      using entry_next None by (simp add: raw_cursor_node_def)
    show "raw_prev_at h' lp p = last (?e # [])"
      using entry_previous None by (simp add: raw_cursor_node_def)
    show "raw_next_at h' lp p = hd (ring xs @ [?e])"
      using exit_next None successor by (simp add: raw_cursor_node_def)
    show "raw_prev_at h' lp (hd (ring xs @ [?e])) = p"
      using exit_previous None successor by (simp add: raw_cursor_node_def)
    fix u
    assume member: "u \<in> insert ?e (set ([] @ ring xs))"
      and ne: "u \<noteq> last (?e # [])"
    show "raw_next_at h' lp u = raw_next_at h lp u"
      by (rule next_frame[OF _ _])
         (use member ne None in
           \<open>simp_all add: raw_cursor_node_def\<close>)
  next
    fix v
    assume member: "v \<in> insert ?e (set ([] @ ring xs))"
      and ne: "v \<noteq> hd (ring xs @ [?e])"
    show "raw_prev_at h' lp v = raw_prev_at h lp v"
      by (rule previous_frame[OF _ _])
         (use member ne None successor in
           \<open>simp_all add: raw_cursor_node_def\<close>)
  qed
  show ?thesis using transfer inserted by simp
next
  case (Some c)
  have c_member: "c \<in> set (ring xs)"
    using wf Some by (auto simp: xlist_wf_def)
  obtain before after where split: "ring xs = before @ c # after"
    and c_fresh: "c \<notin> set before"
    using split_list_first[OF c_member] by blast
  have inserted_after:
    "insert_after c p (ring xs) = before @ c # p # after"
    using insert_after_at_first_occurrence[OF c_fresh] split by simp
  let ?e = "raw_end_item lp"
  let ?b = "hd (after @ [?e])"
  have old_path:
    "list_all
      (\<lambda>(u, v). raw_next_at h lp u = v \<and> raw_prev_at h lp v = u)
      (raw_path_edges ?e (before @ c # after) ?e)"
    using links split by (simp add: raw_ring_links_path_iff)
  have exit: "(c, ?b) \<in>
      set (raw_path_edges ?e (before @ c # after) ?e)"
    by (rule raw_path_edges_exit)
  have successor: "raw_next_at h lp c = ?b"
    using old_path exit by (auto simp: list_all_iff)
  have transfer:
    "raw_ring_links h' lp ((before @ [c]) @ p # after)"
  proof (rule raw_ring_links_insert_path)
    show "raw_ring_links h lp ((before @ [c]) @ after)"
      using links split by simp
    show "distinct (?e # ((before @ [c]) @ after))"
      using distinct_cycle split by simp
    show "raw_next_at h' lp (last (?e # before @ [c])) = p"
      using entry_next Some by (simp add: raw_cursor_node_def)
    show "raw_prev_at h' lp p = last (?e # before @ [c])"
      using entry_previous Some by (simp add: raw_cursor_node_def)
    show "raw_next_at h' lp p = hd (after @ [?e])"
      using exit_next Some successor by (simp add: raw_cursor_node_def)
    show "raw_prev_at h' lp (hd (after @ [?e])) = p"
      using exit_previous Some successor by (simp add: raw_cursor_node_def)
    fix u
    assume member:
      "u \<in> insert ?e (set ((before @ [c]) @ after))"
      and ne: "u \<noteq> last (?e # before @ [c])"
    show "raw_next_at h' lp u = raw_next_at h lp u"
      by (rule next_frame[OF _ _])
         (use member ne Some split in
           \<open>simp_all add: raw_cursor_node_def\<close>)
  next
    fix v
    assume member:
      "v \<in> insert ?e (set ((before @ [c]) @ after))"
      and ne: "v \<noteq> hd (after @ [?e])"
    show "raw_prev_at h' lp v = raw_prev_at h lp v"
      by (rule previous_frame[OF _ _])
         (use member ne Some split successor in
           \<open>simp_all add: raw_cursor_node_def\<close>)
  qed
  have result_ring:
    "ring (list_insert_end_abs p k xs) = before @ c # p # after"
    using Some inserted_after by (simp add: list_insert_end_abs_def)
  show ?thesis using transfer result_ring by simp
qed

end
