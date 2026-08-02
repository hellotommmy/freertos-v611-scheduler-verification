theory Scheduler_Event_Root_Family_Remove_Cursor
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Event_Root_Family_Remove_Predecessor.Scheduler_Event_Root_Family_Remove_Predecessor"
begin

lemma xlist_relabel_remove_cursor_preserved:
  assumes relabel: "xlist_relabel D rx ax"
    and raw_wf: "xlist_wf rx"
    and abs_wf: "xlist_wf ax"
    and member: "p \<in> set (ring rx)"
    and decode: "D p = Some n"
  shows
    "rel_option (\<lambda>q m. D q = Some m)
       (cursor (list_remove_abs p rx))
       (cursor (list_remove_abs n ax))"
proof -
  have pairs:
    "list_all2 (\<lambda>q m. D q = Some m) (ring rx) (ring ax)"
    using relabel by (simp add: xlist_relabel_def)
  have raw_distinct: "distinct (ring rx)"
    and abs_distinct: "distinct (ring ax)"
    using raw_wf abs_wf by (simp_all add: xlist_wf_def)
  have pairs_post:
    "list_all2 (\<lambda>q m. D q = Some m)
       (remove1 p (ring rx)) (remove1 n (ring ax))"
    by (rule list_all2_decoder_remove1[
          OF pairs raw_distinct abs_distinct member decode])
  have predecessor_rel:
    "rel_option (\<lambda>q m. D q = Some m)
       (predecessor p (ring rx)) (predecessor n (ring ax))"
    by (rule list_all2_decoder_predecessor[
          OF pairs raw_distinct abs_distinct member decode])
  have cursor_pre:
    "rel_option (\<lambda>q m. D q = Some m) (cursor rx) (cursor ax)"
    using relabel by (simp add: xlist_relabel_def)
  have cursor_post:
    "rel_option (\<lambda>q m. D q = Some m)
       (if cursor rx = Some p then predecessor p (ring rx) else cursor rx)
       (if cursor ax = Some n then predecessor n (ring ax) else cursor ax)"
  proof (cases "cursor rx")
    case None
    then have abs_none: "cursor ax = None"
      using cursor_pre by (cases "cursor ax") auto
    show ?thesis using None abs_none by simp
  next
    case (Some q)
    then obtain m where abs_some: "cursor ax = Some m"
      and q_decode: "D q = Some m"
      using cursor_pre by (cases "cursor ax") auto
    show ?thesis
    proof (cases "q = p")
      case True
      have mn: "m = n"
        using q_decode decode True by simp
      show ?thesis
        using predecessor_rel Some abs_some True mn by simp
    next
      case False
      have q_member: "q \<in> set (ring rx)"
        using raw_wf Some by (auto simp: xlist_wf_def)
      obtain n' where n'_member: "n' \<in> set (ring ax)"
        and p_decode': "D p = Some n'"
        using list_all2_decoder_left_closed[OF pairs member] by blast
      have n'_eq: "n' = n"
        using decode p_decode' by simp
      have n_member: "n \<in> set (ring ax)"
        using n'_member n'_eq by simp
      have q_post: "q \<in> set (remove1 p (ring rx))"
        using q_member False by simp
      obtain m' where m'_post:
          "m' \<in> set (remove1 n (ring ax))"
        and q_decode': "D q = Some m'"
        using list_all2_decoder_left_closed[OF pairs_post q_post] by blast
      have m'_eq: "m' = m"
        using q_decode q_decode' by simp
      have m_post: "m \<in> set (remove1 n (ring ax))"
        using m'_post m'_eq by simp
      have n_absent: "n \<notin> set (remove1 n (ring ax))"
        by (rule raw_distinct_member_notin_remove1[
              OF abs_distinct n_member])
      have m_ne: "m \<noteq> n"
        using m_post n_absent by blast
      show ?thesis
        using Some abs_some False m_ne q_decode by simp
    qed
  qed
  show ?thesis using cursor_post by (simp add: list_remove_abs_def)
qed

end
