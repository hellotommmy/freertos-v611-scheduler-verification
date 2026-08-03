theory Scheduler_XList_Relabel_Insert_End
  imports
    "EAL6_FreeRTOS_V611_Scheduler_List_All2_Insert_After.Scheduler_List_All2_Insert_After"
begin

theorem xlist_relabel_insert_end_preserved:
  assumes relabel: "xlist_relabel D rx ax"
    and raw_wf: "xlist_wf rx"
    and abs_wf: "xlist_wf ax"
    and abs_fresh: "n \<notin> set (ring ax)"
    and decode: "D p = Some n"
    and new_key: "raw_k = abs_k"
  shows
    "xlist_relabel D
       (list_insert_end_abs p raw_k rx)
       (list_insert_end_abs n abs_k ax)"
proof -
  have pairs:
    "list_all2 (\<lambda>q m. D q = Some m) (ring rx) (ring ax)"
    using relabel by (simp add: xlist_relabel_def)
  have cursors:
    "rel_option (\<lambda>q m. D q = Some m) (cursor rx) (cursor ax)"
    using relabel by (simp add: xlist_relabel_def)
  have old_keys:
    "\<forall>q\<in>set (ring rx). \<forall>m.
       D q = Some m \<longrightarrow> item_key rx q = item_key ax m"
    using relabel by (simp add: xlist_relabel_def)
  have abs_distinct: "distinct (ring ax)"
    using abs_wf by (simp add: xlist_wf_def)
  have pairs_post:
    "list_all2 (\<lambda>q m. D q = Some m)
       (ring (list_insert_end_abs p raw_k rx))
       (ring (list_insert_end_abs n abs_k ax))"
  proof (cases "cursor rx")
    case None
    have abs_none: "cursor ax = None"
      using cursors None by (cases "cursor ax") auto
    show ?thesis
      using pairs decode None abs_none
      by (simp add: list_insert_end_abs_def)
  next
    case (Some c)
    obtain d where abs_some: "cursor ax = Some d"
      and cursor_decode: "D c = Some d"
      using cursors Some by (cases "cursor ax") auto
    have c_member: "c \<in> set (ring rx)"
      using raw_wf Some by (auto simp: xlist_wf_def)
    have inserted:
      "list_all2 (\<lambda>q m. D q = Some m)
         (insert_after c p (ring rx))
         (insert_after d n (ring ax))"
      by (rule list_all2_decoder_insert_after[
            OF pairs abs_distinct c_member cursor_decode decode])
    show ?thesis
      using Some abs_some inserted
      by (simp add: list_insert_end_abs_def)
  qed
  have cursor_post:
    "rel_option (\<lambda>q m. D q = Some m)
       (cursor (list_insert_end_abs p raw_k rx))
       (cursor (list_insert_end_abs n abs_k ax))"
    using decode by (simp add: list_insert_end_abs_def)
  have raw_post_set:
    "set (ring (list_insert_end_abs p raw_k rx)) =
       insert p (set (ring rx))"
  proof (cases "cursor rx")
    case None
    then show ?thesis by (simp add: list_insert_end_abs_def)
  next
    case (Some c)
    have c_member: "c \<in> set (ring rx)"
      using raw_wf Some by (auto simp: xlist_wf_def)
    show ?thesis
      using Some set_insert_after[OF c_member, where x=p]
      by (simp add: list_insert_end_abs_def)
  qed
  have keys_post:
    "\<forall>q\<in>set (ring (list_insert_end_abs p raw_k rx)). \<forall>m.
       D q = Some m \<longrightarrow>
       item_key (list_insert_end_abs p raw_k rx) q =
         item_key (list_insert_end_abs n abs_k ax) m"
  proof (intro ballI)
    fix q
    assume q_post:
      "q \<in> set (ring (list_insert_end_abs p raw_k rx))"
    show "\<forall>m. D q = Some m \<longrightarrow>
      item_key (list_insert_end_abs p raw_k rx) q =
        item_key (list_insert_end_abs n abs_k ax) m"
    proof (intro allI impI)
      fix m
      assume q_decode: "D q = Some m"
      have q_cases: "q = p \<or> q \<in> set (ring rx)"
        using q_post raw_post_set by auto
      show
        "item_key (list_insert_end_abs p raw_k rx) q =
          item_key (list_insert_end_abs n abs_k ax) m"
      proof (cases "q = p")
        case True
        have m_eq: "m = n"
          using decode q_decode True by simp
        show ?thesis
          using True m_eq new_key
          by (simp add: list_insert_end_abs_def)
      next
        case False
        have q_old: "q \<in> set (ring rx)"
          using q_cases False by blast
        have old_key: "item_key rx q = item_key ax m"
          using old_keys q_old q_decode by blast
        obtain m' where m'_member: "m' \<in> set (ring ax)"
          and m'_decode: "D q = Some m'"
          using list_all2_decoder_left_closed[OF pairs q_old] by blast
        have m'_eq: "m' = m"
          using q_decode m'_decode by simp
        have m_member: "m \<in> set (ring ax)"
          using m'_member m'_eq by simp
        have m_ne: "m \<noteq> n"
          using abs_fresh m_member by blast
        show ?thesis
          using False m_ne old_key
          by (simp add: list_insert_end_abs_def)
      qed
    qed
  qed
  show ?thesis
    unfolding xlist_relabel_def
  proof (intro conjI)
    show "list_all2 (\<lambda>q m. D q = Some m)
      (ring (list_insert_end_abs p raw_k rx))
      (ring (list_insert_end_abs n abs_k ax))"
      by (rule pairs_post)
  next
    show "rel_option (\<lambda>q m. D q = Some m)
      (cursor (list_insert_end_abs p raw_k rx))
      (cursor (list_insert_end_abs n abs_k ax))"
      by (rule cursor_post)
  next
    show "\<forall>q\<in>set (ring (list_insert_end_abs p raw_k rx)). \<forall>m.
      D q = Some m \<longrightarrow>
      item_key (list_insert_end_abs p raw_k rx) q =
        item_key (list_insert_end_abs n abs_k ax) m"
      by (rule keys_post)
  qed
qed

end
