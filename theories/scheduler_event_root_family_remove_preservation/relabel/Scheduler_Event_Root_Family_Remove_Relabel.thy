theory Scheduler_Event_Root_Family_Remove_Relabel
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Event_Root_Family_Remove_Keys.Scheduler_Event_Root_Family_Remove_Keys"
begin

lemma xlist_relabel_remove_preserved:
  assumes relabel: "xlist_relabel D rx ax"
    and raw_wf: "xlist_wf rx"
    and abs_wf: "xlist_wf ax"
    and member: "p \<in> set (ring rx)"
    and decode: "D p = Some n"
  shows
    "xlist_relabel D (list_remove_abs p rx) (list_remove_abs n ax)"
proof -
  have pairs:
    "list_all2 (\<lambda>q m. D q = Some m) (ring rx) (ring ax)"
    using relabel by (simp add: xlist_relabel_def)
  have raw_distinct: "distinct (ring rx)"
    and abs_distinct: "distinct (ring ax)"
    using raw_wf abs_wf by (simp_all add: xlist_wf_def)
  have pairs_post:
    "list_all2 (\<lambda>q m. D q = Some m)
       (ring (list_remove_abs p rx))
       (ring (list_remove_abs n ax))"
  proof -
    have removed:
      "list_all2 (\<lambda>q m. D q = Some m)
         (remove1 p (ring rx)) (remove1 n (ring ax))"
      by (rule list_all2_decoder_remove1[
            OF pairs raw_distinct abs_distinct member decode])
    show ?thesis using removed by (simp add: list_remove_abs_def)
  qed
  have cursor_post:
    "rel_option (\<lambda>q m. D q = Some m)
       (cursor (list_remove_abs p rx))
       (cursor (list_remove_abs n ax))"
    by (rule xlist_relabel_remove_cursor_preserved[
          OF relabel raw_wf abs_wf member decode])
  have keys_post:
    "\<forall>q \<in> set (ring (list_remove_abs p rx)). \<forall>m.
       D q = Some m \<longrightarrow>
       item_key (list_remove_abs p rx) q =
         item_key (list_remove_abs n ax) m"
    by (rule xlist_relabel_remove_keys_preserved[OF relabel])
  show ?thesis
    unfolding xlist_relabel_def
  proof (intro conjI)
    show
      "list_all2 (\<lambda>q m. D q = Some m)
         (ring (list_remove_abs p rx))
         (ring (list_remove_abs n ax))"
      by (rule pairs_post)
  next
    show
      "rel_option (\<lambda>q m. D q = Some m)
         (cursor (list_remove_abs p rx))
         (cursor (list_remove_abs n ax))"
      by (rule cursor_post)
  next
    show
      "\<forall>q \<in> set (ring (list_remove_abs p rx)). \<forall>m.
         D q = Some m \<longrightarrow>
         item_key (list_remove_abs p rx) q =
           item_key (list_remove_abs n ax) m"
      by (rule keys_post)
  qed
qed

lemma event_ring_remove_preserved:
  assumes "event_ring ax"
  shows "event_ring (list_remove_abs (Event t) ax)"
  using assms by (auto simp: event_ring_def list_remove_abs_def)

definition event_remove_raw_family ::
  "(xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   xLIST_C ptr \<Rightarrow> raw_node_id \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs)"
where
  "event_remove_raw_family fam owner p =
     fam(owner := list_remove_abs p (fam owner))"

definition event_remove_abs_family ::
  "(xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow>
   xLIST_C ptr \<Rightarrow> 'tid \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring)"
where
  "event_remove_abs_family fam owner t =
     fam(owner := list_remove_abs (Event t) (fam owner))"

lemma event_remove_raw_family_membership_frame:
  assumes different: "q \<noteq> p"
  shows
    "q \<in> set (ring (event_remove_raw_family fam owner p lp)) \<longleftrightarrow>
     q \<in> set (ring (fam lp))"
  using different
  by (cases "lp = owner")
     (simp_all add: event_remove_raw_family_def list_remove_abs_def)

lemma event_remove_abs_family_membership_frame:
  assumes different: "u \<noteq> t"
  shows
    "Event u \<in> set (ring (event_remove_abs_family fam owner t lp))
       \<longleftrightarrow>
     Event u \<in> set (ring (fam lp))"
  using different
  by (cases "lp = owner")
     (simp_all add: event_remove_abs_family_def list_remove_abs_def)

end
