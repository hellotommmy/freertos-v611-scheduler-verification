theory Scheduler_Event_Root_Family_Remove_Container_Rep
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Event_Root_Family_Remove_Physical.Scheduler_Event_Root_Family_Remove_Physical"
begin

lemma scheduler_event_root_family_remove_container_rep:
  assumes rel:
      "scheduler_event_root_family_rel
         D h roots pending raw_fam abs_fam live K_E"
    and owner: "owner \<in> roots"
    and removed_live: "t \<in> live"
    and member:
      "event_item_raw_ptr D t \<in> set (ring (raw_fam owner))"
  shows
    "event_family_container_rep D
       (raw_remove_concrete_heap h (event_item_raw_ptr D t)) roots
       (event_remove_raw_family raw_fam owner (event_item_raw_ptr D t))
       live"
proof -
  let ?p = "event_item_raw_ptr D t"
  let ?h' = "raw_remove_concrete_heap h ?p"
  let ?fam' = "event_remove_raw_family raw_fam owner ?p"
  have old:
    "event_family_container_rep D h roots raw_fam live"
    using rel by (simp add: scheduler_event_root_family_rel_def)
  have faithful_old:
    "raw_family_container_faithful_on h roots raw_fam
       (event_item_raw_set live D)"
    using old by (simp add: event_family_container_rep_def)
  have p_managed: "?p \<in> event_item_raw_set live D"
    using removed_live by (auto simp: event_item_raw_set_def)
  have removed_members:
    "raw_family_members roots ?fam' ?p = {}"
    by (rule scheduler_event_root_family_remove_members_empty[
          OF rel owner removed_live member])
  have membership_frame:
    "\<And>lp q. lp \<in> roots \<Longrightarrow>
      q \<in> event_item_raw_set live D \<Longrightarrow> q \<noteq> ?p \<Longrightarrow>
      (q \<in> set (ring (?fam' lp)) \<longleftrightarrow>
       q \<in> set (ring (raw_fam lp)))"
  proof -
    fix lp q
    assume lp_root: "lp \<in> roots"
      and q_managed: "q \<in> event_item_raw_set live D"
      and q_ne: "q \<noteq> ?p"
    show
      "q \<in> set (ring (?fam' lp)) \<longleftrightarrow>
       q \<in> set (ring (raw_fam lp))"
      by (rule event_remove_raw_family_membership_frame[OF q_ne])
  qed
  have container_frame:
    "\<And>q. q \<in> event_item_raw_set live D \<Longrightarrow> q \<noteq> ?p \<Longrightarrow>
      pvContainer_C (h_val ?h' q) = pvContainer_C (h_val h q)"
  proof -
    fix q
    assume q_managed: "q \<in> event_item_raw_set live D"
      and q_ne: "q \<noteq> ?p"
    obtain u where u_live: "u \<in> live"
      and q: "q = event_item_raw_ptr D u"
      using q_managed by (auto simp: event_item_raw_set_def)
    have u_ne: "u \<noteq> t"
      using q_ne q by auto
    show "pvContainer_C (h_val ?h' q) = pvContainer_C (h_val h q)"
      using scheduler_event_root_family_remove_other_payload_frame[
        OF rel owner removed_live u_live u_ne member] q by simp
  qed
  have removed_null: "pvContainer_C (h_val ?h' ?p) = NULL"
    using scheduler_event_root_family_remove_item_effect[
      OF rel owner removed_live member] by simp
  have faithful_post:
    "raw_family_container_faithful_on ?h' roots ?fam'
       (event_item_raw_set live D)"
    by (rule raw_family_container_faithful_on_preserved[
          OF faithful_old p_managed removed_members membership_frame
             container_frame removed_null])
  have pointwise:
    "\<forall>u\<in>live. \<forall>lp\<in>roots.
       event_item_raw_ptr D u \<in> set (ring (?fam' lp)) \<longleftrightarrow>
       pvContainer_C (h_val ?h' (event_item_raw_ptr D u)) =
         PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
  proof (intro ballI)
    fix u
    assume u_live: "u \<in> live"
    fix lp
    assume lp_root: "lp \<in> roots"
    show
      "event_item_raw_ptr D u \<in> set (ring (?fam' lp)) \<longleftrightarrow>
       pvContainer_C (h_val ?h' (event_item_raw_ptr D u)) =
         PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
    proof (cases "u = t")
      case True
      have absent:
        "event_item_raw_ptr D u \<notin> set (ring (?fam' lp))"
        using removed_members lp_root True
        by (auto simp: raw_family_members_def)
      have null:
        "pvContainer_C (h_val ?h' (event_item_raw_ptr D u)) = NULL"
        using removed_null True by simp
      have raw: "raw_xlist_rel h lp (raw_fam lp)"
        by (rule scheduler_event_root_family_raw_rootD[OF rel lp_root])
      have guard: "c_guard lp"
        using raw by (simp add: raw_xlist_rel_def raw_xlist_layout_def)
      have root_not_null:
        "PTR_COERCE(xLIST_C \<rightarrow> unit) lp \<noteq> NULL"
      proof -
        have "lp \<noteq> NULL"
          by (rule c_guard_NULL[OF guard])
        then show ?thesis by simp
      qed
      show ?thesis
      proof
        assume linked:
          "event_item_raw_ptr D u \<in> set (ring (?fam' lp))"
        show
          "pvContainer_C (h_val ?h' (event_item_raw_ptr D u)) =
             PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
          using absent linked by contradiction
      next
        assume container:
          "pvContainer_C (h_val ?h' (event_item_raw_ptr D u)) =
             PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
        have coerced_null:
          "PTR_COERCE(xLIST_C \<rightarrow> unit) lp = NULL"
          using container null by simp
        show
          "event_item_raw_ptr D u \<in> set (ring (?fam' lp))"
          using root_not_null coerced_null by contradiction
      qed
    next
      case False
      have member_same:
        "event_item_raw_ptr D u \<in> set (ring (?fam' lp)) \<longleftrightarrow>
         event_item_raw_ptr D u \<in> set (ring (raw_fam lp))"
        by (rule scheduler_event_root_family_remove_membership_frame[
              OF rel removed_live u_live False])
      have container_same:
        "pvContainer_C (h_val ?h' (event_item_raw_ptr D u)) =
         pvContainer_C (h_val h (event_item_raw_ptr D u))"
        using scheduler_event_root_family_remove_other_payload_frame[
          OF rel owner removed_live u_live False member] by simp
      have old_iff:
        "event_item_raw_ptr D u \<in> set (ring (raw_fam lp)) \<longleftrightarrow>
         pvContainer_C (h_val h (event_item_raw_ptr D u)) =
           PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
        by (rule scheduler_event_root_family_container_iff[
              OF rel u_live lp_root])
      show ?thesis using member_same container_same old_iff by simp
    qed
  qed
  show ?thesis
    using faithful_post pointwise
    by (simp add: event_family_container_rep_def)
qed

end
