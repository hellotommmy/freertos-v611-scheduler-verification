theory Scheduler_Family_Insert_End_Disjoint
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Family_Insert_End_Subset.Scheduler_Family_Insert_End_Subset"
begin

theorem scheduler_family_insert_end_rings_disjoint:
  assumes pre: "scheduler_family_pre_rel h roots fam live D"
    and target: "target \<in> roots"
    and absent: "raw_family_members roots fam p = {}"
  defines "fam' \<equiv> scheduler_family_insert_end_raw h fam target p"
  shows
    "\<forall>lp\<in>roots. \<forall>lq\<in>roots. lp \<noteq> lq \<longrightarrow>
       set (ring (fam' lp)) \<inter> set (ring (fam' lq)) = {}"
proof -
  have target_rel: "raw_xlist_rel h target (fam target)"
    using pre target
    by (auto simp: scheduler_family_pre_rel_def raw_family_rel_def)
  have target_wf: "xlist_wf (fam target)"
    using target_rel by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have target_set:
    "set (ring (fam' target)) = insert p (set (ring (fam target)))"
    unfolding fam'_def scheduler_family_insert_end_raw_def
    by (simp add: list_insert_end_ring_set[OF target_wf])
  have p_absent:
    "\<And>lp. lp \<in> roots \<Longrightarrow> p \<notin> set (ring (fam lp))"
    using absent by (auto simp: raw_family_members_def)
  have old_disjoint:
    "\<And>lp lq. lp \<in> roots \<Longrightarrow> lq \<in> roots \<Longrightarrow>
      lp \<noteq> lq \<Longrightarrow>
      set (ring (fam lp)) \<inter> set (ring (fam lq)) = {}"
    using pre by (auto simp: scheduler_family_pre_rel_def)
  show ?thesis
  proof (intro ballI impI)
    fix lp
    assume lp: "lp \<in> roots"
    fix lq
    assume lq: "lq \<in> roots" and different: "lp \<noteq> lq"
    have old: "set (ring (fam lp)) \<inter> set (ring (fam lq)) = {}"
      by (rule old_disjoint[OF lp lq different])
    have p_lp: "p \<notin> set (ring (fam lp))"
      by (rule p_absent[OF lp])
    have p_lq: "p \<notin> set (ring (fam lq))"
      by (rule p_absent[OF lq])
    show "set (ring (fam' lp)) \<inter> set (ring (fam' lq)) = {}"
    proof (cases "lp = target")
      case True
      have lq_ne: "lq \<noteq> target" using True different by simp
      show ?thesis
        using target_set old p_lq True lq_ne
        by (simp add: fam'_def scheduler_family_insert_end_raw_def)
    next
      case False
      show ?thesis
      proof (cases "lq = target")
        case True
        show ?thesis
          using target_set old p_lp False True
          by (simp add: fam'_def scheduler_family_insert_end_raw_def)
      next
        case False_lq: False
        show ?thesis
          using old False False_lq
          by (simp add: fam'_def scheduler_family_insert_end_raw_def)
      qed
    qed
  qed
qed

end
