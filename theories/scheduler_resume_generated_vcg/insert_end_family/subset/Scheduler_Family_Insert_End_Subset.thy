theory Scheduler_Family_Insert_End_Subset
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Family_Insert_End_Raw_Family.Scheduler_Family_Insert_End_Raw_Family"
begin

theorem scheduler_family_insert_end_ring_subset:
  assumes pre: "scheduler_family_pre_rel h roots fam live D"
    and target: "target \<in> roots"
    and managed: "p \<in> universal_managed_nodes live D"
  defines "fam' \<equiv> scheduler_family_insert_end_raw h fam target p"
  shows
    "\<forall>lp\<in>roots.
       set (ring (fam' lp)) \<subseteq> universal_managed_nodes live D"
proof -
  have target_rel: "raw_xlist_rel h target (fam target)"
    using pre target
    by (auto simp: scheduler_family_pre_rel_def raw_family_rel_def)
  have target_wf: "xlist_wf (fam target)"
    using target_rel by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have old_managed:
    "\<And>lp. lp \<in> roots \<Longrightarrow>
      set (ring (fam lp)) \<subseteq> universal_managed_nodes live D"
    using pre by (auto simp: scheduler_family_pre_rel_def)
  have target_set:
    "set (ring (fam' target)) = insert p (set (ring (fam target)))"
    unfolding fam'_def scheduler_family_insert_end_raw_def
    by (simp add: list_insert_end_ring_set[OF target_wf])
  show ?thesis
  proof (intro ballI)
    fix lp
    assume root: "lp \<in> roots"
    show
      "set (ring (fam' lp)) \<subseteq> universal_managed_nodes live D"
    proof (cases "lp = target")
      case True
      have set_lp:
        "set (ring (fam' lp)) = insert p (set (ring (fam target)))"
        using target_set True by simp
      show ?thesis
        unfolding set_lp
      proof
        fix q
        assume q: "q \<in> insert p (set (ring (fam target)))"
        show "q \<in> universal_managed_nodes live D"
        proof (cases "q = p")
          case True
          then show ?thesis using managed by simp
        next
          case False
          with q have old: "q \<in> set (ring (fam target))" by simp
          show ?thesis using old old_managed[OF target] by blast
        qed
      qed
    next
      case False
      show ?thesis
        using old_managed[OF root] False
        by (simp add: fam'_def scheduler_family_insert_end_raw_def)
    qed
  qed
qed

end
