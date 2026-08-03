theory Scheduler_Family_Insert_End_Membership
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Family_Insert_End_Disjoint.Scheduler_Family_Insert_End_Disjoint"
begin

theorem scheduler_family_insert_end_membership:
  assumes pre: "scheduler_family_pre_rel h roots fam live D"
    and target: "target \<in> roots"
    and absent: "raw_family_members roots fam p = {}"
  defines "fam' \<equiv> scheduler_family_insert_end_raw h fam target p"
  shows "raw_family_members roots fam' p = {target}"
proof -
  have family: "raw_family_rel h roots fam"
    using pre by (simp add: scheduler_family_pre_rel_def)
  have target_rel: "raw_xlist_rel h target (fam target)"
    using family target by (simp add: raw_family_rel_def)
  have target_wf: "xlist_wf (fam target)"
    using target_rel by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have target_set:
    "set (ring (fam' target)) = insert p (set (ring (fam target)))"
    unfolding fam'_def scheduler_family_insert_end_raw_def
    by (simp add: list_insert_end_ring_set[OF target_wf])
  have p_absent:
    "\<And>lp. lp \<in> roots \<Longrightarrow> p \<notin> set (ring (fam lp))"
  proof -
    fix lp
    assume root: "lp \<in> roots"
    show "p \<notin> set (ring (fam lp))"
    proof
      assume member: "p \<in> set (ring (fam lp))"
      have "lp \<in> raw_family_members roots fam p"
        using root member by (simp add: raw_family_members_def)
      with absent show False by simp
    qed
  qed
  have target_member: "p \<in> set (ring (fam' target))"
    using target_set by simp
  have only:
    "\<And>lp. lp \<in> roots \<Longrightarrow>
      p \<in> set (ring (fam' lp)) \<Longrightarrow> lp = target"
  proof -
    fix lp
    assume root: "lp \<in> roots"
      and member: "p \<in> set (ring (fam' lp))"
    show "lp = target"
    proof (rule ccontr)
      assume different: "lp \<noteq> target"
      then have same: "fam' lp = fam lp"
        by (simp add: fam'_def scheduler_family_insert_end_raw_def)
      from member same p_absent[OF root] show False by simp
    qed
  qed
  show ?thesis
  proof (rule Set.equalityI)
    show "raw_family_members roots fam' p \<subseteq> {target}"
    proof
      fix lp
      assume member: "lp \<in> raw_family_members roots fam' p"
      have root: "lp \<in> roots"
        using member by (simp add: raw_family_members_def)
      have ring_member: "p \<in> set (ring (fam' lp))"
        using member by (simp add: raw_family_members_def)
      have "lp = target" by (rule only[OF root ring_member])
      then show "lp \<in> {target}" by simp
    qed
  next
    show "{target} \<subseteq> raw_family_members roots fam' p"
    proof
      fix lp
      assume "lp \<in> {target}"
      then have "lp = target" by simp
      then show "lp \<in> raw_family_members roots fam' p"
        using target target_member
        by (simp add: raw_family_members_def)
    qed
  qed
qed

end
