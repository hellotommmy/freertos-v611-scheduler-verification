theory Scheduler_Family_Insert_End_Shape
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Family_Insert_End_Membership.Scheduler_Family_Insert_End_Membership"
begin

theorem scheduler_family_insert_end_shape:
  assumes pre: "scheduler_family_pre_rel h roots fam live D"
    and target: "target \<in> roots"
    and managed: "p \<in> universal_managed_nodes live D"
    and absent: "raw_family_members roots fam p = {}"
  defines "fam' \<equiv> scheduler_family_insert_end_raw h fam target p"
  shows
    "(\<forall>lp\<in>roots.
       set (ring (fam' lp)) \<subseteq> universal_managed_nodes live D) \<and>
     (\<forall>lp\<in>roots. \<forall>lq\<in>roots. lp \<noteq> lq \<longrightarrow>
       set (ring (fam' lp)) \<inter> set (ring (fam' lq)) = {}) \<and>
     raw_family_members roots fam' p = {target}"
proof -
  have ring_subset:
    "\<forall>lp\<in>roots.
      set (ring (fam' lp)) \<subseteq> universal_managed_nodes live D"
    unfolding fam'_def
    by (rule scheduler_family_insert_end_ring_subset[
          OF pre target managed])
  have rings_disjoint:
    "\<forall>lp\<in>roots. \<forall>lq\<in>roots. lp \<noteq> lq \<longrightarrow>
      set (ring (fam' lp)) \<inter> set (ring (fam' lq)) = {}"
    unfolding fam'_def
    by (rule scheduler_family_insert_end_rings_disjoint[
          OF pre target absent])
  have membership: "raw_family_members roots fam' p = {target}"
    unfolding fam'_def
    by (rule scheduler_family_insert_end_membership[
          OF pre target absent])
  show ?thesis using ring_subset rings_disjoint membership by simp
qed

end
