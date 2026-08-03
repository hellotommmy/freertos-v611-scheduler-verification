theory Scheduler_Family_Insert_End_Preservation
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Family_Insert_End_Shape.Scheduler_Family_Insert_End_Shape"
begin

theorem scheduler_family_insert_end_pre_rel_and_linked:
  assumes pre: "scheduler_family_pre_rel h roots fam live D"
    and target: "target \<in> roots"
    and fresh: "raw_fresh_for_insert target (ring (fam target)) p"
    and managed: "p \<in> universal_managed_nodes live D"
    and absent: "raw_family_members roots fam p = {}"
  defines
    "h' \<equiv> raw_insert_concrete_heap h target (fam target) p"
    and "fam' \<equiv> scheduler_family_insert_end_raw h fam target p"
  shows
    "scheduler_family_pre_rel h' roots fam' live D \<and>
     raw_family_members roots fam' p = {target} \<and>
     raw_key_at h' p = raw_key_at h p \<and>
     pvContainer_C (h_val h' p) = PTR_COERCE(xLIST_C \<rightarrow> unit) target"
proof -
  have target_rel: "raw_xlist_rel h target (fam target)"
    using pre target
    by (auto simp: scheduler_family_pre_rel_def raw_family_rel_def)
  have family_post: "raw_family_rel h' roots fam'"
    unfolding h'_def fam'_def
    by (rule scheduler_family_insert_end_raw_family_rel[
          OF pre target fresh managed absent])
  have shape:
    "(\<forall>lp\<in>roots.
       set (ring (fam' lp)) \<subseteq> universal_managed_nodes live D) \<and>
     (\<forall>lp\<in>roots. \<forall>lq\<in>roots. lp \<noteq> lq \<longrightarrow>
       set (ring (fam' lp)) \<inter> set (ring (fam' lq)) = {}) \<and>
     raw_family_members roots fam' p = {target}"
    unfolding fam'_def
    by (rule scheduler_family_insert_end_shape[
          OF pre target managed absent])
  have pre_post: "scheduler_family_pre_rel h' roots fam' live D"
    using pre family_post shape
    by (simp add: scheduler_family_pre_rel_def)
  have payload:
    "raw_key_at h' p = raw_key_at h p \<and>
     pvContainer_C (h_val h' p) = PTR_COERCE(xLIST_C \<rightarrow> unit) target"
    unfolding h'_def
    by (rule raw_insert_concrete_heap_new_payload_effect[
      OF target_rel fresh])
  show ?thesis
    using pre_post shape payload by simp
qed

end
