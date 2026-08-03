theory Scheduler_Family_Insert_End_Raw_Family
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Family_Insert_End_Storage_Frame.Scheduler_Family_Insert_End_Storage_Frame"
begin

definition scheduler_family_insert_end_raw ::
  "heap_mem \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   xLIST_C ptr \<Rightarrow> raw_node_id \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs)"
where
  "scheduler_family_insert_end_raw h fam target p =
     fam(target := list_insert_end_abs p (raw_key_at h p) (fam target))"

theorem scheduler_family_insert_end_raw_family_rel:
  assumes pre: "scheduler_family_pre_rel h roots fam live D"
    and target: "target \<in> roots"
    and fresh: "raw_fresh_for_insert target (ring (fam target)) p"
    and managed: "p \<in> universal_managed_nodes live D"
    and absent: "raw_family_members roots fam p = {}"
  defines
    "h' \<equiv> raw_insert_concrete_heap h target (fam target) p"
    and "fam' \<equiv> scheduler_family_insert_end_raw h fam target p"
  shows "raw_family_rel h' roots fam'"
proof -
  have target_rel: "raw_xlist_rel h target (fam target)"
    using pre target
    by (auto simp: scheduler_family_pre_rel_def raw_family_rel_def)
  have capacity: "raw_count_can_increment (fam target)"
    by (rule raw_xlist_rel_fresh_count_can_increment[OF target_rel fresh])
  have target_post:
    "raw_xlist_rel h' target
       (list_insert_end_abs p (raw_key_at h p) (fam target))"
    unfolding h'_def
    by (rule raw_insert_concrete_heap_refines[
      OF target_rel fresh capacity])
  have other_post:
    "\<And>lp. lp \<in> roots \<Longrightarrow> lp \<noteq> target \<Longrightarrow>
      raw_xlist_rel h' lp (fam lp)"
  proof -
    fix lp
    assume root: "lp \<in> roots" and different: "lp \<noteq> target"
    have old: "raw_xlist_rel h lp (fam lp)"
      using pre root
      by (auto simp: scheduler_family_pre_rel_def raw_family_rel_def)
    show "raw_xlist_rel h' lp (fam lp)"
      unfolding h'_def
    proof (rule insert_family_raw_xlist_rel_storage_frame[OF old])
      fix address
      assume address: "address \<in> raw_xlist_storage lp (fam lp)"
      show
        "raw_insert_concrete_heap h target (fam target) p address = h address"
        by (rule raw_insert_end_family_non_target_byte_frame[
          OF pre target root _ fresh managed absent address])
           (use different in simp)
    qed
  qed
  show ?thesis
    unfolding raw_family_rel_def
  proof (intro conjI ballI)
    show "finite roots"
      using pre
      by (simp add: scheduler_family_pre_rel_def raw_family_rel_def)
  next
    fix lp
    assume root: "lp \<in> roots"
    show "raw_xlist_rel h' lp (fam' lp)"
    proof (cases "lp = target")
      case True
      then show ?thesis
        using target_post by (simp add: fam'_def
            scheduler_family_insert_end_raw_def)
    next
      case False
      then show ?thesis
        using other_post[OF root False]
        by (simp add: fam'_def scheduler_family_insert_end_raw_def)
    qed
  qed
qed

end
