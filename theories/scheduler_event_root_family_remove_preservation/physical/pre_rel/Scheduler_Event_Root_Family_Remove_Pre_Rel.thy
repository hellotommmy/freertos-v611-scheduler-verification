theory Scheduler_Event_Root_Family_Remove_Pre_Rel
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Event_Root_Family_Remove_Relabel.Scheduler_Event_Root_Family_Remove_Relabel"
    "EAL6_FreeRTOS_V611_Scheduler_Delay_Suspended_Core.Scheduler_Delay_Suspended_Core"
begin

text \<open>The next brick reconstructs the complete physical family relation.
  The target root follows the exact concrete remove effect.  Every other root
  follows from the checked byte-footprint frame, not from a post-relation
  premise.\<close>

lemma scheduler_event_root_family_remove_pre_rel:
  assumes rel:
      "scheduler_event_root_family_rel
         D h roots pending raw_fam abs_fam live K_E"
    and owner: "owner \<in> roots"
    and removed_live: "t \<in> live"
    and member:
      "event_item_raw_ptr D t \<in> set (ring (raw_fam owner))"
  shows
    "scheduler_family_pre_rel
       (raw_remove_concrete_heap h (event_item_raw_ptr D t)) roots
       (event_remove_raw_family raw_fam owner (event_item_raw_ptr D t))
       live D"
proof -
  let ?p = "event_item_raw_ptr D t"
  let ?h' = "raw_remove_concrete_heap h ?p"
  let ?fam' = "event_remove_raw_family raw_fam owner ?p"
  have pre: "scheduler_family_pre_rel h roots raw_fam live D"
    by (rule scheduler_event_root_family_preD[OF rel])
  have target_rel: "raw_xlist_rel ?h' owner (list_remove_abs ?p (raw_fam owner))"
  proof -
    have raw: "raw_xlist_rel h owner (raw_fam owner)"
      by (rule scheduler_event_root_family_raw_rootD[OF rel owner])
    have unlinked:
      "raw_remove_unlinked_effect h ?h' owner (raw_fam owner) ?p"
      by (rule raw_remove_concrete_heap_unlinked_effect[OF raw member])
    have effect: "raw_remove_effect h ?h' owner (raw_fam owner) ?p"
      using unlinked by (simp add: raw_remove_unlinked_effect_def)
    show ?thesis by (rule raw_remove_effect_refines[OF raw member effect])
  qed
  have other_rel:
    "\<And>lp. lp \<in> roots \<Longrightarrow> lp \<noteq> owner \<Longrightarrow>
      raw_xlist_rel ?h' lp (raw_fam lp)"
  proof -
    fix lp
    assume lp_root: "lp \<in> roots" and different: "lp \<noteq> owner"
    have raw: "raw_xlist_rel h lp (raw_fam lp)"
      by (rule scheduler_event_root_family_raw_rootD[OF rel lp_root])
    show "raw_xlist_rel ?h' lp (raw_fam lp)"
    proof (rule delay_raw_xlist_rel_storage_frame[OF raw])
      fix a
      assume address: "a \<in> raw_xlist_storage lp (raw_fam lp)"
      show "?h' a = h a"
        by (rule raw_remove_family_non_target_byte_frame[
              OF pre owner lp_root _ member address])
           (use different in auto)
    qed
  qed
  have family_post: "raw_family_rel ?h' roots ?fam'"
    unfolding raw_family_rel_def
  proof (intro conjI ballI)
    show "finite roots"
      using pre by (simp add: scheduler_family_pre_rel_def raw_family_rel_def)
  next
    fix lp
    assume lp_root: "lp \<in> roots"
    show "raw_xlist_rel ?h' lp (?fam' lp)"
    proof (cases "lp = owner")
      case True
      show ?thesis
        using target_rel True by (simp add: event_remove_raw_family_def)
    next
      case False
      show ?thesis
        using other_rel[OF lp_root False] False
        by (simp add: event_remove_raw_family_def)
    qed
  qed
  have geometry: "universal_tcb_geometry live D"
    using pre by (simp add: scheduler_family_pre_rel_def)
  have ring_subset:
    "\<And>lp. lp \<in> roots \<Longrightarrow>
      set (ring (?fam' lp)) \<subseteq> set (ring (raw_fam lp))"
  proof -
    fix lp
    assume lp_root: "lp \<in> roots"
    show "set (ring (?fam' lp)) \<subseteq> set (ring (raw_fam lp))"
    proof (cases "lp = owner")
      case True
      show ?thesis
        using set_remove1_subset[of ?p "ring (raw_fam owner)"] True
        by (simp add: event_remove_raw_family_def list_remove_abs_def)
    next
      case False
      show ?thesis by (simp add: event_remove_raw_family_def False)
    qed
  qed
  have managed:
    "\<forall>lp\<in>roots.
       set (ring (?fam' lp)) \<subseteq> universal_managed_nodes live D"
  proof (intro ballI)
    fix lp
    assume lp_root: "lp \<in> roots"
    have old:
      "set (ring (raw_fam lp)) \<subseteq> universal_managed_nodes live D"
      using pre lp_root by (auto simp: scheduler_family_pre_rel_def)
    show
      "set (ring (?fam' lp)) \<subseteq> universal_managed_nodes live D"
      using ring_subset[OF lp_root] old by (rule subset_trans)
  qed
  have root_separate:
    "\<forall>lp\<in>roots. \<forall>lq\<in>roots. lp \<noteq> lq \<longrightarrow>
       raw_list_region lp \<inter> raw_list_region lq = {}"
    using pre by (simp add: scheduler_family_pre_rel_def)
  have root_tcb:
    "\<forall>lp\<in>roots. \<forall>u\<in>live.
       raw_list_region lp \<inter>
         universal_tcb_region (sd_tcb_ptr D u) = {}"
    using pre by (simp add: scheduler_family_pre_rel_def)
  have rings_separate:
    "\<forall>lp\<in>roots. \<forall>lq\<in>roots. lp \<noteq> lq \<longrightarrow>
       set (ring (?fam' lp)) \<inter> set (ring (?fam' lq)) = {}"
  proof (intro ballI impI)
    fix lp
    assume lp_root: "lp \<in> roots"
    fix lq
    assume lq_root: "lq \<in> roots" and different: "lp \<noteq> lq"
    have old:
      "set (ring (raw_fam lp)) \<inter> set (ring (raw_fam lq)) = {}"
      using pre lp_root lq_root different
      by (auto simp: scheduler_family_pre_rel_def)
    show "set (ring (?fam' lp)) \<inter> set (ring (?fam' lq)) = {}"
      using ring_subset[OF lp_root] ring_subset[OF lq_root] old by blast
  qed
  show ?thesis
    using family_post geometry managed root_separate root_tcb rings_separate
    by (simp add: scheduler_family_pre_rel_def)
qed

end
