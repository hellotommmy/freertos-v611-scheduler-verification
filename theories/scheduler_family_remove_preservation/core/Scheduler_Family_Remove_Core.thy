theory Scheduler_Family_Remove_Core
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Event_Root_Family_Remove_Relabel.Scheduler_Event_Root_Family_Remove_Relabel"
    "EAL6_FreeRTOS_V611_Scheduler_Delay_Suspended_Core.Scheduler_Delay_Suspended_Core"
begin

text \<open>
  Kind-agnostic family removal.  The removed raw node, its decoded scheduler
  node, the protected roots, the live-task universe, all keys, the ring
  length, the cursor position, and the owner root remain universally
  quantified.  The only branch premise is the source-level vListRemove guard:
  the raw node is a member of the selected owner ring.
\<close>

definition scheduler_family_remove_raw ::
  "(xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   xLIST_C ptr \<Rightarrow> raw_node_id \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs)"
where
  "scheduler_family_remove_raw fam owner p =
     fam(owner := list_remove_abs p (fam owner))"

definition scheduler_family_remove_abs ::
  "(xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow>
   xLIST_C ptr \<Rightarrow> 'tid node_kind \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring)"
where
  "scheduler_family_remove_abs fam owner n =
     fam(owner := list_remove_abs n (fam owner))"

lemma scheduler_family_remove_raw_ring_subset:
  "set (ring (scheduler_family_remove_raw fam owner p lp))
     \<subseteq> set (ring (fam lp))"
proof (cases "lp = owner")
  case True
  show ?thesis
    using set_remove1_subset[of p "ring (fam owner)"] True
    by (simp add: scheduler_family_remove_raw_def list_remove_abs_def)
next
  case False
  show ?thesis by (simp add: scheduler_family_remove_raw_def False)
qed

lemma scheduler_family_remove_raw_membership_frame:
  assumes different: "q \<noteq> p"
  shows
    "q \<in> set (ring (scheduler_family_remove_raw fam owner p lp))
       \<longleftrightarrow> q \<in> set (ring (fam lp))"
  using different
  by (cases "lp = owner")
     (simp_all add: scheduler_family_remove_raw_def list_remove_abs_def)

lemma scheduler_family_remove_abs_membership_frame:
  assumes different: "m \<noteq> n"
  shows
    "m \<in> set (ring (scheduler_family_remove_abs fam owner n lp))
       \<longleftrightarrow> m \<in> set (ring (fam lp))"
  using different
  by (cases "lp = owner")
     (simp_all add: scheduler_family_remove_abs_def list_remove_abs_def)

lemma scheduler_family_remove_specific_subset_preserved:
  assumes old:
    "\<And>lp. lp \<in> roots \<Longrightarrow>
      set (ring (fam lp)) \<subseteq> managed"
  shows
    "\<And>lp. lp \<in> roots \<Longrightarrow>
      set (ring (scheduler_family_remove_raw fam owner p lp))
        \<subseteq> managed"
proof -
  fix lp
  assume lp_root: "lp \<in> roots"
  show
    "set (ring (scheduler_family_remove_raw fam owner p lp))
       \<subseteq> managed"
    using scheduler_family_remove_raw_ring_subset[of fam owner p lp]
      old[OF lp_root]
    by (rule subset_trans)
qed

lemma scheduler_family_remove_unique_owner:
  assumes pre: "scheduler_family_pre_rel h roots fam live D"
    and owner: "owner \<in> roots"
    and member: "p \<in> set (ring (fam owner))"
  shows "raw_family_members roots fam p = {owner}"
proof (rule set_eqI)
  fix lp
  show "lp \<in> raw_family_members roots fam p \<longleftrightarrow> lp \<in> {owner}"
  proof
    assume lp_member: "lp \<in> raw_family_members roots fam p"
    have lp_root: "lp \<in> roots"
      and p_member: "p \<in> set (ring (fam lp))"
      using lp_member by (auto simp: raw_family_members_def)
    show "lp \<in> {owner}"
    proof (rule ccontr)
      assume "lp \<notin> {owner}"
      then have different: "lp \<noteq> owner" by simp
      have disjoint:
        "set (ring (fam lp)) \<inter> set (ring (fam owner)) = {}"
        using pre lp_root owner different
        by (auto simp: scheduler_family_pre_rel_def)
      show False using disjoint p_member member by blast
    qed
  next
    assume "lp \<in> {owner}"
    then show "lp \<in> raw_family_members roots fam p"
      using owner member by (simp add: raw_family_members_def)
  qed
qed

lemma scheduler_family_remove_owner_raw_rel:
  assumes pre: "scheduler_family_pre_rel h roots fam live D"
    and owner: "owner \<in> roots"
    and member: "p \<in> set (ring (fam owner))"
  shows
    "raw_xlist_rel (raw_remove_concrete_heap h p) owner
       (list_remove_abs p (fam owner))"
proof -
  have raw: "raw_xlist_rel h owner (fam owner)"
    using pre owner
    by (auto simp: scheduler_family_pre_rel_def raw_family_rel_def)
  have unlinked:
    "raw_remove_unlinked_effect h (raw_remove_concrete_heap h p)
       owner (fam owner) p"
    by (rule raw_remove_concrete_heap_unlinked_effect[OF raw member])
  have effect:
    "raw_remove_effect h (raw_remove_concrete_heap h p)
       owner (fam owner) p"
    using unlinked by (simp add: raw_remove_unlinked_effect_def)
  show ?thesis by (rule raw_remove_effect_refines[OF raw member effect])
qed

lemma scheduler_family_remove_non_target_raw_rel:
  assumes pre: "scheduler_family_pre_rel h roots fam live D"
    and owner: "owner \<in> roots"
    and other: "other \<in> roots"
    and different: "other \<noteq> owner"
    and member: "p \<in> set (ring (fam owner))"
  shows "raw_xlist_rel (raw_remove_concrete_heap h p) other (fam other)"
proof -
  have raw: "raw_xlist_rel h other (fam other)"
    using pre other
    by (auto simp: scheduler_family_pre_rel_def raw_family_rel_def)
  show ?thesis
  proof (rule delay_raw_xlist_rel_storage_frame[OF raw])
    fix a
    assume address: "a \<in> raw_xlist_storage other (fam other)"
    show "raw_remove_concrete_heap h p a = h a"
      by (rule raw_remove_family_non_target_byte_frame[
            OF pre owner other _ member address])
         (use different in auto)
  qed
qed

theorem scheduler_family_remove_pre_rel_and_unlinked:
  assumes pre: "scheduler_family_pre_rel h roots fam live D"
    and owner: "owner \<in> roots"
    and member: "p \<in> set (ring (fam owner))"
  shows
    "scheduler_family_pre_rel (raw_remove_concrete_heap h p) roots
       (scheduler_family_remove_raw fam owner p) live D \<and>
     raw_family_globally_unlinked (raw_remove_concrete_heap h p) roots
       (scheduler_family_remove_raw fam owner p) p"
proof -
  let ?h' = "raw_remove_concrete_heap h p"
  let ?fam' = "scheduler_family_remove_raw fam owner p"
  have target:
    "raw_xlist_rel ?h' owner (list_remove_abs p (fam owner))"
    by (rule scheduler_family_remove_owner_raw_rel[OF pre owner member])
  have others:
    "\<And>lp. lp \<in> roots \<Longrightarrow> lp \<noteq> owner \<Longrightarrow>
      raw_xlist_rel ?h' lp (fam lp)"
  proof -
    fix lp
    assume lp_root: "lp \<in> roots" and different: "lp \<noteq> owner"
    show "raw_xlist_rel ?h' lp (fam lp)"
      by (rule scheduler_family_remove_non_target_raw_rel[
            OF pre owner lp_root different member])
  qed
  have family: "raw_family_rel h roots fam"
    using pre by (simp add: scheduler_family_pre_rel_def)
  have unique: "raw_family_members roots fam p = {owner}"
    by (rule scheduler_family_remove_unique_owner[OF pre owner member])
  have raw: "raw_xlist_rel h owner (fam owner)"
    using pre owner
    by (auto simp: scheduler_family_pre_rel_def raw_family_rel_def)
  have removed_null: "pvContainer_C (h_val ?h' p) = NULL"
    using raw_remove_concrete_heap_removed_item_effect[OF raw member]
    by simp
  have family_and_unlinked:
    "raw_family_rel ?h' roots
       (fam(owner := list_remove_abs p (fam owner))) \<and>
     raw_family_globally_unlinked ?h' roots
       (fam(owner := list_remove_abs p (fam owner))) p"
    by (rule raw_family_remove_owner_globally_unlinked[
          OF family owner unique target others removed_null])
  have family_post: "raw_family_rel ?h' roots ?fam'"
    using family_and_unlinked
    by (simp add: scheduler_family_remove_raw_def)
  have unlinked:
    "raw_family_globally_unlinked ?h' roots ?fam' p"
    using family_and_unlinked
    by (simp add: scheduler_family_remove_raw_def)
  have geometry: "universal_tcb_geometry live D"
    using pre by (simp add: scheduler_family_pre_rel_def)
  have managed:
    "\<forall>lp\<in>roots.
       set (ring (?fam' lp)) \<subseteq> universal_managed_nodes live D"
  proof (intro ballI)
    fix lp
    assume lp_root: "lp \<in> roots"
    have old:
      "set (ring (fam lp)) \<subseteq> universal_managed_nodes live D"
      using pre lp_root by (auto simp: scheduler_family_pre_rel_def)
    show
      "set (ring (?fam' lp)) \<subseteq> universal_managed_nodes live D"
      using scheduler_family_remove_raw_ring_subset[of fam owner p lp] old
      by (rule subset_trans)
  qed
  have root_separate:
    "\<forall>lp\<in>roots. \<forall>lq\<in>roots. lp \<noteq> lq \<longrightarrow>
       raw_list_region lp \<inter> raw_list_region lq = {}"
    using pre by (simp add: scheduler_family_pre_rel_def)
  have root_tcb:
    "\<forall>lp\<in>roots. \<forall>t\<in>live.
       raw_list_region lp \<inter>
         universal_tcb_region (sd_tcb_ptr D t) = {}"
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
      "set (ring (fam lp)) \<inter> set (ring (fam lq)) = {}"
      using pre lp_root lq_root different
      by (auto simp: scheduler_family_pre_rel_def)
    show "set (ring (?fam' lp)) \<inter> set (ring (?fam' lq)) = {}"
      using scheduler_family_remove_raw_ring_subset[of fam owner p lp]
        scheduler_family_remove_raw_ring_subset[of fam owner p lq] old
      by blast
  qed
  have post: "scheduler_family_pre_rel ?h' roots ?fam' live D"
    using family_post geometry managed root_separate root_tcb rings_separate
    by (simp add: scheduler_family_pre_rel_def)
  show ?thesis using post unlinked by simp
qed

corollary scheduler_family_remove_pre_rel_preserved:
  assumes pre: "scheduler_family_pre_rel h roots fam live D"
    and owner: "owner \<in> roots"
    and member: "p \<in> set (ring (fam owner))"
  shows
    "scheduler_family_pre_rel (raw_remove_concrete_heap h p) roots
       (scheduler_family_remove_raw fam owner p) live D"
  using scheduler_family_remove_pre_rel_and_unlinked[OF pre owner member]
  by simp

lemma scheduler_family_remove_item_effect:
  assumes pre: "scheduler_family_pre_rel h roots fam live D"
    and owner: "owner \<in> roots"
    and member: "p \<in> set (ring (fam owner))"
  shows
    "raw_key_at (raw_remove_concrete_heap h p) p = raw_key_at h p \<and>
     pvContainer_C (h_val (raw_remove_concrete_heap h p) p) = NULL \<and>
     xLIST_ITEM_C.pxNext_C
       (h_val (raw_remove_concrete_heap h p) p) =
       xLIST_ITEM_C.pxNext_C (h_val h p) \<and>
     xLIST_ITEM_C.pxPrevious_C
       (h_val (raw_remove_concrete_heap h p) p) =
       xLIST_ITEM_C.pxPrevious_C (h_val h p)"
proof -
  have raw: "raw_xlist_rel h owner (fam owner)"
    using pre owner
    by (auto simp: scheduler_family_pre_rel_def raw_family_rel_def)
  show ?thesis
    using raw_remove_concrete_heap_preserves_item_key[OF raw member]
      raw_remove_concrete_heap_removed_item_effect[OF raw member]
    by simp
qed

lemma scheduler_family_remove_nonmember_item_byte_frame:
  assumes pre: "scheduler_family_pre_rel h roots fam live D"
    and owner: "owner \<in> roots"
    and member: "p \<in> set (ring (fam owner))"
    and managed: "q \<in> universal_managed_nodes live D"
    and nonmember: "q \<notin> set (ring (fam owner))"
  shows
    "\<forall>a\<in>raw_item_region q. raw_remove_concrete_heap h p a = h a"
proof -
  obtain u where u_live: "u \<in> live"
    using managed by (auto simp: universal_managed_nodes_def)
  show ?thesis
    using raw_remove_family_sibling_item_priority_byte_frame[
      OF pre owner member managed nonmember u_live]
    by blast
qed

lemma scheduler_family_remove_priority_byte_frame:
  assumes pre: "scheduler_family_pre_rel h roots fam live D"
    and owner: "owner \<in> roots"
    and member: "p \<in> set (ring (fam owner))"
    and task_live: "u \<in> live"
  shows
    "\<forall>a\<in>universal_priority_field_region (sd_tcb_ptr D u).
       raw_remove_concrete_heap h p a = h a"
proof (intro ballI)
  fix a
  assume address:
    "a \<in> universal_priority_field_region (sd_tcb_ptr D u)"
  have raw: "raw_xlist_rel h owner (fam owner)"
    using pre owner
    by (auto simp: scheduler_family_pre_rel_def raw_family_rel_def)
  have footprint:
    "raw_remove_exact_write_footprint h owner p
       \<subseteq> raw_xlist_storage owner (fam owner)"
    by (rule raw_remove_exact_footprint_subset_storage[OF raw member])
  have disjoint:
    "raw_xlist_storage owner (fam owner) \<inter>
       universal_priority_field_region (sd_tcb_ptr D u) = {}"
    by (rule scheduler_family_target_storage_priority_disjoint[
          OF pre owner task_live])
  have outside: "a \<notin> raw_remove_exact_write_footprint h owner p"
    using footprint disjoint address by blast
  show "raw_remove_concrete_heap h p a = h a"
    by (rule raw_remove_concrete_heap_exact_external_frame[
          OF raw member outside])
qed

lemma scheduler_family_remove_managed_payload_frame:
  assumes pre: "scheduler_family_pre_rel h roots fam live D"
    and owner: "owner \<in> roots"
    and member: "p \<in> set (ring (fam owner))"
    and managed: "q \<in> universal_managed_nodes live D"
    and different: "q \<noteq> p"
  shows
    "raw_key_at (raw_remove_concrete_heap h p) q = raw_key_at h q \<and>
     pvContainer_C (h_val (raw_remove_concrete_heap h p) q) =
       pvContainer_C (h_val h q)"
proof (cases "q \<in> set (ring (fam owner))")
  case True
  have remaining: "q \<in> set (remove1 p (ring (fam owner)))"
    using True different by simp
  have raw: "raw_xlist_rel h owner (fam owner)"
    using pre owner
    by (auto simp: scheduler_family_pre_rel_def raw_family_rel_def)
  show ?thesis
    using raw_remove_concrete_heap_payload_effect[OF raw member] remaining
    by blast
next
  case False
  have byte_frame:
    "\<forall>a\<in>raw_item_region q. raw_remove_concrete_heap h p a = h a"
    by (rule scheduler_family_remove_nonmember_item_byte_frame[
          OF pre owner member managed False])
  have item_same:
    "h_val (raw_remove_concrete_heap h p) q = h_val h q"
  proof (rule delay_h_val_region_cong)
    fix a
    assume address: "a \<in> {ptr_val q..+size_of TYPE(xLIST_ITEM_C)}"
    show "raw_remove_concrete_heap h p a = h a"
      using byte_frame address by (simp add: raw_item_region_def)
  qed
  show ?thesis using item_same by (simp add: raw_key_at_def)
qed

lemma scheduler_family_remove_managed_keys_preserved:
  assumes pre: "scheduler_family_pre_rel h roots fam live D"
    and owner: "owner \<in> roots"
    and member: "p \<in> set (ring (fam owner))"
    and keys:
      "\<And>q. q \<in> universal_managed_nodes live D \<Longrightarrow>
        raw_key_at h q = key_of q"
  shows
    "\<And>q. q \<in> universal_managed_nodes live D \<Longrightarrow>
      raw_key_at (raw_remove_concrete_heap h p) q = key_of q"
proof -
  fix q
  assume q_managed: "q \<in> universal_managed_nodes live D"
  show "raw_key_at (raw_remove_concrete_heap h p) q = key_of q"
  proof (cases "q = p")
    case True
    show ?thesis
      using scheduler_family_remove_item_effect[OF pre owner member]
        keys[OF q_managed] True
      by simp
  next
    case False
    show ?thesis
      using scheduler_family_remove_managed_payload_frame[
          OF pre owner member q_managed False]
        keys[OF q_managed]
      by simp
  qed
qed

theorem scheduler_family_remove_container_faithful_on_preserved:
  assumes pre: "scheduler_family_pre_rel h roots fam live D"
    and faithful:
      "raw_family_container_faithful_on h roots fam
         (universal_managed_nodes live D)"
    and owner: "owner \<in> roots"
    and member: "p \<in> set (ring (fam owner))"
  shows
    "raw_family_container_faithful_on (raw_remove_concrete_heap h p) roots
       (scheduler_family_remove_raw fam owner p)
       (universal_managed_nodes live D)"
proof -
  let ?h' = "raw_remove_concrete_heap h p"
  let ?fam' = "scheduler_family_remove_raw fam owner p"
  have p_managed: "p \<in> universal_managed_nodes live D"
    using pre owner member by (auto simp: scheduler_family_pre_rel_def)
  have unlinked: "raw_family_globally_unlinked ?h' roots ?fam' p"
    using scheduler_family_remove_pre_rel_and_unlinked[OF pre owner member]
    by simp
  have absent: "raw_family_members roots ?fam' p = {}"
    using unlinked by (simp add: raw_family_globally_unlinked_def)
  have removed_null: "pvContainer_C (h_val ?h' p) = NULL"
    using unlinked by (simp add: raw_family_globally_unlinked_def)
  show ?thesis
  proof (rule raw_family_container_faithful_on_preserved[
        OF faithful p_managed absent])
    fix lp q
    assume lp_root: "lp \<in> roots"
      and q_managed: "q \<in> universal_managed_nodes live D"
      and q_ne: "q \<noteq> p"
    show
      "q \<in> set (ring (?fam' lp)) \<longleftrightarrow>
       q \<in> set (ring (fam lp))"
      by (rule scheduler_family_remove_raw_membership_frame[OF q_ne])
  next
    fix q
    assume q_managed: "q \<in> universal_managed_nodes live D"
      and q_ne: "q \<noteq> p"
    show "pvContainer_C (h_val ?h' q) = pvContainer_C (h_val h q)"
      using scheduler_family_remove_managed_payload_frame[
        OF pre owner member q_managed q_ne]
      by simp
  next
    show "pvContainer_C (h_val ?h' p) = NULL" by (rule removed_null)
  qed
qed

end
