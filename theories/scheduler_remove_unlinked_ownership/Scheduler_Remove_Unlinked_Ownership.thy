theory Scheduler_Remove_Unlinked_Ownership
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Ordered_Insert_General_Refinement.Scheduler_Ordered_Insert_General_Refinement"
    "EAL6_FreeRTOS_V611_List_Raw_R6_Remove_General_Refinement.List_V611_Raw_R6_Remove_General_Refinement"
begin

text \<open>
  Universal removal-to-unlinked ownership bridge.  Quantifier ledger:
  arbitrary heap, source root, finite protected-root family, family model,
  removed item, ring length, item position, cursor, predecessor and successor.
  No task count, priority, address, singleton shape, or cursor branch is fixed.
\<close>

lemma raw_remove_container_heap_to_field:
  assumes guard: "c_guard p"
  shows
    "raw_remove_container_heap h p =
     heap_update (raw_container_field_ptr p) NULL h"
  unfolding raw_remove_container_heap_def raw_container_field_ptr_def
  apply (rule sym)
  by (rule xLIST_ITEM_C_heap_update_fields(5)[OF guard])

lemma raw_remove_count_heap_to_field:
  assumes guard: "c_guard lp"
  shows
    "raw_remove_count_heap h lp =
     heap_update (raw_count_field_ptr lp)
       (uxNumberOfItems_C (h_val h lp) - 1) h"
  unfolding raw_remove_count_heap_def raw_count_field_ptr_def
  apply (subst raw_count_update_to_constant)
  apply (rule sym)
  by (rule xLIST_C_heap_update_fields(1)[OF guard])

lemma raw_remove_taken_index_heap_to_field:
  assumes guard: "c_guard lp"
  shows
    "heap_update lp
       (pxIndex_C_update (\<lambda>_. q) (h_val h lp)) h =
     heap_update (raw_index_field_ptr lp) q h"
  unfolding raw_index_field_ptr_def
  apply (rule sym)
  by (rule xLIST_C_heap_update_fields(2)[OF guard])

lemma heap_update_raw_index_field_external_frame:
  assumes outside: "a \<notin> raw_index_field_region lp"
  shows "heap_update (raw_index_field_ptr lp) v h a = h a"
  unfolding heap_update_def raw_index_field_region_def
  apply (rule heap_update_nmem_same)
  using outside by (simp add: raw_index_field_region_def)

definition raw_remove_exact_write_footprint ::
  "heap_mem \<Rightarrow> xLIST_C ptr \<Rightarrow> raw_node_id \<Rightarrow> addr set"
where
  "raw_remove_exact_write_footprint h lp p =
     raw_pointer_field_region
       (raw_previous_field_ptr (xLIST_ITEM_C.pxNext_C (h_val h p))) \<union>
     raw_pointer_field_region
       (raw_next_field_ptr (xLIST_ITEM_C.pxPrevious_C (h_val h p))) \<union>
     raw_index_field_region lp \<union>
     raw_container_field_region p \<union>
     raw_count_field_region lp"

lemma raw_remove_concrete_heap_removed_item_effect:
  assumes rel: "raw_xlist_rel h lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "pvContainer_C (h_val (raw_remove_concrete_heap h p) p) = NULL \<and>
     xLIST_ITEM_C.pxNext_C (h_val (raw_remove_concrete_heap h p) p) =
       xLIST_ITEM_C.pxNext_C (h_val h p) \<and>
     xLIST_ITEM_C.pxPrevious_C (h_val (raw_remove_concrete_heap h p) p) =
       xLIST_ITEM_C.pxPrevious_C (h_val h p)"
proof -
  let ?hu = "raw_source_unlink_two h p"
  let ?hi = "raw_remove_index_heap ?hu lp p"
  let ?hc = "raw_remove_container_heap ?hi p"
  have layout: "raw_xlist_layout lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def)
  have p_guard: "c_guard p"
    using layout member by (auto simp: raw_xlist_layout_def)
  have item_list: "raw_item_region p \<inter> raw_list_region lp = {}"
    using layout member by (auto simp: raw_xlist_layout_def)
  have unlink_same: "h_val ?hu p = h_val h p"
    by (rule raw_source_unlink_two_item_same[OF rel member])
  have index_same: "h_val ?hi p = h_val ?hu p"
  proof (cases "pxIndex_C (h_val ?hu lp) = p")
    case True
    show ?thesis
      unfolding raw_remove_index_heap_def
      apply (simp only: if_P[OF True])
      by (rule
        List_V611_Raw_R6_Remove_Topology_Effect.raw_list_update_preserves_disjoint_item[
          OF item_list])
  next
    case False
    show ?thesis
      unfolding raw_remove_index_heap_def by (simp only: if_not_P[OF False])
  qed
  have container_readback:
    "pvContainer_C (h_val ?hc p) = NULL \<and>
     xLIST_ITEM_C.pxNext_C (h_val ?hc p) =
       xLIST_ITEM_C.pxNext_C (h_val ?hi p) \<and>
     xLIST_ITEM_C.pxPrevious_C (h_val ?hc p) =
       xLIST_ITEM_C.pxPrevious_C (h_val ?hi p)"
    unfolding raw_remove_container_heap_def
    using p_guard by (simp add: h_val_heap_update)
  have count_same:
    "h_val (raw_remove_count_heap ?hc lp) p = h_val ?hc p"
    unfolding raw_remove_count_heap_def
    by (rule
      List_V611_Raw_R6_Remove_Topology_Effect.raw_list_update_preserves_disjoint_item[
        OF item_list])
  have concrete:
    "raw_remove_concrete_heap h p = raw_remove_source_heap h lp p"
    by (rule raw_remove_concrete_heap_eq[OF rel member])
  show ?thesis
    using concrete unlink_same index_same container_readback count_same
    by (simp add: raw_remove_source_heap_def raw_remove_suffix_heap_def)
qed

theorem raw_remove_concrete_heap_exact_external_frame:
  assumes rel: "raw_xlist_rel h lp xs"
    and member: "p \<in> set (ring xs)"
    and outside: "a \<notin> raw_remove_exact_write_footprint h lp p"
  shows "raw_remove_concrete_heap h p a = h a"
proof -
  let ?h1 = "raw_source_unlink_first h p"
  let ?hu = "raw_source_unlink_two h p"
  let ?hi = "raw_remove_index_heap ?hu lp p"
  let ?hc = "raw_remove_container_heap ?hi p"
  have layout: "raw_xlist_layout lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def)
  have p_guard: "c_guard p"
    using layout member by (auto simp: raw_xlist_layout_def)
  have lp_guard: "c_guard lp"
    using layout by (simp add: raw_xlist_layout_def)
  have h1_item: "h_val ?h1 p = h_val h p"
    unfolding raw_source_unlink_first_def
    by (rule raw_remove_first_unlink_preserves_item[OF rel member])
  have source_two:
    "?hu =
     heap_update
       (raw_next_field_ptr (xLIST_ITEM_C.pxPrevious_C (h_val h p)))
       (xLIST_ITEM_C.pxNext_C (h_val h p)) ?h1"
    unfolding raw_source_unlink_two_def
    using h1_item by simp
  have out_first:
    "a \<notin> raw_pointer_field_region
       (raw_previous_field_ptr (xLIST_ITEM_C.pxNext_C (h_val h p)))"
    using outside by (simp add: raw_remove_exact_write_footprint_def)
  have out_second:
    "a \<notin> raw_pointer_field_region
       (raw_next_field_ptr (xLIST_ITEM_C.pxPrevious_C (h_val h p)))"
    using outside by (simp add: raw_remove_exact_write_footprint_def)
  have out_index: "a \<notin> raw_index_field_region lp"
    using outside by (simp add: raw_remove_exact_write_footprint_def)
  have out_container: "a \<notin> raw_container_field_region p"
    using outside by (simp add: raw_remove_exact_write_footprint_def)
  have out_count: "a \<notin> raw_count_field_region lp"
    using outside by (simp add: raw_remove_exact_write_footprint_def)
  have h1: "?h1 a = h a"
    unfolding raw_source_unlink_first_def
    by (rule heap_update_raw_pointer_field_external_frame[OF out_first])
  have hu: "?hu a = ?h1 a"
    unfolding source_two
    by (rule heap_update_raw_pointer_field_external_frame[OF out_second])
  have hi: "?hi a = ?hu a"
  proof (cases "pxIndex_C (h_val ?hu lp) = p")
    case True
    have field:
      "?hi = heap_update (raw_index_field_ptr lp)
         (xLIST_ITEM_C.pxPrevious_C (h_val ?hu p)) ?hu"
      unfolding raw_remove_index_heap_def
      apply (simp only: if_P[OF True])
      by (rule raw_remove_taken_index_heap_to_field[OF lp_guard])
    show ?thesis
      unfolding field
      by (rule heap_update_raw_index_field_external_frame[OF out_index])
  next
    case False
    show ?thesis
      unfolding raw_remove_index_heap_def by (simp only: if_not_P[OF False])
  qed
  have hc_field: "?hc = heap_update (raw_container_field_ptr p) NULL ?hi"
    by (rule raw_remove_container_heap_to_field[OF p_guard])
  have hc: "?hc a = ?hi a"
    unfolding hc_field
    by (rule heap_update_raw_container_field_external_frame[OF out_container])
  have count_field:
    "raw_remove_count_heap ?hc lp =
     heap_update (raw_count_field_ptr lp)
       (uxNumberOfItems_C (h_val ?hc lp) - 1) ?hc"
    by (rule raw_remove_count_heap_to_field[OF lp_guard])
  have count: "raw_remove_count_heap ?hc lp a = ?hc a"
    unfolding count_field
    by (rule heap_update_raw_count_field_external_frame[OF out_count])
  have concrete:
    "raw_remove_concrete_heap h p = raw_remove_source_heap h lp p"
    by (rule raw_remove_concrete_heap_eq[OF rel member])
  show ?thesis
    using concrete h1 hu hi hc count
    by (simp add: raw_remove_source_heap_def raw_remove_suffix_heap_def)
qed

definition raw_remove_unlinked_effect ::
  "heap_mem \<Rightarrow> heap_mem \<Rightarrow> xLIST_C ptr \<Rightarrow>
   (raw_node_id, raw_key) xlist_abs \<Rightarrow> raw_node_id \<Rightarrow> bool"
where
  "raw_remove_unlinked_effect h h' lp xs p \<longleftrightarrow>
     raw_remove_effect h h' lp xs p \<and>
     pvContainer_C (h_val h' p) = NULL \<and>
     xLIST_ITEM_C.pxNext_C (h_val h' p) =
       xLIST_ITEM_C.pxNext_C (h_val h p) \<and>
     xLIST_ITEM_C.pxPrevious_C (h_val h' p) =
       xLIST_ITEM_C.pxPrevious_C (h_val h p) \<and>
     (\<forall>a. a \<notin> raw_remove_exact_write_footprint h lp p
       \<longrightarrow> h' a = h a)"

theorem raw_remove_concrete_heap_unlinked_effect:
  assumes rel: "raw_xlist_rel h lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "raw_remove_unlinked_effect h (raw_remove_concrete_heap h p) lp xs p"
proof -
  have effect:
    "raw_remove_effect h (raw_remove_concrete_heap h p) lp xs p"
  proof -
    have count: "uxNumberOfItems_C
        (h_val (raw_remove_concrete_heap h p) lp) =
        uxNumberOfItems_C (h_val h lp) - 1"
      by (rule raw_remove_concrete_heap_count_effect[OF rel member])
    have index: "pxIndex_C (h_val (raw_remove_concrete_heap h p) lp) =
        (if pxIndex_C (h_val h lp) = p then raw_prev_at h lp p
         else pxIndex_C (h_val h lp))"
      by (rule raw_remove_concrete_heap_index_effect[OF rel member])
    have links: "raw_ring_links (raw_remove_concrete_heap h p) lp
        (remove1 p (ring xs))"
      by (rule raw_remove_concrete_heap_topology_effect[OF rel member])
    have payload: "\<forall>q \<in> set (remove1 p (ring xs)).
        raw_key_at (raw_remove_concrete_heap h p) q = raw_key_at h q \<and>
        pvContainer_C (h_val (raw_remove_concrete_heap h p) q) =
          pvContainer_C (h_val h q)"
      by (rule raw_remove_concrete_heap_payload_effect[OF rel member])
    show ?thesis using count index links payload
      by (simp add: raw_remove_effect_def)
  qed
  have removed:
    "pvContainer_C (h_val (raw_remove_concrete_heap h p) p) = NULL \<and>
     xLIST_ITEM_C.pxNext_C (h_val (raw_remove_concrete_heap h p) p) =
       xLIST_ITEM_C.pxNext_C (h_val h p) \<and>
     xLIST_ITEM_C.pxPrevious_C (h_val (raw_remove_concrete_heap h p) p) =
       xLIST_ITEM_C.pxPrevious_C (h_val h p)"
    by (rule raw_remove_concrete_heap_removed_item_effect[OF rel member])
  have frame: "\<forall>a. a \<notin> raw_remove_exact_write_footprint h lp p
      \<longrightarrow> raw_remove_concrete_heap h p a = h a"
    by (intro allI impI raw_remove_concrete_heap_exact_external_frame[
          OF rel member])
  show ?thesis
    using effect removed frame by (simp add: raw_remove_unlinked_effect_def)
qed

theorem raw_vListRemove_general_unlinked_effect:
  assumes rel: "raw_xlist_rel (hrs_mem (t_hrs_' s)) lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "vListRemove' p \<bullet> s
     \<lbrace>\<lambda>r t. r = Result () \<and>
       raw_remove_unlinked_effect
         (hrs_mem (t_hrs_' s)) (hrs_mem (t_hrs_' t)) lp xs p
     \<rbrace>"
proof -
  note heap = raw_vListRemove_general_heap_effect[OF rel member]
  have pure:
    "raw_remove_unlinked_effect (hrs_mem (t_hrs_' s))
       (raw_remove_concrete_heap (hrs_mem (t_hrs_' s)) p) lp xs p"
    by (rule raw_remove_concrete_heap_unlinked_effect[OF rel member])
  show ?thesis
    apply (rule runs_to_weaken[OF heap])
    using pure by auto
qed

definition raw_family_members ::
  "xLIST_C ptr set \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   raw_node_id \<Rightarrow> xLIST_C ptr set"
where
  "raw_family_members roots fam p =
     {lp \<in> roots. p \<in> set (ring (fam lp))}"

definition raw_family_rel ::
  "heap_mem \<Rightarrow> xLIST_C ptr set \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow> bool"
where
  "raw_family_rel h roots fam \<longleftrightarrow>
     finite roots \<and> (\<forall>lp \<in> roots. raw_xlist_rel h lp (fam lp))"

definition raw_family_container_faithful ::
  "heap_mem \<Rightarrow> xLIST_C ptr set \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow> bool"
where
  "raw_family_container_faithful h roots fam \<longleftrightarrow>
     (\<forall>p. pvContainer_C (h_val h p) = NULL \<longleftrightarrow>
       raw_family_members roots fam p = {}) \<and>
     (\<forall>lp \<in> roots. \<forall>p \<in> set (ring (fam lp)).
       pvContainer_C (h_val h p) = PTR_COERCE(xLIST_C \<rightarrow> unit) lp)"

definition raw_family_container_faithful_on ::
  "heap_mem \<Rightarrow> xLIST_C ptr set \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   raw_node_id set \<Rightarrow> bool"
where
  "raw_family_container_faithful_on h roots fam managed \<longleftrightarrow>
     (\<forall>p \<in> managed. pvContainer_C (h_val h p) = NULL \<longleftrightarrow>
       raw_family_members roots fam p = {}) \<and>
     (\<forall>lp \<in> roots. \<forall>p \<in> managed \<inter> set (ring (fam lp)).
       pvContainer_C (h_val h p) = PTR_COERCE(xLIST_C \<rightarrow> unit) lp)"

definition raw_family_globally_unlinked ::
  "heap_mem \<Rightarrow> xLIST_C ptr set \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   raw_node_id \<Rightarrow> bool"
where
  "raw_family_globally_unlinked h roots fam p \<longleftrightarrow>
     raw_family_members roots fam p = {} \<and>
     pvContainer_C (h_val h p) = NULL"

theorem raw_family_remove_owner_globally_unlinked:
  assumes family: "raw_family_rel h roots fam"
    and owner: "owner \<in> roots"
    and unique: "raw_family_members roots fam p = {owner}"
    and owner_post:
      "raw_xlist_rel h' owner (list_remove_abs p (fam owner))"
    and other_frames:
      "\<And>lp. lp \<in> roots \<Longrightarrow> lp \<noteq> owner \<Longrightarrow>
        raw_xlist_rel h' lp (fam lp)"
    and removed_null: "pvContainer_C (h_val h' p) = NULL"
  shows
    "raw_family_rel h' roots
       (fam(owner := list_remove_abs p (fam owner))) \<and>
     raw_family_globally_unlinked h' roots
       (fam(owner := list_remove_abs p (fam owner))) p"
proof -
  let ?fam' = "fam(owner := list_remove_abs p (fam owner))"
  have finite: "finite roots"
    using family by (simp add: raw_family_rel_def)
  have family_post: "raw_family_rel h' roots ?fam'"
    unfolding raw_family_rel_def
  proof (intro conjI ballI)
    show "finite roots" by (rule finite)
    fix lp
    assume lp_root: "lp \<in> roots"
    show "raw_xlist_rel h' lp (?fam' lp)"
    proof (cases "lp = owner")
      case True
      show ?thesis using owner_post True by simp
    next
      case False
      show ?thesis using other_frames[OF lp_root False] False by simp
    qed
  qed
  have uniqueD:
    "\<And>lp. lp \<in> roots \<Longrightarrow>
      p \<in> set (ring (fam lp)) \<Longrightarrow> lp = owner"
    using unique by (auto simp: raw_family_members_def)
  have owner_old_member: "p \<in> set (ring (fam owner))"
    using unique owner by (auto simp: raw_family_members_def)
  have owner_wf: "xlist_wf (fam owner)"
    using family owner
    by (simp add: raw_family_rel_def raw_xlist_rel_def raw_xlist_view_def)
  have owner_distinct: "distinct (ring (fam owner))"
    using owner_wf by (simp add: xlist_wf_def)
  have owner_absent:
    "p \<notin> set (ring (list_remove_abs p (fam owner)))"
    using owner_old_member owner_distinct
    by (simp add: list_remove_abs_def distinct_remove1)
  have no_member: "raw_family_members roots ?fam' p = {}"
  proof (rule equals0I)
    fix lp
    assume lp_mem: "lp \<in> raw_family_members roots ?fam' p"
    have lp_root: "lp \<in> roots"
      using lp_mem by (simp add: raw_family_members_def)
    have p_mem: "p \<in> set (ring (?fam' lp))"
      using lp_mem by (simp add: raw_family_members_def)
    show False
    proof (cases "lp = owner")
      case True
      show False using p_mem owner_absent True by simp
    next
      case False
      have old_mem: "p \<in> set (ring (fam lp))"
        using p_mem False by simp
      have "lp = owner" by (rule uniqueD[OF lp_root old_mem])
      with False show False by simp
    qed
  qed
  have unlinked: "raw_family_globally_unlinked h' roots ?fam' p"
    using no_member removed_null
    by (simp add: raw_family_globally_unlinked_def)
  show ?thesis using family_post unlinked by simp
qed

text \<open>
  Faithfulness is deliberately separate from global unlinking.  Its
  preservation needs a declared managed-item universe, a membership frame for
  every protected root, and a container frame for every surviving managed
  item.  The local remove theorem supplies the removed-item NULL fact and a
  byte frame; a scheduler composition must discharge these family-wide frame
  premises from its allocation geometry.
\<close>

theorem raw_family_container_faithful_on_preserved:
  assumes pre:
      "raw_family_container_faithful_on h roots fam managed"
    and removed_managed: "p \<in> managed"
    and removed_members:
      "raw_family_members roots fam' p = {}"
    and membership_frame:
      "\<And>lp q. lp \<in> roots \<Longrightarrow> q \<in> managed \<Longrightarrow>
        q \<noteq> p \<Longrightarrow>
        (q \<in> set (ring (fam' lp)) \<longleftrightarrow>
         q \<in> set (ring (fam lp)))"
    and container_frame:
      "\<And>q. q \<in> managed \<Longrightarrow> q \<noteq> p \<Longrightarrow>
        pvContainer_C (h_val h' q) = pvContainer_C (h_val h q)"
    and removed_null: "pvContainer_C (h_val h' p) = NULL"
  shows "raw_family_container_faithful_on h' roots fam' managed"
proof -
  have members_frame:
    "\<And>q. q \<in> managed \<Longrightarrow> q \<noteq> p \<Longrightarrow>
      raw_family_members roots fam' q = raw_family_members roots fam q"
  proof -
    fix q
    assume q_managed: "q \<in> managed" and q_ne: "q \<noteq> p"
    show "raw_family_members roots fam' q = raw_family_members roots fam q"
      unfolding raw_family_members_def
      using membership_frame[OF _ q_managed q_ne] by auto
  qed
  have null_iff:
    "\<forall>q \<in> managed.
      pvContainer_C (h_val h' q) = NULL \<longleftrightarrow>
      raw_family_members roots fam' q = {}"
  proof (intro ballI)
    fix q
    assume q_managed: "q \<in> managed"
    show
      "pvContainer_C (h_val h' q) = NULL \<longleftrightarrow>
       raw_family_members roots fam' q = {}"
    proof (cases "q = p")
      case True
      show ?thesis using True removed_null removed_members by simp
    next
      case False
      have pre_q:
        "pvContainer_C (h_val h q) = NULL \<longleftrightarrow>
         raw_family_members roots fam q = {}"
        using pre q_managed
        by (auto simp: raw_family_container_faithful_on_def)
      show ?thesis
        using pre_q container_frame[OF q_managed False]
          members_frame[OF q_managed False]
        by simp
    qed
  qed
  have live_owner:
    "\<forall>lp \<in> roots. \<forall>q \<in> managed \<inter> set (ring (fam' lp)).
      pvContainer_C (h_val h' q) = PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
  proof (intro ballI)
    fix lp q
    assume lp_root: "lp \<in> roots"
      and q_post: "q \<in> managed \<inter> set (ring (fam' lp))"
    have q_managed: "q \<in> managed" using q_post by simp
    have q_ne: "q \<noteq> p"
    proof
      assume "q = p"
      then have "lp \<in> raw_family_members roots fam' p"
        using lp_root q_post by (simp add: raw_family_members_def)
      with removed_members show False by simp
    qed
    have q_pre: "q \<in> set (ring (fam lp))"
      using q_post membership_frame[OF lp_root q_managed q_ne] by simp
    have pre_owner:
      "pvContainer_C (h_val h q) = PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
      using pre lp_root q_managed q_pre
      by (auto simp: raw_family_container_faithful_on_def)
    show
      "pvContainer_C (h_val h' q) = PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
      using container_frame[OF q_managed q_ne] pre_owner by simp
  qed
  show ?thesis
    using null_iff live_owner
    by (simp add: raw_family_container_faithful_on_def)
qed

end
