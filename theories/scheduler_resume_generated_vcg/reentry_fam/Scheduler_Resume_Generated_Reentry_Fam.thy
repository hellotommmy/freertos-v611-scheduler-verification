theory Scheduler_Resume_Generated_Reentry_Fam
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Reentry_Rep.Scheduler_Resume_Generated_Reentry_Rep"
begin

text \<open>
  The raw-family clauses of re-entry for the remaining pending tasks.  The
  drained family differs from the entry family in exactly two rings -- the
  awakened task's item left its blocked ring and joined its ready ring -- so
  every other task's ownership, membership, insertion geometry, ring
  subsets, and the generic-versus-event storage separation carry over by
  set reasoning; no heap byte is consulted beyond the container
  observations already checked.
\<close>

context
  fixes D :: "'tid scheduler_decode"
    and R :: scheduler_roots
    and c :: "Scheduler_V611_Parse.globals"
    and a :: "'tid scheduler_abs"
    and C :: "('tid, xLIST_C ptr) resume_pending_context"
    and S :: "('tid, xLIST_C ptr) resume_pending_snapshot"
    and generic_raw event_raw ::
      "xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs"
    and t :: 'tid and rest :: "'tid list"
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
begin

lemma reentry_entry_preL:
  "scheduler_family_pre_rel
     (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
     (rpc_generic_roots C) generic_raw (rpc_live C) D"
  by (rule resume_pending_gate_generic_familyD[OF rel])

lemma reentry_entry_wf_atL:
  assumes root: "g \<in> rpc_generic_roots C"
  shows "xlist_wf (generic_raw g)"
proof -
  have raw: "raw_xlist_rel
      (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
      g (generic_raw g)"
    using reentry_entry_preL root
    by (auto simp: scheduler_family_pre_rel_def raw_family_rel_def)
  show ?thesis
    using raw by (simp add: raw_xlist_rel_def raw_xlist_view_def)
qed

lemma reentry_fam_after_ring_setL:
  assumes root: "g \<in> rpc_generic_roots C"
  shows
    "set (ring (resume_pending_generic_raw_after C D t generic_raw g)) =
       (if g = rpc_generic_owner C t
        then set (ring (generic_raw g)) -
          {resume_pending_generic_raw_ptr D t}
        else set (ring (generic_raw g)))"
proof (cases "g = rpc_generic_owner C t")
  case True
  have distinct: "distinct (ring (generic_raw g))"
    using reentry_entry_wf_atL[OF root] by (simp add: xlist_wf_def)
  show ?thesis
    using True distinct
    by (simp add: resume_pending_generic_raw_after_def
        scheduler_family_remove_raw_def list_remove_abs_def
        set_remove1_eq)
next
  case False
  show ?thesis
    using False
    by (simp add: resume_pending_generic_raw_after_def
        scheduler_family_remove_raw_def)
qed

lemma reentry_fam_after_wf_atL:
  assumes root: "g \<in> rpc_generic_roots C"
  shows
    "xlist_wf (resume_pending_generic_raw_after C D t generic_raw g)"
proof (cases "g = rpc_generic_owner C t")
  case True
  show ?thesis
    using xlist_wf_remove[OF reentry_entry_wf_atL[OF root]] True
    by (simp add: resume_pending_generic_raw_after_def
        scheduler_family_remove_raw_def)
next
  case False
  show ?thesis
    using reentry_entry_wf_atL[OF root] False
    by (simp add: resume_pending_generic_raw_after_def
        scheduler_family_remove_raw_def)
qed

lemma reentry_drained_fam_ring_setL:
  assumes root: "g \<in> rpc_generic_roots C"
  shows
    "set (ring (resume_pending_drained_generic_fam C D t c
       generic_raw g)) =
       (if g = rpc_ready_root C (rpc_priority C t)
        then insert (resume_pending_generic_raw_ptr D t)
          (set (ring (resume_pending_generic_raw_after C D t
            generic_raw g)))
        else set (ring (resume_pending_generic_raw_after C D t
          generic_raw g)))"
proof (cases "g = rpc_ready_root C (rpc_priority C t)")
  case True
  have target_root:
    "rpc_ready_root C (rpc_priority C t) \<in> rpc_generic_roots C"
    by (rule resume_pending_ready_target_in_roots[OF rel tasks])
  have wf_after:
    "xlist_wf (resume_pending_generic_raw_after C D t generic_raw
       (rpc_ready_root C (rpc_priority C t)))"
    by (rule reentry_fam_after_wf_atL[OF target_root])
  show ?thesis
    using True ring_set_insert_end[OF wf_after]
    by (simp add: resume_pending_drained_generic_fam_def
        scheduler_family_insert_end_raw_def)
next
  case False
  show ?thesis
    using False
    by (simp add: resume_pending_drained_generic_fam_def
        scheduler_family_insert_end_raw_def)
qed

lemma reentry_ptr_distinctL:
  assumes u_live: "u \<in> rpc_live C"
    and u_ne_t: "u \<noteq> t"
  shows
    "resume_pending_generic_raw_ptr D u \<noteq>
       resume_pending_generic_raw_ptr D t"
proof
  assume eq:
    "resume_pending_generic_raw_ptr D u =
       resume_pending_generic_raw_ptr D t"
  have t_live: "t \<in> rpc_live C"
    by (rule resume_pending_gate_head_liveD[OF rel tasks])
  have geometry: "universal_tcb_geometry (rpc_live C) D"
    using reentry_entry_preL
    by (simp add: scheduler_family_pre_rel_def)
  have disjoint:
    "universal_item_region
       (abi_generic_list_item_ptr (sd_tcb_ptr D u)) \<inter>
     universal_item_region
       (abi_generic_list_item_ptr (sd_tcb_ptr D t)) = {}"
    using universal_different_live_component_regions_disjoint[
      OF geometry u_live t_live u_ne_t,
      where left=GenericItem and right=GenericItem] by simp
  have base:
    "ptr_val (abi_generic_list_item_ptr (sd_tcb_ptr D u)) \<in>
       universal_item_region
         (abi_generic_list_item_ptr (sd_tcb_ptr D u))"
    using intvlI[of 0 20
        "ptr_val (abi_generic_list_item_ptr (sd_tcb_ptr D u))"]
    by (simp add: universal_item_region_size)
  show False
    using base eq disjoint
    by (simp add: resume_pending_generic_raw_ptr_def)
qed

lemma reentry_tail_membershipL:
  assumes u_rest: "u \<in> set rest"
    and root: "g \<in> rpc_generic_roots C"
  shows
    "resume_pending_generic_raw_ptr D u \<in>
       set (ring (resume_pending_drained_generic_fam C D t c
         generic_raw g)) \<longleftrightarrow>
     resume_pending_generic_raw_ptr D u \<in> set (ring (generic_raw g))"
proof -
  have u_pending: "u \<in> set (rpc_tasks C)"
    using tasks u_rest by simp
  have u_live: "u \<in> rpc_live C"
    by (rule resume_pending_gate_pending_liveD[OF rel u_pending])
  have wf_ctx: "resume_pending_context_wf C"
    using resume_pending_gate_pure_entryD[OF rel]
    by (simp add: resume_pending_entry_rel_def)
  have u_ne_t: "u \<noteq> t"
    using wf_ctx tasks u_rest
    by (auto simp: resume_pending_context_wf_def)
  have ptr_ne:
    "resume_pending_generic_raw_ptr D u \<noteq>
       resume_pending_generic_raw_ptr D t"
    by (rule reentry_ptr_distinctL[OF u_live u_ne_t])
  show ?thesis
    using reentry_drained_fam_ring_setL[OF root]
      reentry_fam_after_ring_setL[OF root] ptr_ne
    by (auto split: if_splits)
qed

lemma reentry_tail_membersL:
  assumes u_rest: "u \<in> set rest"
  shows
    "raw_family_members (rpc_generic_roots C)
       (resume_pending_drained_generic_fam C D t c generic_raw)
       (resume_pending_generic_raw_ptr D u) =
     raw_family_members (rpc_generic_roots C) generic_raw
       (resume_pending_generic_raw_ptr D u)"
  using reentry_tail_membershipL[OF u_rest]
  by (auto simp: raw_family_members_def)

lemma reentry_tail_owner_entryL:
  assumes u_rest: "u \<in> set rest"
  shows
    "scheduler_delay_owner_entry_rel
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
         (resume_pending_ready_inserted_state D C t generic_raw c)))
       (rpc_generic_roots C)
       (resume_pending_drained_generic_fam C D t c generic_raw)
       (rpc_generic_owner C u)
       (resume_pending_generic_raw_ptr D u)"
proof -
  have u_pending: "u \<in> set (rpc_tasks C)"
    using tasks u_rest by simp
  note entry_owner =
    resume_pending_gate_tail_owner_entryD[OF rel u_pending]
  have owner_root: "rpc_generic_owner C u \<in> rpc_generic_roots C"
    using entry_owner
    by (simp add: scheduler_delay_owner_entry_rel_def)
  have members:
    "raw_family_members (rpc_generic_roots C)
       (resume_pending_drained_generic_fam C D t c generic_raw)
       (resume_pending_generic_raw_ptr D u) =
       {rpc_generic_owner C u}"
    using reentry_tail_membersL[OF u_rest] entry_owner
    by (simp add: scheduler_delay_owner_entry_rel_def)
  have membership:
    "resume_pending_generic_raw_ptr D u \<in>
       set (ring (resume_pending_drained_generic_fam C D t c
         generic_raw (rpc_generic_owner C u)))"
    using reentry_tail_membershipL[OF u_rest owner_root] entry_owner
    by (simp add: scheduler_delay_owner_entry_rel_def)
  have container:
    "List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvContainer_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
         (resume_pending_ready_inserted_state D C t generic_raw c)))
         (resume_pending_generic_raw_ptr D u)) =
     PTR_COERCE(xLIST_C \<rightarrow> unit) (rpc_generic_owner C u)"
    by (rule resume_pending_drained_container_observationD[
      OF rel tasks u_rest])
  show ?thesis
    using owner_root members membership container
    by (simp add: scheduler_delay_owner_entry_rel_def)
qed

lemma reentry_tail_geometryL:
  assumes u_rest: "u \<in> set rest"
  shows
    "raw_family_insert_geometry (rpc_generic_roots C)
       (resume_pending_drained_generic_fam C D t c generic_raw)
       (resume_pending_generic_raw_ptr D u)"
proof -
  have u_pending: "u \<in> set (rpc_tasks C)"
    using tasks u_rest by simp
  have u_live: "u \<in> rpc_live C"
    by (rule resume_pending_gate_pending_liveD[OF rel u_pending])
  have t_live: "t \<in> rpc_live C"
    by (rule resume_pending_gate_head_liveD[OF rel tasks])
  have wf_ctx: "resume_pending_context_wf C"
    using resume_pending_gate_pure_entryD[OF rel]
    by (simp add: resume_pending_entry_rel_def)
  have u_ne_t: "u \<noteq> t"
    using wf_ctx tasks u_rest
    by (auto simp: resume_pending_context_wf_def)
  have entry_geometry:
    "raw_family_insert_geometry (rpc_generic_roots C) generic_raw
       (resume_pending_generic_raw_ptr D u)"
    using rel u_pending
    unfolding resume_pending_gate_entry_rel_def Let_def by blast
  have geometry: "universal_tcb_geometry (rpc_live C) D"
    using reentry_entry_preL
    by (simp add: scheduler_family_pre_rel_def)
  have u_managed:
    "resume_pending_generic_raw_ptr D u \<in>
       universal_managed_nodes (rpc_live C) D"
    using u_live
    by (auto simp: resume_pending_generic_raw_ptr_def
        universal_managed_nodes_def)
  have t_managed:
    "resume_pending_generic_raw_ptr D t \<in>
       universal_managed_nodes (rpc_live C) D"
    using t_live
    by (auto simp: resume_pending_generic_raw_ptr_def
        universal_managed_nodes_def)
  have ptr_ne:
    "resume_pending_generic_raw_ptr D t \<noteq>
       resume_pending_generic_raw_ptr D u"
    using reentry_ptr_distinctL[OF u_live u_ne_t] by simp
  have new_disjoint:
    "raw_item_region (resume_pending_generic_raw_ptr D t) \<inter>
       raw_item_region (resume_pending_generic_raw_ptr D u) = {}"
    by (rule universal_distinct_managed_item_regions_disjoint[
      OF geometry t_managed u_managed ptr_ne])
  show ?thesis
    unfolding raw_family_insert_geometry_def
  proof (rule conjI)
    show "c_guard (resume_pending_generic_raw_ptr D u)"
      using entry_geometry
      by (simp add: raw_family_insert_geometry_def)
  next
    show
      "\<forall>lp\<in>rpc_generic_roots C.
         resume_pending_generic_raw_ptr D u \<noteq> raw_end_item lp \<and>
         raw_item_region (resume_pending_generic_raw_ptr D u) \<inter>
           raw_list_region lp = {} \<and>
         (\<forall>q\<in>set (ring (resume_pending_drained_generic_fam C D t c
            generic_raw lp)).
            q \<noteq> resume_pending_generic_raw_ptr D u \<longrightarrow>
            raw_item_region (resume_pending_generic_raw_ptr D u) \<inter>
              raw_item_region q = {})"
  proof (rule ballI)
    fix lp assume root: "lp \<in> rpc_generic_roots C"
    have entry_here:
      "resume_pending_generic_raw_ptr D u \<noteq> raw_end_item lp \<and>
       raw_item_region (resume_pending_generic_raw_ptr D u) \<inter>
         raw_list_region lp = {} \<and>
       (\<forall>q\<in>set (ring (generic_raw lp)).
          q \<noteq> resume_pending_generic_raw_ptr D u \<longrightarrow>
          raw_item_region (resume_pending_generic_raw_ptr D u) \<inter>
            raw_item_region q = {})"
      using entry_geometry root
      by (simp add: raw_family_insert_geometry_def)
    have ring_bound:
      "set (ring (resume_pending_drained_generic_fam C D t c
         generic_raw lp)) \<subseteq>
       insert (resume_pending_generic_raw_ptr D t)
         (set (ring (generic_raw lp)))"
      using reentry_drained_fam_ring_setL[OF root]
        reentry_fam_after_ring_setL[OF root]
      by (auto split: if_splits)
    have per_member:
      "\<And>q. q \<in> set (ring (resume_pending_drained_generic_fam C D t c
         generic_raw lp)) \<Longrightarrow>
        q \<noteq> resume_pending_generic_raw_ptr D u \<Longrightarrow>
        raw_item_region (resume_pending_generic_raw_ptr D u) \<inter>
          raw_item_region q = {}"
    proof -
      fix q
      assume q_in:
        "q \<in> set (ring (resume_pending_drained_generic_fam C D t c
           generic_raw lp))"
        and q_ne: "q \<noteq> resume_pending_generic_raw_ptr D u"
      show "raw_item_region (resume_pending_generic_raw_ptr D u) \<inter>
          raw_item_region q = {}"
      proof (cases "q = resume_pending_generic_raw_ptr D t")
        case True
        show ?thesis
          using new_disjoint True by (simp add: Int_commute)
      next
        case False
        have q_entry: "q \<in> set (ring (generic_raw lp))"
          using q_in ring_bound False by auto
        show ?thesis
          using entry_here q_entry q_ne by blast
      qed
    qed
    show
      "resume_pending_generic_raw_ptr D u \<noteq> raw_end_item lp \<and>
       raw_item_region (resume_pending_generic_raw_ptr D u) \<inter>
         raw_list_region lp = {} \<and>
       (\<forall>q\<in>set (ring (resume_pending_drained_generic_fam C D t c
          generic_raw lp)).
          q \<noteq> resume_pending_generic_raw_ptr D u \<longrightarrow>
          raw_item_region (resume_pending_generic_raw_ptr D u) \<inter>
            raw_item_region q = {})"
      using entry_here per_member by blast
  qed
  qed
qed

lemma reentry_drained_ring_subsetL:
  assumes root: "g \<in> rpc_generic_roots C"
  shows
    "set (ring (resume_pending_drained_generic_fam C D t c
       generic_raw g)) \<subseteq>
     resume_pending_generic_raw_set (rpc_live C) D"
proof -
  have t_live: "t \<in> rpc_live C"
    by (rule resume_pending_gate_head_liveD[OF rel tasks])
  have entry_subset:
    "set (ring (generic_raw g)) \<subseteq>
       resume_pending_generic_raw_set (rpc_live C) D"
    using rel root
    unfolding resume_pending_gate_entry_rel_def Let_def by blast
  have t_in:
    "resume_pending_generic_raw_ptr D t \<in>
       resume_pending_generic_raw_set (rpc_live C) D"
    using t_live by (simp add: resume_pending_generic_raw_set_def)
  show ?thesis
    using reentry_drained_fam_ring_setL[OF root]
      reentry_fam_after_ring_setL[OF root] entry_subset t_in
    by (auto split: if_splits)
qed

lemma reentry_drained_crossL:
  assumes root: "g \<in> rpc_generic_roots C"
    and event_root: "e \<in> rpc_event_roots C"
  shows
    "raw_xlist_storage g
       (resume_pending_drained_generic_fam C D t c generic_raw g) \<inter>
     raw_xlist_storage e
       (resume_pending_event_raw_after C D t event_raw e) = {}"
proof -
  have t_in: "t \<in> set (rpc_tasks C)"
    using tasks by simp
  have owner_entry:
    "scheduler_delay_owner_entry_rel
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (rpc_generic_roots C) generic_raw (rpc_generic_owner C t)
       (resume_pending_generic_raw_ptr D t)"
    by (rule resume_pending_gate_tail_owner_entryD[OF rel t_in])
  have owner_root: "rpc_generic_owner C t \<in> rpc_generic_roots C"
    using owner_entry
    by (simp add: scheduler_delay_owner_entry_rel_def)
  have t_member:
    "resume_pending_generic_raw_ptr D t \<in>
       set (ring (generic_raw (rpc_generic_owner C t)))"
    using owner_entry
    by (simp add: scheduler_delay_owner_entry_rel_def)
  have t_item_in_owner:
    "raw_item_region (resume_pending_generic_raw_ptr D t) \<subseteq>
       raw_xlist_storage (rpc_generic_owner C t)
         (generic_raw (rpc_generic_owner C t))"
    using t_member by (auto simp: raw_xlist_storage_def)
  have storage_bound:
    "raw_xlist_storage g
       (resume_pending_drained_generic_fam C D t c generic_raw g) \<subseteq>
     raw_xlist_storage g (generic_raw g) \<union>
       raw_item_region (resume_pending_generic_raw_ptr D t)"
    using reentry_drained_fam_ring_setL[OF root]
      reentry_fam_after_ring_setL[OF root]
    by (auto simp: raw_xlist_storage_def split: if_splits)
  have cross_g:
    "raw_xlist_storage g (generic_raw g) \<inter>
       raw_xlist_storage e (event_raw e) = {}"
    using rel root event_root
    unfolding resume_pending_gate_entry_rel_def Let_def by blast
  have cross_owner:
    "raw_xlist_storage (rpc_generic_owner C t)
       (generic_raw (rpc_generic_owner C t)) \<inter>
       raw_xlist_storage e (event_raw e) = {}"
    using rel owner_root event_root
    unfolding resume_pending_gate_entry_rel_def Let_def by blast
  have after_subset:
    "raw_xlist_storage e
       (resume_pending_event_raw_after C D t event_raw e) \<subseteq>
     raw_xlist_storage e (event_raw e)"
    by (rule resume_pending_event_raw_after_storage_subset)
  show ?thesis
    using storage_bound t_item_in_owner cross_g cross_owner
      after_subset
    by blast
qed

end

end
