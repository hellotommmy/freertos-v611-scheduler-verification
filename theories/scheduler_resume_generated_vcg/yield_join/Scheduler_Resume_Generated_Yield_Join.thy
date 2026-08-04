theory Scheduler_Resume_Generated_Yield_Join
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Ready_Insert.Scheduler_Resume_Generated_Ready_Insert"
begin

text \<open>
  After the generated ready insertion, the pending-ready drain body reads
  \<open>pxCurrentTCB\<close> under its own guard and compares the current task's priority
  with the awakened head task's priority; the loop-carried yield word becomes
  one exactly when the comparison requests a yield.  This theory executes that
  generated fragment from the checked ready-inserted cutpoint state.

  No task, priority, live set, heap layout or list population is fixed.  The
  current task is whatever task the entry relation's current-task clause
  designates, at an arbitrary in-range priority; the head task priority is
  whatever the represented pending head carries.  Both comparison outcomes are
  covered by one exact conditional result.
\<close>

section \<open>Named ready-inserted cutpoint state\<close>

definition resume_pending_ready_inserted_state ::
  "'tid scheduler_decode \<Rightarrow>
   ('tid, xLIST_C ptr) resume_pending_context \<Rightarrow> 'tid \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> Scheduler_V611_Parse.globals"
where
  "resume_pending_ready_inserted_state D C t generic_raw c =
     scheduler_mem_state
       (raw_insert_concrete_heap
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
           (resume_pending_top_raised_state D t c)))
         (rpc_ready_root C (rpc_priority C t))
         (resume_pending_generic_raw_after C D t generic_raw
           (rpc_ready_root C (rpc_priority C t)))
         (resume_pending_generic_raw_ptr D t))
       (resume_pending_top_raised_state D t c)"

lemma resume_pending_ready_inserted_heap:
  "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
     (resume_pending_ready_inserted_state D C t generic_raw c)) =
   raw_insert_concrete_heap
     (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
       (resume_pending_top_raised_state D t c)))
     (rpc_ready_root C (rpc_priority C t))
     (resume_pending_generic_raw_after C D t generic_raw
       (rpc_ready_root C (rpc_priority C t)))
     (resume_pending_generic_raw_ptr D t)"
  by (simp add: resume_pending_ready_inserted_state_def)

lemma resume_pending_top_raised_pxCurrentTCB:
  "Scheduler_V611_Parse.globals.pxCurrentTCB_'
     (resume_pending_top_raised_state D t c) =
   Scheduler_V611_Parse.globals.pxCurrentTCB_' c"
  by (simp add: resume_pending_top_raised_state_def
      scheduler_mem_state_def Let_def)

lemma resume_pending_ready_inserted_pxCurrentTCB:
  "Scheduler_V611_Parse.globals.pxCurrentTCB_'
     (resume_pending_ready_inserted_state D C t generic_raw c) =
   Scheduler_V611_Parse.globals.pxCurrentTCB_' c"
  by (simp add: resume_pending_ready_inserted_state_def
      scheduler_mem_state_def resume_pending_top_raised_pxCurrentTCB)

lemma resume_pending_ready_inserted_top:
  "Scheduler_V611_Parse.globals.uxTopReadyPriority_'
     (resume_pending_ready_inserted_state D C t generic_raw c) =
   Scheduler_V611_Parse.globals.uxTopReadyPriority_'
     (resume_pending_top_raised_state D t c)"
  by (simp add: resume_pending_ready_inserted_state_def
      scheduler_mem_state_def)

corollary resume_pending_generated_ready_insert_named:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
    and roots: "R = generated_scheduler_roots"
  shows
    "Scheduler_V611_Delay_Translation.vListInsertEnd'
       (sr_ready generated_scheduler_roots (rpc_priority C t))
       (scheduler_generic_item_ptr (sd_tcb_ptr D t)) \<bullet>
       (resume_pending_top_raised_state D t c)
     \<lbrace>\<lambda>r s.
       r = Result () \<and>
       s = resume_pending_ready_inserted_state D C t generic_raw c
     \<rbrace>"
  apply (rule runs_to_weaken[
    OF resume_pending_generated_ready_insert_exact[OF rel tasks roots]])
  by (simp add: resume_pending_ready_inserted_state_def)

section \<open>Priority byte frame across the generated insert-end\<close>

text \<open>
  The sibling-frame capstone theorems already frame priority fields, but they
  additionally demand a distinct sibling item.  The yield comparison only
  needs the priority half, so it is restated here without any sibling
  premise: the exact insert-end footprint stays inside the target ring's
  storage and the inserted item's region, and both are disjoint from every
  live task's priority field.
\<close>

lemma raw_insert_end_family_priority_byte_frame:
  assumes pre: "scheduler_family_pre_rel h roots fam live D"
    and target: "target \<in> roots"
    and fresh: "raw_fresh_for_insert target (ring (fam target)) p"
    and p_managed: "p \<in> universal_managed_nodes live D"
    and t_live: "t \<in> live"
  shows
    "\<forall>a\<in>universal_priority_field_region (sd_tcb_ptr D t).
       raw_insert_concrete_heap h target (fam target) p a = h a"
proof -
  have geometry: "universal_tcb_geometry live D"
    using pre by (simp add: scheduler_family_pre_rel_def)
  have rel: "raw_xlist_rel h target (fam target)"
    using pre target
    by (auto simp: scheduler_family_pre_rel_def raw_family_rel_def)
  have footprint:
    "raw_insert_end_exact_write_footprint h target (fam target) p \<subseteq>
       raw_xlist_storage target (fam target) \<union> raw_item_region p"
    by (rule raw_insert_end_exact_footprint_subset_storage[OF rel])
  have storage_priority:
    "raw_xlist_storage target (fam target) \<inter>
       universal_priority_field_region (sd_tcb_ptr D t) = {}"
    by (rule scheduler_family_target_storage_priority_disjoint[
          OF pre target t_live])
  have p_priority:
    "raw_item_region p \<inter>
       universal_priority_field_region (sd_tcb_ptr D t) = {}"
    by (rule universal_managed_item_priority_region_disjoint[
          OF geometry t_live p_managed])
  have priority_outside:
    "\<And>a. a \<in> universal_priority_field_region (sd_tcb_ptr D t)
       \<Longrightarrow>
       a \<notin> raw_insert_end_exact_write_footprint h target (fam target) p"
    using footprint storage_priority p_priority by blast
  show ?thesis
    using raw_insert_concrete_heap_exact_external_frame[OF rel fresh]
      priority_outside by blast
qed

lemma resume_pending_ready_insert_priority_frame:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
    and live: "u \<in> rpc_live C"
  shows
    "Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
         (resume_pending_ready_inserted_state D C t generic_raw c)))
         (sd_tcb_ptr D u)) =
     Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val (resume_pending_generic_remove_heap D t c)
         (sd_tcb_ptr D u))"
proof -
  let ?hR = "resume_pending_generic_remove_heap D t c"
  let ?target = "rpc_ready_root C (rpc_priority C t)"
  let ?fam = "resume_pending_generic_raw_after C D t generic_raw"
  let ?p = "resume_pending_generic_raw_ptr D t"
  let ?tp = "sd_tcb_ptr D u"
  have t_live: "t \<in> rpc_live C"
    by (rule resume_pending_gate_head_liveD[OF rel tasks])
  have heap_base:
    "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
       (resume_pending_top_raised_state D t c)) = ?hR"
    using resume_pending_top_raised_semantics[OF rel tasks] by blast
  have pre:
    "scheduler_family_pre_rel ?hR (rpc_generic_roots C) ?fam
       (rpc_live C) D"
    using resume_pending_top_raised_generic_family[OF rel tasks] heap_base
    by simp
  have target: "?target \<in> rpc_generic_roots C"
    by (rule resume_pending_ready_target_in_roots[OF rel tasks])
  have fresh: "raw_fresh_for_insert ?target (ring (?fam ?target)) ?p"
    by (rule resume_pending_ready_fresh_after_removal[OF rel tasks])
  have p_managed: "?p \<in> universal_managed_nodes (rpc_live C) D"
    using t_live
    by (auto simp: resume_pending_generic_raw_ptr_def
        universal_managed_nodes_def)
  have bytes:
    "\<forall>address\<in>universal_priority_field_region ?tp.
       raw_insert_concrete_heap ?hR ?target (?fam ?target) ?p address =
       ?hR address"
    by (rule raw_insert_end_family_priority_byte_frame[
          OF pre target fresh p_managed live])
  have heap_inserted:
    "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
       (resume_pending_ready_inserted_state D C t generic_raw c)) =
     raw_insert_concrete_heap ?hR ?target (?fam ?target) ?p"
    using heap_base
    by (simp add: resume_pending_ready_inserted_heap)
  have field_same:
    "h_val (raw_insert_concrete_heap ?hR ?target (?fam ?target) ?p)
       (universal_priority_field_ptr ?tp) =
     h_val ?hR (universal_priority_field_ptr ?tp)"
  proof (rule delay_h_val_region_cong)
    fix address
    assume "address \<in>
      {ptr_val (universal_priority_field_ptr ?tp)..+size_of TYPE(32 word)}"
    then show
      "raw_insert_concrete_heap ?hR ?target (?fam ?target) ?p address =
       ?hR address"
      using bytes by (simp add: universal_priority_field_region_def)
  qed
  have fields:
    "Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val (raw_insert_concrete_heap ?hR ?target (?fam ?target) ?p)
         ?tp) =
     Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val ?hR ?tp)"
    using field_same
    unfolding universal_priority_field_ptr_def
    by (simp only:
      Scheduler_V611_Parse.tskTaskControlBlock_C_h_val_fields(4))
  show ?thesis
    using fields by (simp add: heap_inserted)
qed

section \<open>Priority observations at the ready-inserted cutpoint\<close>

lemma resume_pending_inserted_head_priorityD:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "unat (Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
         (resume_pending_ready_inserted_state D C t generic_raw c)))
         (sd_tcb_ptr D t))) = rpc_priority C t"
proof -
  have live: "t \<in> rpc_live C"
    by (rule resume_pending_gate_head_liveD[OF rel tasks])
  note post_removal = resume_pending_two_removes_head_priorityD[OF rel tasks]
  note frame = resume_pending_ready_insert_priority_frame[OF rel tasks live]
  show ?thesis using post_removal frame by simp
qed

lemma resume_pending_gate_current_taskD:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
  shows
    "\<exists>current\<in>rpc_live C.
       sa_current a = Some current \<and>
       rpc_current_priority C = rpc_priority C current \<and>
       Scheduler_V611_Parse.globals.pxCurrentTCB_' c = sd_tcb_ptr D current"
proof -
  have current_rel: "scheduler_current_rel D c a"
    using rel
    unfolding resume_pending_gate_entry_rel_def Let_def by blast
  obtain current where live: "current \<in> rpc_live C"
      and abs: "sa_current a = Some current"
      and priority: "rpc_current_priority C = rpc_priority C current"
    using rel
    unfolding resume_pending_gate_entry_rel_def Let_def by blast
  have ptr:
    "Scheduler_V611_Parse.globals.pxCurrentTCB_' c = sd_tcb_ptr D current"
    using current_rel abs by (simp add: scheduler_current_rel_def)
  show ?thesis using live abs priority ptr by blast
qed

lemma resume_pending_inserted_current_observationD:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "c_guard (Scheduler_V611_Parse.globals.pxCurrentTCB_'
       (resume_pending_ready_inserted_state D C t generic_raw c)) \<and>
     unat (Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
         (resume_pending_ready_inserted_state D C t generic_raw c)))
         (Scheduler_V611_Parse.globals.pxCurrentTCB_'
           (resume_pending_ready_inserted_state D C t generic_raw c)))) =
     rpc_current_priority C"
proof -
  obtain current where current_live: "current \<in> rpc_live C"
      and current_abs: "sa_current a = Some current"
      and current_priority: "rpc_current_priority C = rpc_priority C current"
      and current_ptr:
        "Scheduler_V611_Parse.globals.pxCurrentTCB_' c =
           sd_tcb_ptr D current"
    using resume_pending_gate_current_taskD[OF rel] by blast
  have observation:
    "TaskObservationRel D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) a"
    by (rule resume_pending_gate_task_observationD[OF rel])
  have live_abs: "current \<in> sa_live a"
    using rel current_live
    unfolding resume_pending_gate_entry_rel_def Let_def by blast
  have guard_current: "c_guard (sd_tcb_ptr D current)"
    using TaskObservationRel_liveD[OF observation live_abs] by blast
  have entry_priority:
    "unat (Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
         (sd_tcb_ptr D current))) = sa_priority a current"
    using TaskObservationRel_liveD[OF observation live_abs] by blast
  have priority_map: "rpc_priority C current = sa_priority a current"
    using rel current_live
    unfolding resume_pending_gate_entry_rel_def Let_def by blast
  note eframe = resume_pending_event_remove_priority_frame[
    OF rel tasks current_live]
  note gframe = resume_pending_generic_remove_priority_frame[
    OF rel tasks current_live]
  note iframe = resume_pending_ready_insert_priority_frame[
    OF rel tasks current_live]
  have ptr_inserted:
    "Scheduler_V611_Parse.globals.pxCurrentTCB_'
       (resume_pending_ready_inserted_state D C t generic_raw c) =
     sd_tcb_ptr D current"
    by (simp add: resume_pending_ready_inserted_pxCurrentTCB current_ptr)
  have inserted_priority:
    "unat (Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
         (resume_pending_ready_inserted_state D C t generic_raw c)))
         (sd_tcb_ptr D current))) = rpc_current_priority C"
    using iframe gframe eframe entry_priority priority_map
      current_priority by simp
  show ?thesis
    using guard_current ptr_inserted inserted_priority by simp
qed

section \<open>Exact generated yield join\<close>

definition resume_pending_generated_yield_join ::
  "'tid scheduler_decode \<Rightarrow> 'tid \<Rightarrow> int \<Rightarrow>
   (int, Scheduler_V611_Parse.globals) res_monad"
where
  "resume_pending_generated_yield_join D t y = do {
     guard (\<lambda>s. c_guard (Scheduler_V611_Parse.globals.pxCurrentTCB_' s));
     condition
       (\<lambda>s. Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
           (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
             (Scheduler_V611_Parse.globals.pxCurrentTCB_' s)) \<le>
         Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
           (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
             (sd_tcb_ptr D t)))
       (return 1)
       (return y)
   }"

theorem resume_pending_generated_yield_join_exact:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "resume_pending_generated_yield_join D t y \<bullet>
       (resume_pending_ready_inserted_state D C t generic_raw c)
     \<lbrace>\<lambda>r s.
       r = Result
         (if rpc_current_priority C \<le> rpc_priority C t then 1 else y) \<and>
       s = resume_pending_ready_inserted_state D C t generic_raw c
     \<rbrace>"
proof -
  note head = resume_pending_inserted_head_priorityD[OF rel tasks]
  note current = resume_pending_inserted_current_observationD[OF rel tasks]
  have compare:
    "(Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
        (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
          (resume_pending_ready_inserted_state D C t generic_raw c)))
          (Scheduler_V611_Parse.globals.pxCurrentTCB_'
            (resume_pending_ready_inserted_state D C t generic_raw c))) \<le>
      Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
        (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
          (resume_pending_ready_inserted_state D C t generic_raw c)))
          (sd_tcb_ptr D t))) =
     (rpc_current_priority C \<le> rpc_priority C t)"
    using head current by (simp add: word_le_nat_alt)
  show ?thesis
    unfolding resume_pending_generated_yield_join_def
    apply runs_to_vcg
    using current compare by simp_all
qed

section \<open>Phase invariant through the yield cut\<close>

lemma resume_pending_yield_checked_phaseD:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "resume_pending_loop_phase_inv C S [] (t # rest) RP_YieldChecked
       (resume_pending_yield_check_state C t
         (resume_pending_ready_insert_state C t
           (resume_pending_raise_top_state C t
             (resume_pending_generic_unlink_state C t
               (resume_pending_event_unlink_state C t S)))))"
  by (rule resume_pending_loop_phase_inv_yield_step[
      OF resume_pending_loop_phase_inv_ready_step[
      OF resume_pending_top_raised_phaseD[OF rel tasks]]])

text \<open>
  The loop-carried yield word encodes the abstract local-yield flag: if the
  entry word already encodes the flag, the returned conditional word encodes
  the flag after the abstract yield check.  This connects the generated
  return value to \<open>resume_pending_yield_check_state\<close> without fixing either
  branch.
\<close>

lemma resume_pending_yield_join_word_encoding:
  fixes y :: "int"
  assumes encode: "(y \<noteq> 0) = rps_local_yield S'"
  shows
    "((if rpc_current_priority C \<le> rpc_priority C t then 1 else y) \<noteq> 0) =
     rps_local_yield (resume_pending_yield_check_state C t S')"
  using encode
  by (auto simp: resume_pending_yield_check_state_def)

end
