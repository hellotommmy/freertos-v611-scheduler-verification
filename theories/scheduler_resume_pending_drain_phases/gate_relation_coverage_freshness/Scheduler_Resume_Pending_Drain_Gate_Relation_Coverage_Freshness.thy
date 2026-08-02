theory Scheduler_Resume_Pending_Drain_Gate_Relation_Coverage_Freshness
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Pending_Drain_Gate_Relation_Coverage_Ownership.Scheduler_Resume_Pending_Drain_Gate_Relation_Coverage_Ownership"
begin

lemma resume_pending_gate_head_ready_freshD:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "raw_fresh_for_insert (rpc_ready_root C (rpc_priority C t))
       (ring (generic_raw (rpc_ready_root C (rpc_priority C t))))
       (resume_pending_generic_raw_ptr D t)"
proof -
  have live: "t \<in> rpc_live C"
    by (rule resume_pending_gate_head_liveD[OF rel tasks])
  have pending: "t \<in> set (rpc_tasks C)"
    using tasks by simp
  have pure: "resume_pending_entry_rel C S"
    by (rule resume_pending_gate_pure_entryD[OF rel])
  have target:
    "rpc_ready_root C (rpc_priority C t) \<in> rpc_generic_roots C"
    using pure live
    by (auto simp: resume_pending_entry_rel_def resume_pending_context_wf_def)
  have distinct:
    "rpc_generic_owner C t \<noteq>
       rpc_ready_root C (rpc_priority C t)"
    using pure pending live
    by (auto simp: resume_pending_entry_rel_def resume_pending_context_wf_def)
  have owner_geometry:
    "scheduler_delay_owner_entry_rel
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (rpc_generic_roots C) generic_raw (rpc_generic_owner C t)
       (resume_pending_generic_raw_ptr D t) \<and>
     raw_family_insert_geometry (rpc_generic_roots C) generic_raw
       (resume_pending_generic_raw_ptr D t)"
    by (rule resume_pending_gate_head_generic_ownerD[OF rel tasks])
  have owner_entry:
    "scheduler_delay_owner_entry_rel
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (rpc_generic_roots C) generic_raw (rpc_generic_owner C t)
       (resume_pending_generic_raw_ptr D t)"
    by (rule owner_geometry[THEN conjunct1])
  have geometry:
    "raw_family_insert_geometry (rpc_generic_roots C) generic_raw
       (resume_pending_generic_raw_ptr D t)"
    by (rule owner_geometry[THEN conjunct2])
  show ?thesis
    by (rule scheduler_delay_entry_fresh_for_derived_target[
      OF owner_entry geometry target distinct])
qed

end
