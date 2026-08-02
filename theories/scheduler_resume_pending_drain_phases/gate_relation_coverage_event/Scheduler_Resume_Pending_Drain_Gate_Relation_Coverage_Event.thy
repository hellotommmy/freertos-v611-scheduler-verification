theory Scheduler_Resume_Pending_Drain_Gate_Relation_Coverage_Event
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Pending_Drain_Gate_Relation_Coverage_Freshness.Scheduler_Resume_Pending_Drain_Gate_Relation_Coverage_Freshness"
begin

lemma resume_pending_gate_head_event_memberD:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "event_item_raw_ptr D t \<in>
       set (ring (event_raw (rpc_pending_root C)))"
proof -
  have live: "t \<in> rpc_live C"
    by (rule resume_pending_gate_head_liveD[OF rel tasks])
  have pending: "rpc_pending_root C \<in> rpc_event_roots C"
    using resume_pending_gate_pure_entryD[OF rel]
    by (auto simp: resume_pending_entry_rel_def resume_pending_context_wf_def)
  have abstract:
    "Event t \<in>
       set (ring (rps_event_family S (rpc_pending_root C)))"
    using resume_pending_gate_pure_entryD[OF rel] tasks
    by (auto simp: resume_pending_entry_rel_def)
  show ?thesis
    using scheduler_event_root_family_member_iff[
      OF resume_pending_gate_event_familyD[OF rel] live pending]
      abstract by simp
qed

end
