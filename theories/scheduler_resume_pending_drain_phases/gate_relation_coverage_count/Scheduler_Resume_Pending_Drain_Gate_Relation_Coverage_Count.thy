theory Scheduler_Resume_Pending_Drain_Gate_Relation_Coverage_Count
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Pending_Drain_Gate_Relation_Coverage_Observation.Scheduler_Resume_Pending_Drain_Gate_Relation_Coverage_Observation"
begin

lemma resume_pending_gate_task_count_nonzeroD:
  assumes rel:
    "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
  shows
    "Scheduler_V611_Parse.globals.uxCurrentNumberOfTasks_' c \<noteq> 0"
proof -
  have finite_live: "finite (rpc_live C)"
    using resume_pending_gate_pure_entryD[OF rel]
    by (auto simp: resume_pending_entry_rel_def resume_pending_context_wf_def)
  have live_eq_forward: "rpc_live C = sa_live a"
    using rel
    unfolding resume_pending_gate_entry_rel_def Let_def
    by (elim conjE) assumption
  have live_eq: "sa_live a = rpc_live C"
    by (rule live_eq_forward[symmetric])
  have scalar: "scheduler_scalar_rel c a"
    using rel
    unfolding resume_pending_gate_entry_rel_def Let_def
    by (elim conjE) assumption
  have current:
    "\<exists>current\<in>rpc_live C.
       sa_current a = Some current \<and>
       rpc_current_priority C = rpc_priority C current"
    using rel
    unfolding resume_pending_gate_entry_rel_def Let_def
    by (elim conjE) assumption
  have nonempty: "rpc_live C \<noteq> {}"
    using current by blast
  have card_pos: "0 < card (rpc_live C)"
    using finite_live nonempty by (simp add: card_gt_0_iff)
  have count:
    "unat (Scheduler_V611_Parse.globals.uxCurrentNumberOfTasks_' c) =
       card (rpc_live C)"
    using scalar live_eq
    by (simp add: scheduler_scalar_rel_def)
  show ?thesis using count card_pos by auto
qed

end
