theory Scheduler_Resume_Pending_Drain_Gate_Relation_Coverage_Observation
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Pending_Drain_Gate_Relation_Decoder.Scheduler_Resume_Pending_Drain_Gate_Relation_Decoder"
begin

lemma resume_pending_gate_task_observationD:
  assumes rel:
    "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
  shows
    "TaskObservationRel D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) a"
  using rel
  unfolding resume_pending_gate_entry_rel_def Let_def
  by blast

end
