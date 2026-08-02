theory Scheduler_Concurrent_Environment_Closure
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Concurrent_Environment_Step.Scheduler_Concurrent_Environment_Step"
begin
inductive scheduler_environment_steps ::
  "('tid \<Rightarrow> 32 word) \<Rightarrow>
   'tid concurrent_scheduler_state \<Rightarrow>
   'tid concurrent_scheduler_state \<Rightarrow> bool"
for K_E where
  EnvStepsRefl:
    "scheduler_environment_steps K_E c c"
| EnvStepsSnoc:
    "scheduler_environment_steps K_E c m \<Longrightarrow>
     scheduler_environment_step K_E m c' \<Longrightarrow>
     scheduler_environment_steps K_E c c'"

lemma environment_steps_frames_control:
  assumes "scheduler_environment_steps K_E c c'"
  shows
    "cs_critical_depth c' = cs_critical_depth c \<and>
     cs_interrupt_masked c' = cs_interrupt_masked c \<and>
     cs_saved_masks c' = cs_saved_masks c \<and>
     cs_phase c' = cs_phase c \<and>
     cs_resume_yielded c' = cs_resume_yielded c"
  using assms
proof (induction rule: scheduler_environment_steps.induct)
  case EnvStepsRefl
  then show ?case by simp
next
  case (EnvStepsSnoc c m c')
  moreover have
    "cs_critical_depth c' = cs_critical_depth m \<and>
     cs_interrupt_masked c' = cs_interrupt_masked m \<and>
     cs_saved_masks c' = cs_saved_masks m \<and>
     cs_phase c' = cs_phase m \<and>
     cs_resume_yielded c' = cs_resume_yielded m"
    using environment_step_frames_control[OF EnvStepsSnoc.hyps(2)] .
  ultimately show ?case by simp
qed

lemma environment_steps_frames_task_domain:
  assumes "scheduler_environment_steps K_E c c'"
  shows
    "cs_allocated c' = cs_allocated c \<and>
     cs_termination c' = cs_termination c"
  using assms
proof (induction rule: scheduler_environment_steps.induct)
  case EnvStepsRefl
  then show ?case by simp
next
  case (EnvStepsSnoc c m c')
  moreover have
    "cs_allocated c' = cs_allocated m \<and>
     cs_termination c' = cs_termination m"
    by (rule environment_step_frames_task_domain[OF EnvStepsSnoc.hyps(2)])
  ultimately show ?case by simp
qed

lemma environment_steps_preserve_generic_view:
  assumes "scheduler_environment_steps K_E c c'"
  shows "GenericSchedulerViewEq (cs_abs c) (cs_abs c')"
  using assms
proof (induction rule: scheduler_environment_steps.induct)
  case EnvStepsRefl
  then show ?case by simp
next
  case (EnvStepsSnoc c m c')
  have tail: "GenericSchedulerViewEq (cs_abs m) (cs_abs c')"
    by (rule environment_step_preserves_generic_view[OF EnvStepsSnoc.hyps(2)])
  show ?case
    by (rule GenericSchedulerViewEq_trans[OF EnvStepsSnoc.IH tail])
qed

lemma environment_steps_preserve_TaskObservationRel:
  assumes steps: "scheduler_environment_steps K_E c c'"
    and observation: "TaskObservationRel D h (cs_abs c)"
  shows "TaskObservationRel D h (cs_abs c')"
  using GenericSchedulerViewEq_preserves_TaskObservationRel[
      OF environment_steps_preserve_generic_view[OF steps] observation] .

lemma environment_steps_preserve_AllocatedTaskObservationRel:
  assumes steps: "scheduler_environment_steps K_E c c'"
    and observation:
      "AllocatedTaskObservationRel
         D h (cs_allocated c) (sa_priority (cs_abs c))"
  shows
    "AllocatedTaskObservationRel
       D h (cs_allocated c') (sa_priority (cs_abs c'))"
  using observation environment_steps_frames_task_domain[OF steps]
    environment_steps_preserve_generic_view[OF steps]
  by (auto simp: AllocatedTaskObservationRel_def GenericSchedulerViewEq_def)

lemma environment_steps_preserve_task_domain_wf:
  assumes steps: "scheduler_environment_steps K_E c c'"
    and domain: "ConcurrentTaskDomainWF c"
  shows "ConcurrentTaskDomainWF c'"
  using domain environment_steps_frames_task_domain[OF steps]
    environment_steps_preserve_generic_view[OF steps]
  by (auto simp: ConcurrentTaskDomainWF_def GenericSchedulerViewEq_def)

lemma environment_steps_trans:
  assumes "scheduler_environment_steps K_E a b"
    and "scheduler_environment_steps K_E b c"
  shows "scheduler_environment_steps K_E a c"
  using assms(2,1)
proof (induction arbitrary: a rule: scheduler_environment_steps.induct)
  case (EnvStepsRefl c)
  then show ?case by simp
next
  case (EnvStepsSnoc b m c)
  then show ?case
    by (meson scheduler_environment_steps.EnvStepsSnoc)
qed

end
