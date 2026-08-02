theory Scheduler_Concurrent_Environment_Step
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Concurrent_State.Scheduler_Concurrent_State"
begin
section \<open>Rely: ISR/environment steps\<close>

inductive scheduler_environment_step ::
  "('tid \<Rightarrow> 32 word) \<Rightarrow>
   'tid concurrent_scheduler_state \<Rightarrow>
   'tid concurrent_scheduler_state \<Rightarrow> bool"
for K_E where
  EnvTick:
    "environment_window_open c \<Longrightarrow>
     cs_phase c = ConcurrentSuspendedWindow \<Longrightarrow>
     sa_suspend_depth (cs_abs c) > 0 \<Longrightarrow>
     c' = c\<lparr>cs_abs := task_increment_tick_abs (cs_abs c)\<rparr> \<Longrightarrow>
     scheduler_environment_step K_E c c'"
| EnvYieldRequest:
    "environment_window_open c \<Longrightarrow>
     cs_phase c = ConcurrentSuspendedWindow \<Longrightarrow>
     sa_suspend_depth (cs_abs c) > 0 \<Longrightarrow>
     c' = c\<lparr>cs_abs := task_switch_context_abs (cs_abs c)\<rparr> \<Longrightarrow>
     scheduler_environment_step K_E c c'"
| EnvPendReady:
    "environment_window_open c \<Longrightarrow>
     cs_phase c = ConcurrentSuspendedWindow \<Longrightarrow>
     sa_suspend_depth (cs_abs c) > 0 \<Longrightarrow>
     t \<in> sa_event_waiting (cs_abs c) \<Longrightarrow>
     Event t \<notin> set (ring (sa_pending (cs_abs c))) \<Longrightarrow>
     xlist_wf (sa_pending (cs_abs c)) \<Longrightarrow>
     c' = c\<lparr>cs_abs := enqueue_pending_event_abs K_E t (cs_abs c)\<rparr> \<Longrightarrow>
     scheduler_environment_step K_E c c'"

lemma environment_step_requires_open:
  assumes "scheduler_environment_step K_E c c'"
  shows "environment_window_open c"
  using assms by (cases rule: scheduler_environment_step.cases) auto

lemma environment_step_requires_suspended_window:
  assumes "scheduler_environment_step K_E c c'"
  shows
    "cs_phase c = ConcurrentSuspendedWindow \<and>
     sa_suspend_depth (cs_abs c) > 0"
  using assms by (cases rule: scheduler_environment_step.cases) auto

lemma protected_region_excludes_environment:
  assumes "program_region_protected c"
  shows "\<not> scheduler_environment_step K_E c c'"
  using assms environment_step_requires_open open_iff_not_protected by blast

lemma environment_step_frames_control:
  assumes "scheduler_environment_step K_E c c'"
  shows
    "cs_critical_depth c' = cs_critical_depth c \<and>
     cs_interrupt_masked c' = cs_interrupt_masked c \<and>
     cs_saved_masks c' = cs_saved_masks c \<and>
     cs_phase c' = cs_phase c \<and>
     cs_resume_yielded c' = cs_resume_yielded c"
  using assms by (cases rule: scheduler_environment_step.cases) auto

lemma environment_step_frames_task_domain:
  assumes "scheduler_environment_step K_E c c'"
  shows
    "cs_allocated c' = cs_allocated c \<and>
     cs_termination c' = cs_termination c"
  using assms by (cases rule: scheduler_environment_step.cases) auto

lemma environment_step_preserves_control_wf:
  assumes step: "scheduler_environment_step K_E c c'"
    and wf: "concurrent_control_wf c"
  shows "concurrent_control_wf c'"
  using step wf environment_step_frames_control
  by (auto simp: concurrent_control_wf_def)

lemma environment_step_preserves_phase_wf:
  assumes step: "scheduler_environment_step K_E c c'"
    and wf: "concurrent_phase_wf c"
  shows "concurrent_phase_wf c'"
  using step wf
  by (cases rule: scheduler_environment_step.cases)
     (auto simp: concurrent_phase_wf_def program_region_protected_def
       task_increment_tick_abs_def task_switch_context_abs_def
       enqueue_pending_event_abs_def)

lemma environment_step_preserves_state_wf:
  assumes step: "scheduler_environment_step K_E c c'"
    and wf: "concurrent_state_wf c"
  shows "concurrent_state_wf c'"
  using environment_step_preserves_control_wf[OF step]
    environment_step_preserves_phase_wf[OF step] wf
  by (auto simp: concurrent_state_wf_def)

lemma environment_tick_is_missed_tick:
  assumes window: "environment_window_open c"
    and phase: "cs_phase c = ConcurrentSuspendedWindow"
    and suspended: "sa_suspend_depth (cs_abs c) > 0"
  shows
    "scheduler_environment_step K_E c
       (c\<lparr>cs_abs :=
          (cs_abs c)\<lparr>
            sa_missed_ticks := Suc (sa_missed_ticks (cs_abs c))
          \<rparr>\<rparr>)"
proof -
  have nonzero: "sa_suspend_depth (cs_abs c) \<noteq> 0"
    using suspended by simp
  have tick:
    "task_increment_tick_abs (cs_abs c) =
       (cs_abs c)\<lparr>
         sa_missed_ticks := Suc (sa_missed_ticks (cs_abs c))
       \<rparr>"
    by (rule task_increment_tick_while_suspended[OF nonzero])
  show ?thesis
    by (rule scheduler_environment_step.EnvTick[OF window phase suspended])
       (simp add: tick)
qed

lemma environment_yield_is_missed_yield:
  assumes window: "environment_window_open c"
    and phase: "cs_phase c = ConcurrentSuspendedWindow"
    and suspended: "sa_suspend_depth (cs_abs c) > 0"
  shows
    "scheduler_environment_step K_E c
       (c\<lparr>cs_abs := (cs_abs c)\<lparr>sa_missed_yield := True\<rparr>\<rparr>)"
proof -
  have nonzero: "sa_suspend_depth (cs_abs c) \<noteq> 0"
    using suspended by simp
  have request:
    "task_switch_context_abs (cs_abs c) =
       (cs_abs c)\<lparr>sa_missed_yield := True\<rparr>"
    by (rule task_switch_context_while_suspended[OF nonzero])
  show ?thesis
    by (rule scheduler_environment_step.EnvYieldRequest[
      OF window phase suspended])
       (simp add: request)
qed

lemma environment_pending_step_preserves_generic_view:
  assumes window: "environment_window_open c"
    and phase: "cs_phase c = ConcurrentSuspendedWindow"
    and suspended: "sa_suspend_depth (cs_abs c) > 0"
    and waiting: "t \<in> sa_event_waiting (cs_abs c)"
    and absent: "Event t \<notin> set (ring (sa_pending (cs_abs c)))"
    and wf: "xlist_wf (sa_pending (cs_abs c))"
  shows
    "scheduler_environment_step K_E c
       (c\<lparr>cs_abs := enqueue_pending_event_abs K_E t (cs_abs c)\<rparr>)
     \<and>
     GenericSchedulerViewEq (cs_abs c)
       (cs_abs
         (c\<lparr>cs_abs :=
           enqueue_pending_event_abs K_E t (cs_abs c)\<rparr>))"
  using window phase suspended waiting absent wf
  by (auto intro: scheduler_environment_step.EnvPendReady)

lemma environment_step_preserves_generic_view:
  assumes step: "scheduler_environment_step K_E c c'"
  shows "GenericSchedulerViewEq (cs_abs c) (cs_abs c')"
  using step
  by (cases rule: scheduler_environment_step.cases)
     (auto simp: GenericSchedulerViewEq_def enqueue_pending_event_abs_def
       task_increment_tick_abs_def task_switch_context_abs_def)

lemma GenericSchedulerViewEq_preserves_TaskObservationRel:
  assumes view: "GenericSchedulerViewEq a b"
    and observation: "TaskObservationRel D h a"
  shows "TaskObservationRel D h b"
  using view observation
  by (auto simp: GenericSchedulerViewEq_def TaskObservationRel_def)

lemma environment_step_preserves_TaskObservationRel:
  assumes step: "scheduler_environment_step K_E c c'"
    and observation: "TaskObservationRel D h (cs_abs c)"
  shows "TaskObservationRel D h (cs_abs c')"
  using GenericSchedulerViewEq_preserves_TaskObservationRel[
      OF environment_step_preserves_generic_view[OF step] observation] .

lemma environment_step_preserves_AllocatedTaskObservationRel:
  assumes step: "scheduler_environment_step K_E c c'"
    and observation:
      "AllocatedTaskObservationRel
         D h (cs_allocated c) (sa_priority (cs_abs c))"
  shows
    "AllocatedTaskObservationRel
       D h (cs_allocated c') (sa_priority (cs_abs c'))"
  using observation environment_step_frames_task_domain[OF step]
    environment_step_preserves_generic_view[OF step]
  by (auto simp: AllocatedTaskObservationRel_def GenericSchedulerViewEq_def)

lemma environment_step_preserves_task_domain_wf:
  assumes step: "scheduler_environment_step K_E c c'"
    and domain: "ConcurrentTaskDomainWF c"
  shows "ConcurrentTaskDomainWF c'"
  using domain environment_step_frames_task_domain[OF step]
    environment_step_preserves_generic_view[OF step]
  by (auto simp: ConcurrentTaskDomainWF_def GenericSchedulerViewEq_def)

end
