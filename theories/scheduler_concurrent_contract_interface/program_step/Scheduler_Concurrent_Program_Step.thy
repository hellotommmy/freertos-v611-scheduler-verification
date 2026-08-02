theory Scheduler_Concurrent_Program_Step
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Concurrent_Environment_Closure.Scheduler_Concurrent_Environment_Closure"
begin
section \<open>Guarantee: task-context linearisation steps\<close>

text \<open>
  ResumeRel is one abstract linearisation step, not a claim that the concrete
  pending drain is one machine instruction.  ConcurrentResumeDrain and
  ConcurrentResumeLinearised bracket its source-ordered Event unlink,
  Generic unlink, ready insertion, missed-tick replay, and yield aggregation.
  cs_resume_yielded retains the exact ResumeRel result across ProgFinishResume,
  so the caller's later "yield only when resume did not" branch is not erased
  by existentially hiding the return value.
  The protected-region premises rule out ISR rely steps between those concrete
  cutpoints; the generated-source proof must still represent the temporary
  Unlinked/Keyed/Inserted heap phases.

  A critical exit may expose interrupts only from a stable phase.  Nested exits
  inside the drain remain permitted when another critical level or a saved
  masked state continues to protect the region.
\<close>

inductive scheduler_program_step ::
  "'tid concurrent_scheduler_state \<Rightarrow>
   'tid concurrent_scheduler_state \<Rightarrow> bool"
where
  ProgEnterCritical:
    "c' = c\<lparr>
       cs_critical_depth := Suc (cs_critical_depth c),
       cs_interrupt_masked := True,
       cs_saved_masks := cs_interrupt_masked c # cs_saved_masks c
     \<rparr> \<Longrightarrow>
     scheduler_program_step c c'"

| ProgExitCritical:
    "cs_saved_masks c = old_mask # rest \<Longrightarrow>
     (rest = [] \<and> \<not> old_mask \<longrightarrow>
        stable_linear_phase (cs_phase c)) \<Longrightarrow>
     c' = c\<lparr>
       cs_critical_depth := cs_critical_depth c - 1,
       cs_interrupt_masked := old_mask,
       cs_saved_masks := rest
     \<rparr> \<Longrightarrow>
     scheduler_program_step c c'"
| ProgSuspendLinearise:
    "program_region_protected c \<Longrightarrow>
     stable_linear_phase (cs_phase c) \<Longrightarrow>
     c' = c\<lparr>
       cs_abs := (cs_abs c)\<lparr>
         sa_suspend_depth := Suc (sa_suspend_depth (cs_abs c))
       \<rparr>,
       cs_phase := ConcurrentSuspendedWindow
     \<rparr> \<Longrightarrow>
     scheduler_program_step c c'"
| ProgBeginResume:
    "program_region_protected c \<Longrightarrow>
     cs_phase c = ConcurrentSuspendedWindow \<Longrightarrow>
     sa_suspend_depth (cs_abs c) > 0 \<Longrightarrow>
     c' = c\<lparr>
       cs_phase := ConcurrentResumeDrain,
       cs_resume_yielded := None
     \<rparr> \<Longrightarrow>
     scheduler_program_step c c'"
| ProgResumeLinearise:
    "program_region_protected c \<Longrightarrow>
     cs_phase c = ConcurrentResumeDrain \<Longrightarrow>
     ResumeRel (cs_abs c) yielded a' \<Longrightarrow>
     c' = c\<lparr>
       cs_abs := a',
       cs_phase := ConcurrentResumeLinearised,
       cs_resume_yielded := Some yielded
     \<rparr> \<Longrightarrow>
     scheduler_program_step c c'"
| ProgFinishResume:
    "program_region_protected c \<Longrightarrow>
     cs_phase c = ConcurrentResumeLinearised \<Longrightarrow>
     c' = c\<lparr>cs_phase :=
       (if sa_suspend_depth (cs_abs c) = 0
        then ConcurrentQuiescent
        else ConcurrentSuspendedWindow)\<rparr> \<Longrightarrow>
     scheduler_program_step c c'"

lemma program_step_frames_task_domain:
  assumes "scheduler_program_step c c'"
  shows
    "cs_allocated c' = cs_allocated c \<and>
     cs_termination c' = cs_termination c"
  using assms by (cases rule: scheduler_program_step.cases) auto

lemma enter_critical_establishes_protection:
  "scheduler_program_step c
     (c\<lparr>
       cs_critical_depth := Suc (cs_critical_depth c),
       cs_interrupt_masked := True,
       cs_saved_masks := cs_interrupt_masked c # cs_saved_masks c
      \<rparr>)"
  by (rule scheduler_program_step.ProgEnterCritical) simp

lemma enter_critical_blocks_environment:
  shows
    "\<not> scheduler_environment_step K_E
       (c\<lparr>
         cs_critical_depth := Suc (cs_critical_depth c),
         cs_interrupt_masked := True,
         cs_saved_masks := cs_interrupt_masked c # cs_saved_masks c
        \<rparr>) c'"
  by (rule protected_region_excludes_environment)
     (simp add: program_region_protected_def)

lemma program_step_preserves_control_wf:
  assumes step: "scheduler_program_step c c'"
    and wf: "concurrent_control_wf c"
  shows "concurrent_control_wf c'"
proof -
  have pop:
    "\<And>old_mask rest.
       saved_mask_stack_wf (old_mask # rest) \<Longrightarrow>
       saved_mask_stack_wf rest \<and> (rest \<noteq> [] \<longrightarrow> old_mask)"
    by (case_tac rest) auto
  show ?thesis
    using step wf
    by (cases rule: scheduler_program_step.cases)
       (auto simp: concurrent_control_wf_def dest: pop split: if_splits)
qed

lemma program_step_preserves_state_wf:
  assumes step: "scheduler_program_step c c'"
    and wf: "concurrent_state_wf c"
  shows "concurrent_state_wf c'"
proof -
  have control_before: "concurrent_control_wf c"
    using wf by (simp add: concurrent_state_wf_def)
  have phase_before: "concurrent_phase_wf c"
    using wf by (simp add: concurrent_state_wf_def)
  have control_after: "concurrent_control_wf c'"
    by (rule program_step_preserves_control_wf[OF step control_before])
  have phase_after: "concurrent_phase_wf c'"
    using step phase_before control_before
    by (cases rule: scheduler_program_step.cases)
       (auto simp: concurrent_phase_wf_def concurrent_control_wf_def
         stable_linear_phase_def program_region_protected_def
         split: scheduler_linear_phase.splits if_splits)
  show ?thesis
    using control_after phase_after
    by (simp add: concurrent_state_wf_def)
qed

lemma resume_linearisation_is_ResumeRel:
  assumes step: "scheduler_program_step c c'"
    and before: "cs_phase c = ConcurrentResumeDrain"
    and after: "cs_phase c' = ConcurrentResumeLinearised"
  shows
    "\<exists>yielded.
       ResumeRel (cs_abs c) yielded (cs_abs c') \<and>
       cs_resume_yielded c' = Some yielded"
  using step before after
  by (cases rule: scheduler_program_step.cases) auto

lemma finish_resume_preserves_yield_result:
  assumes step: "scheduler_program_step c c'"
    and before: "cs_phase c = ConcurrentResumeLinearised"
    and after: "stable_linear_phase (cs_phase c')"
  shows "cs_resume_yielded c' = cs_resume_yielded c"
  using step before after
  by (cases rule: scheduler_program_step.cases)
     (auto simp: stable_linear_phase_def)

lemma suspend_linearisation_increments_symbolic_depth:
  assumes protected: "program_region_protected c"
    and phase: "stable_linear_phase (cs_phase c)"
  defines "c' \<equiv> c\<lparr>
    cs_abs := (cs_abs c)\<lparr>
      sa_suspend_depth := Suc (sa_suspend_depth (cs_abs c))
    \<rparr>,
    cs_phase := ConcurrentSuspendedWindow
  \<rparr>"
  shows
    "scheduler_program_step c c' \<and>
     sa_suspend_depth (cs_abs c') = Suc (sa_suspend_depth (cs_abs c))"
  using protected phase
  unfolding c'_def
  by (auto intro: scheduler_program_step.ProgSuspendLinearise)

end
