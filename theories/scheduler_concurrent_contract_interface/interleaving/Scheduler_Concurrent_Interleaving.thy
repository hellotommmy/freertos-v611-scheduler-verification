theory Scheduler_Concurrent_Interleaving
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Concurrent_Program_Step.Scheduler_Concurrent_Program_Step"
begin
section \<open>Interleaving algebra\<close>

inductive scheduler_interleaving ::
  "('tid \<Rightarrow> 32 word) \<Rightarrow>
   'tid concurrent_scheduler_state \<Rightarrow>
   'tid concurrent_scheduler_state \<Rightarrow> bool"
for K_E where
  InterleaveRefl:
    "scheduler_interleaving K_E c c"
| InterleaveEnv:
    "scheduler_interleaving K_E c m \<Longrightarrow>
     scheduler_environment_step K_E m c' \<Longrightarrow>
     scheduler_interleaving K_E c c'"
| InterleaveProg:
    "scheduler_interleaving K_E c m \<Longrightarrow>
     scheduler_program_step m c' \<Longrightarrow>
     scheduler_interleaving K_E c c'"

lemma scheduler_interleaving_trans:
  assumes "scheduler_interleaving K_E a b"
    and "scheduler_interleaving K_E b c"
  shows "scheduler_interleaving K_E a c"
  using assms(2,1)
proof (induction arbitrary: a rule: scheduler_interleaving.induct)
  case (InterleaveRefl c)
  then show ?case by simp
next
  case (InterleaveEnv b m c)
  then show ?case by (meson scheduler_interleaving.InterleaveEnv)
next
  case (InterleaveProg b m c)
  then show ?case by (meson scheduler_interleaving.InterleaveProg)
qed

lemma scheduler_interleaving_preserves_control_wf:
  assumes trace: "scheduler_interleaving K_E c c'"
    and wf: "concurrent_control_wf c"
  shows "concurrent_control_wf c'"
  using trace wf
proof (induction rule: scheduler_interleaving.induct)
  case InterleaveRefl
  then show ?case .
next
  case (InterleaveEnv c m c')
  then show ?case
    using environment_step_preserves_control_wf by blast
next
  case (InterleaveProg c m c')
  then show ?case
    using program_step_preserves_control_wf by blast
qed

lemma scheduler_interleaving_frames_task_domain:
  assumes "scheduler_interleaving K_E c c'"
  shows
    "cs_allocated c' = cs_allocated c \<and>
     cs_termination c' = cs_termination c"
  using assms
proof (induction rule: scheduler_interleaving.induct)
  case InterleaveRefl
  then show ?case by simp
next
  case (InterleaveEnv c m c')
  moreover have
    "cs_allocated c' = cs_allocated m \<and>
     cs_termination c' = cs_termination m"
    by (rule environment_step_frames_task_domain[OF InterleaveEnv.hyps(2)])
  ultimately show ?case by simp
next
  case (InterleaveProg c m c')
  moreover have
    "cs_allocated c' = cs_allocated m \<and>
     cs_termination c' = cs_termination m"
    by (rule program_step_frames_task_domain[OF InterleaveProg.hyps(2)])
  ultimately show ?case by simp
qed

lemma scheduler_interleaving_preserves_state_wf:
  assumes trace: "scheduler_interleaving K_E c c'"
    and wf: "concurrent_state_wf c"
  shows "concurrent_state_wf c'"
  using trace wf
proof (induction rule: scheduler_interleaving.induct)
  case InterleaveRefl
  then show ?case .
next
  case (InterleaveEnv c m c')
  then show ?case
    using environment_step_preserves_state_wf by blast
next
  case (InterleaveProg c m c')
  then show ?case
    using program_step_preserves_state_wf by blast
qed

end
