theory Scheduler_Resume_Inner_Source
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_General_Relation.Scheduler_Resume_General_Relation"
begin

text \<open>
  Universal generated-source bridge for the inner-resume branch.  The only
  scheduler condition is that the positive suspension depth remains nonzero
  after the source decrement.  Therefore xTaskResumeAll returns before reading
  any pending-ready root, missed-tick counter, TCB, priority, or list node.
  Those values, and the complete heap, remain symbolic and are framed by the
  exact whole-globals equality.
\<close>

definition scheduler_resume_inner_state ::
  "Scheduler_V611_Parse.globals \<Rightarrow> Scheduler_V611_Parse.globals"
where
  "scheduler_resume_inner_state c =
     Scheduler_V611_Parse.globals.uxSchedulerSuspended_'_update
       (\<lambda>n. n - 1) c"

definition resume_inner_abs ::
  "'tid scheduler_abs \<Rightarrow> 'tid scheduler_abs"
where
  "resume_inner_abs a =
     a\<lparr>sa_suspend_depth := sa_suspend_depth a - 1\<rparr>"

lemma ResumeRel_inner_constructor:
  assumes inner: "1 < sa_suspend_depth a"
  shows "ResumeRel a False (resume_inner_abs a)"
  using inner
  by (simp add: ResumeRel_def resume_inner_abs_def Let_def)

theorem scheduler_xTaskResumeAll_inner_exact:
  fixes c :: Scheduler_V611_Parse.globals
  assumes inner:
      "Scheduler_V611_Parse.globals.uxSchedulerSuspended_' c - 1 \<noteq> 0"
    and depth:
      "Scheduler_V611_Parse.globals.eal6_port_critical_depth_' c = 0"
    and interrupts:
      "Scheduler_V611_Parse.globals.eal6_port_interrupts_disabled_' c = 0"
  shows
    "Scheduler_V611_Delay_Translation.xTaskResumeAll' \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result 0 \<and>
       t = scheduler_resume_inner_state c
     \<rbrace>"
proof -
  have not_one:
    "Scheduler_V611_Parse.globals.uxSchedulerSuspended_' c \<noteq> 1"
    using inner by auto
  show ?thesis
    unfolding Scheduler_V611_Delay_Translation.xTaskResumeAll'_def
      Scheduler_V611_Tick_Translation.eal6_port_enter_critical'_def
      Scheduler_V611_Tick_Translation.eal6_port_exit_critical'_def
      scheduler_resume_inner_state_def
    apply runs_to_vcg
    apply (simp_all add: inner not_one depth interrupts)
    done
qed

lemma scheduler_control_mod_rel_resume_inner:
  assumes rel: "scheduler_control_mod_rel c a"
    and inner: "1 < sa_suspend_depth a"
  shows
    "scheduler_control_mod_rel
       (scheduler_resume_inner_state c) (resume_inner_abs a)"
proof -
  let ?w = "Scheduler_V611_Parse.globals.uxSchedulerSuspended_' c"
  have count: "unat ?w = sa_suspend_depth a"
    using rel by (simp add: scheduler_control_mod_rel_def)
  have nonzero: "?w \<noteq> 0"
    using count inner by auto
  have predecessor: "Suc (unat (?w - 1)) = unat ?w"
    by (rule Suc_unat_minus_one[OF nonzero])
  have decreased:
    "unat (?w - 1) = sa_suspend_depth a - 1"
    using count predecessor inner by arith
  show ?thesis
    using rel decreased
    by (simp add: scheduler_control_mod_rel_def
        scheduler_resume_inner_state_def resume_inner_abs_def)
qed

theorem scheduler_xTaskResumeAll_inner_refines_ResumeRel:
  fixes c :: Scheduler_V611_Parse.globals
    and a :: "'tid scheduler_abs"
  assumes rel: "scheduler_control_mod_rel c a"
    and inner: "1 < sa_suspend_depth a"
    and depth:
      "Scheduler_V611_Parse.globals.eal6_port_critical_depth_' c = 0"
    and interrupts:
      "Scheduler_V611_Parse.globals.eal6_port_interrupts_disabled_' c = 0"
  shows
    "Scheduler_V611_Delay_Translation.xTaskResumeAll' \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result 0 \<and>
       t = scheduler_resume_inner_state c \<and>
       scheduler_control_mod_rel t (resume_inner_abs a) \<and>
       ResumeRel a False (resume_inner_abs a)
     \<rbrace>"
proof -
  let ?w = "Scheduler_V611_Parse.globals.uxSchedulerSuspended_' c"
  have count: "unat ?w = sa_suspend_depth a"
    using rel by (simp add: scheduler_control_mod_rel_def)
  have nonzero: "?w \<noteq> 0"
    using count inner by auto
  have predecessor: "Suc (unat (?w - 1)) = unat ?w"
    by (rule Suc_unat_minus_one[OF nonzero])
  have branch: "?w - 1 \<noteq> 0"
    using count predecessor inner by auto
  note source = scheduler_xTaskResumeAll_inner_exact[
      OF branch depth interrupts]
  have control:
    "scheduler_control_mod_rel
       (scheduler_resume_inner_state c) (resume_inner_abs a)"
    by (rule scheduler_control_mod_rel_resume_inner[OF rel inner])
  have abstract: "ResumeRel a False (resume_inner_abs a)"
    by (rule ResumeRel_inner_constructor[OF inner])
  show ?thesis
    apply (rule runs_to_weaken[OF source])
    using control abstract by auto
qed

end
