theory Scheduler_Resume_Generated_Missed_Loop
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Drain_Abs_Fold.Scheduler_Resume_Generated_Drain_Abs_Fold"
begin

text \<open>
  Parametric composition of the generated missed-tick replay loop.  The body
  of the generated loop is \<open>vTaskIncrementTick'\<close> followed by the
  \<open>uxMissedTicks\<close> decrement; a complete unlocked-tick source proof does
  not exist yet, so the single-iteration effect enters as an explicit
  premise: any relation \<open>Rel\<close> that (i) exposes the concrete
  \<open>uxMissedTicks\<close> counter as \<open>sa_missed_ticks\<close> and (ii) is preserved
  by one generated body execution mapping the abstract state through
  \<open>resume_missed_source_step_abs\<close> is carried through the whole loop,
  which then performs exactly
  \<open>resume_missed_source_steps_abs (sa_missed_ticks a)\<close> and exits with a
  zero counter.  No tick count, task population, heap layout or wake
  pattern is fixed.  Once the unlocked-tick source summary lands, it
  discharges the premise and this theorem closes the replay segment of
  \<open>xTaskResumeAll'\<close> against the outer scaffold's
  \<open>resume_missed_loop_inv\<close>.
\<close>

lemma resume_pending_gate_missed_count:
  assumes rel:
    "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
  shows "unat (Scheduler_V611_Parse.globals.uxMissedTicks_' c) =
     sa_missed_ticks a"
proof -
  have scalar: "scheduler_scalar_rel c a"
    using rel
    unfolding resume_pending_gate_entry_rel_def Let_def
    by blast
  show ?thesis
    using scalar
    unfolding scheduler_scalar_rel_def
    by blast
qed

lemma resume_missed_source_step_abs_missed_ticks:
  "sa_missed_ticks (resume_missed_source_step_abs a) =
     sa_missed_ticks a - 1"
  by (simp add: resume_missed_source_step_abs_def)

lemma resume_missed_source_steps_abs_zero:
  "sa_missed_ticks a = 0 \<Longrightarrow>
     resume_missed_source_steps_abs (sa_missed_ticks a) a = a"
  by simp

theorem resume_missed_generated_loop_replays_aux:
  fixes Rel ::
    "Scheduler_V611_Parse.globals \<Rightarrow> 'tid scheduler_abs \<Rightarrow> bool"
  assumes step:
    "\<And>c a. Rel c a \<Longrightarrow> 0 < sa_missed_ticks a \<Longrightarrow>
       resume_missed_generated_body () \<bullet> c
       \<lbrace>\<lambda>r t. r = Result () \<and>
          Rel t (resume_missed_source_step_abs a)\<rbrace>"
    and count:
    "\<And>c a. Rel c a \<Longrightarrow>
       unat (Scheduler_V611_Parse.globals.uxMissedTicks_' c) =
         sa_missed_ticks a"
  shows
    "\<And>c a. n = sa_missed_ticks a \<Longrightarrow> Rel c a \<Longrightarrow>
       whileLoop resume_missed_generated_cond
         resume_missed_generated_body () \<bullet> c
       \<lbrace>\<lambda>r t. \<exists>a'. r = Result () \<and> Rel t a' \<and>
          a' = resume_missed_source_steps_abs n a \<and>
          sa_missed_ticks a' = 0\<rbrace>"
proof (induction n)
  case (0 c a)
  have counter_zero:
    "Scheduler_V611_Parse.globals.uxMissedTicks_' c = 0"
    using count[OF "0.prems"(2)] "0.prems"(1)
    by (simp add: unat_eq_zero)
  have cond_false:
    "\<not> resume_missed_generated_cond () c"
    using counter_zero
    by (simp add: resume_missed_generated_cond_def)
  show ?case
    apply (subst runs_to_whileLoop_cond_fail
        [of resume_missed_generated_cond "()" c, OF cond_false])
    apply runs_to_vcg
    using "0.prems"
    by simp_all
next
  case (Suc n c a)
  have pos: "0 < sa_missed_ticks a"
    using Suc.prems(1) by simp
  have counter_pos:
    "Scheduler_V611_Parse.globals.uxMissedTicks_' c \<noteq> 0"
    using count[OF Suc.prems(2)] pos
    by (metis unat_eq_zero neq0_conv)
  have cond_true:
    "resume_missed_generated_cond () c"
    using counter_pos
    by (simp add: resume_missed_generated_cond_def word_neq_0_conv)
  have step_count:
    "sa_missed_ticks (resume_missed_source_step_abs a) = n"
    using Suc.prems(1)
    by (simp add: resume_missed_source_step_abs_missed_ticks)
  show ?case
    apply (subst whileLoop_unroll)
    apply (simp only: runs_to_condition_iff)
    apply (simp only: cond_true if_True)
    apply (rule runs_to_bind)
    apply (rule runs_to_weaken[OF step[OF Suc.prems(2) pos]])
    apply clarsimp
    apply (rule runs_to_weaken
        [OF Suc.IH[OF step_count[symmetric]]])
     apply assumption
    by clarify
qed

theorem resume_missed_generated_loop_replays:
  fixes Rel ::
    "Scheduler_V611_Parse.globals \<Rightarrow> 'tid scheduler_abs \<Rightarrow> bool"
  assumes step:
    "\<And>c a. Rel c a \<Longrightarrow> 0 < sa_missed_ticks a \<Longrightarrow>
       resume_missed_generated_body () \<bullet> c
       \<lbrace>\<lambda>r t. r = Result () \<and>
          Rel t (resume_missed_source_step_abs a)\<rbrace>"
    and count:
    "\<And>c a. Rel c a \<Longrightarrow>
       unat (Scheduler_V611_Parse.globals.uxMissedTicks_' c) =
         sa_missed_ticks a"
    and rel: "Rel c a"
  shows
    "whileLoop resume_missed_generated_cond
       resume_missed_generated_body () \<bullet> c
     \<lbrace>\<lambda>r t. \<exists>a'. r = Result () \<and> Rel t a' \<and>
        a' = resume_missed_source_steps_abs (sa_missed_ticks a) a \<and>
        sa_missed_ticks a' = 0\<rbrace>"
  by (rule resume_missed_generated_loop_replays_aux
      [OF step count refl rel])

corollary resume_missed_generated_loop_inv_exit:
  fixes Rel ::
    "Scheduler_V611_Parse.globals \<Rightarrow> 'tid scheduler_abs \<Rightarrow> bool"
  assumes step:
    "\<And>c a. Rel c a \<Longrightarrow> 0 < sa_missed_ticks a \<Longrightarrow>
       resume_missed_generated_body () \<bullet> c
       \<lbrace>\<lambda>r t. r = Result () \<and>
          Rel t (resume_missed_source_step_abs a)\<rbrace>"
    and count:
    "\<And>c a. Rel c a \<Longrightarrow>
       unat (Scheduler_V611_Parse.globals.uxMissedTicks_' c) =
         sa_missed_ticks a"
    and rel: "Rel c a"
  shows
    "whileLoop resume_missed_generated_cond
       resume_missed_generated_body () \<bullet> c
     \<lbrace>\<lambda>r t. \<exists>a'. r = Result () \<and> Rel t a' \<and>
        resume_missed_loop_inv a (sa_missed_ticks a)
          (sa_missed_ticks a) a'\<rbrace>"
  apply (rule runs_to_weaken
      [OF resume_missed_generated_loop_replays[OF step count rel]])
    apply assumption
   apply assumption
  apply clarify
  apply (intro exI)
  by (auto simp: resume_missed_loop_inv_def)

end
