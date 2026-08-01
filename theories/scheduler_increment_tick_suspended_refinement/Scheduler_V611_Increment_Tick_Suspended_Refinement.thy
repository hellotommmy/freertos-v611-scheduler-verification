theory Scheduler_V611_Increment_Tick_Suspended_Refinement
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Switch_Suspended_Refinement.Scheduler_V611_Switch_Suspended_Refinement"
begin

text \<open>
  Second scheduler control-projection refinement rung.  A hardware tick that
  arrives while the scheduler is suspended is not committed to xTickCount and
  does not inspect either delayed list.  The source records one 32-bit missed
  tick; the abstract model records one natural-number debt.  Their arithmetic
  agrees only before the concrete word reaches its maximum value, so the
  no-wrap premise is explicit rather than hidden in simplification.
\<close>

definition scheduler_missed_tick_no_wrap :: "globals \<Rightarrow> bool"
where
  "scheduler_missed_tick_no_wrap c \<longleftrightarrow>
     uxMissedTicks_' c \<noteq> (-1 :: 32 word)"

lemma missed_tick_unat_add_one:
  assumes no_wrap: "scheduler_missed_tick_no_wrap c"
  shows
    "unat (uxMissedTicks_' c + 1) =
       Suc (unat (uxMissedTicks_' c))"
  using no_wrap
  unfolding scheduler_missed_tick_no_wrap_def
  by (metis add.commute max_word_wrap unatSuc)

text \<open>
  A concrete non-vacuity witness sets both missed-tick ledgers to zero and the
  suspension depth to one.  No raw heap validity is required on this branch.
\<close>

lemma scheduler_increment_tick_suspended_pre_witness:
  "scheduler_control_rel
     (c\<lparr>
        uxSchedulerSuspended_' := 1,
        uxMissedTicks_' := 0,
        xMissedYield_' := 0
      \<rparr>)
     (a\<lparr>
        sa_tick := xTickCount_' c,
        sa_missed_ticks := 0,
        sa_suspend_depth := 1,
        sa_missed_yield := False,
        sa_yield_count := unat (eal6_port_yield_count_' c)
      \<rparr>) \<and>
   sa_suspend_depth
     (a\<lparr>
        sa_tick := xTickCount_' c,
        sa_missed_ticks := 0,
        sa_suspend_depth := 1,
        sa_missed_yield := False,
        sa_yield_count := unat (eal6_port_yield_count_' c)
      \<rparr>) \<noteq> 0 \<and>
   scheduler_missed_tick_no_wrap
     (c\<lparr>
        uxSchedulerSuspended_' := 1,
        uxMissedTicks_' := 0,
        xMissedYield_' := 0
      \<rparr>)"
  by (simp add: scheduler_control_rel_def
      scheduler_missed_tick_no_wrap_def)

lemma scheduler_control_rel_increment_missed_tick:
  assumes rel: "scheduler_control_rel c a"
      and no_wrap: "scheduler_missed_tick_no_wrap c"
  shows
    "scheduler_control_rel
       (uxMissedTicks_'_update (\<lambda>n. n + 1) c)
       (a\<lparr>sa_missed_ticks := Suc (sa_missed_ticks a)\<rparr>)"
proof -
  have step:
    "unat (uxMissedTicks_' c + 1) =
       Suc (unat (uxMissedTicks_' c))"
    using missed_tick_unat_add_one[OF no_wrap] .
  show ?thesis
    using rel step
    by (simp add: scheduler_control_rel_def)
qed

text \<open>
  Exact source semantics do not need the no-wrap premise: C is allowed to
  wrap.  The bound is introduced only when transferring the word update to
  the abstract natural-number Suc operation.
\<close>

theorem vTaskIncrementTick_suspended_result:
  assumes suspended: "uxSchedulerSuspended_' c \<noteq> 0"
  shows
    "vTaskIncrementTick' \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       t = uxMissedTicks_'_update (\<lambda>n. n + 1) c
     \<rbrace>"
proof -
  show ?thesis
    unfolding vTaskIncrementTick'_def
    apply runs_to_vcg
    apply (simp_all add: suspended)
    done
qed

definition scheduler_increment_tick_suspended_frame ::
  "globals \<Rightarrow> globals \<Rightarrow> bool"
where
  "scheduler_increment_tick_suspended_frame c t \<longleftrightarrow>
     t_hrs_' t = t_hrs_' c \<and>
     pxCurrentTCB_' t = pxCurrentTCB_' c \<and>
     pxDelayedTaskList_' t = pxDelayedTaskList_' c \<and>
     pxOverflowDelayedTaskList_' t = pxOverflowDelayedTaskList_' c \<and>
     uxTopReadyPriority_' t = uxTopReadyPriority_' c \<and>
     uxCurrentNumberOfTasks_' t = uxCurrentNumberOfTasks_' c \<and>
     xTickCount_' t = xTickCount_' c \<and>
     uxSchedulerSuspended_' t = uxSchedulerSuspended_' c \<and>
     xMissedYield_' t = xMissedYield_' c \<and>
     xNumOfOverflows_' t = xNumOfOverflows_' c \<and>
     eal6_port_critical_depth_' t = eal6_port_critical_depth_' c \<and>
     eal6_port_interrupts_disabled_' t =
       eal6_port_interrupts_disabled_' c \<and>
     eal6_port_yield_count_' t = eal6_port_yield_count_' c"

corollary vTaskIncrementTick_suspended_strong_frame:
  assumes suspended: "uxSchedulerSuspended_' c \<noteq> 0"
      and no_wrap: "scheduler_missed_tick_no_wrap c"
  shows
    "vTaskIncrementTick' \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       uxMissedTicks_' t = uxMissedTicks_' c + 1 \<and>
       unat (uxMissedTicks_' t) =
         Suc (unat (uxMissedTicks_' c)) \<and>
       scheduler_increment_tick_suspended_frame c t
     \<rbrace>"
proof -
  have step:
    "unat (uxMissedTicks_' c + 1) =
       Suc (unat (uxMissedTicks_' c))"
    using missed_tick_unat_add_one[OF no_wrap] .
  note exact = vTaskIncrementTick_suspended_result[OF suspended]
  show ?thesis
    apply (rule runs_to_weaken[OF exact])
    using step
    apply (clarsimp simp: scheduler_increment_tick_suspended_frame_def)
    done
qed

theorem vTaskIncrementTick_suspended_refines:
  assumes rel: "scheduler_control_rel c a"
      and suspended: "sa_suspend_depth a \<noteq> 0"
      and no_wrap: "scheduler_missed_tick_no_wrap c"
  shows
    "vTaskIncrementTick' \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       t = uxMissedTicks_'_update (\<lambda>n. n + 1) c \<and>
       scheduler_control_rel t (task_increment_tick_abs a)
     \<rbrace>"
proof -
  have source_suspended: "uxSchedulerSuspended_' c \<noteq> 0"
    using scheduler_control_rel_source_suspended[OF rel suspended] .
  have abstract_step:
    "task_increment_tick_abs a =
       a\<lparr>sa_missed_ticks := Suc (sa_missed_ticks a)\<rparr>"
    using task_increment_tick_while_suspended[OF suspended] .
  have marked:
    "scheduler_control_rel
       (uxMissedTicks_'_update (\<lambda>n. n + 1) c)
       (a\<lparr>sa_missed_ticks := Suc (sa_missed_ticks a)\<rparr>)"
    using scheduler_control_rel_increment_missed_tick[OF rel no_wrap] .
  note exact = vTaskIncrementTick_suspended_result[OF source_suspended]
  show ?thesis
    apply (rule runs_to_weaken[OF exact])
    using marked abstract_step
    apply clarsimp
    done
qed

end
