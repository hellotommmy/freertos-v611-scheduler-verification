theory Scheduler_V611_Switch_Suspended_Refinement
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Roots.Scheduler_V611_Roots_Translation"
    "EAL6_FreeRTOS_V611_Scheduler_Abstract_Model.Scheduler_Abstract_Model"
begin

text \<open>
  A deliberately narrow but genuine scheduler source-to-abstract rung.
  When the scheduler is suspended, vTaskSwitchContext must not inspect or
  mutate any ready list and must not perform a proof-port yield.  It records
  exactly one deferred-yield request instead.  This theory relates the scalar
  scheduler-control projection only; it is not yet the full raw list/TCB
  representation relation needed by the unlocked branch.
\<close>

definition scheduler_control_rel ::
  "globals \<Rightarrow> 'tid scheduler_abs \<Rightarrow> bool"
where
  "scheduler_control_rel c a \<longleftrightarrow>
     xTickCount_' c = sa_tick a \<and>
     unat (uxSchedulerSuspended_' c) = sa_suspend_depth a \<and>
     unat (uxMissedTicks_' c) = sa_missed_ticks a \<and>
     xMissedYield_' c = (if sa_missed_yield a then 1 else 0) \<and>
     unat (eal6_port_yield_count_' c) = sa_yield_count a"

text \<open>
  The relation is inhabited on a suspended state without imposing any heap
  validity premise: the selected source branch reaches its return before the
  first ready-list access.
\<close>

lemma scheduler_control_rel_suspended_witness:
  "scheduler_control_rel
     (c\<lparr>uxSchedulerSuspended_' := 1, xMissedYield_' := 0\<rparr>)
     (a\<lparr>
        sa_tick := xTickCount_' c,
        sa_missed_ticks := unat (uxMissedTicks_' c),
        sa_suspend_depth := 1,
        sa_missed_yield := False,
        sa_yield_count := unat (eal6_port_yield_count_' c)
      \<rparr>) \<and>
   sa_suspend_depth
     (a\<lparr>
        sa_tick := xTickCount_' c,
        sa_missed_ticks := unat (uxMissedTicks_' c),
        sa_suspend_depth := 1,
        sa_missed_yield := False,
        sa_yield_count := unat (eal6_port_yield_count_' c)
      \<rparr>) \<noteq> 0"
  by (simp add: scheduler_control_rel_def)

lemma scheduler_control_rel_source_suspended:
  assumes rel: "scheduler_control_rel c a"
      and suspended: "sa_suspend_depth a \<noteq> 0"
  shows "uxSchedulerSuspended_' c \<noteq> 0"
  using rel suspended
  by (auto simp: scheduler_control_rel_def)

lemma scheduler_control_rel_set_missed_yield:
  assumes rel: "scheduler_control_rel c a"
  shows
    "scheduler_control_rel
       (xMissedYield_'_update (\<lambda>_. 1) c)
       (a\<lparr>sa_missed_yield := True\<rparr>)"
  using rel
  by (simp add: scheduler_control_rel_def)

text \<open>
  This is the exact source result, before any abstraction weakening.  In
  particular, equality with the one-field record update frames the complete
  raw heap and every other generated global.
\<close>

theorem vTaskSwitchContext_suspended_result:
  assumes suspended: "uxSchedulerSuspended_' c \<noteq> 0"
  shows
    "vTaskSwitchContext' \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       t = xMissedYield_'_update (\<lambda>_. 1) c
     \<rbrace>"
proof -
  show ?thesis
    unfolding vTaskSwitchContext'_def
    apply runs_to_vcg
    apply (simp_all add: suspended)
    done
qed

definition scheduler_switch_suspended_frame ::
  "globals \<Rightarrow> globals \<Rightarrow> bool"
where
  "scheduler_switch_suspended_frame c t \<longleftrightarrow>
     t_hrs_' t = t_hrs_' c \<and>
     pxCurrentTCB_' t = pxCurrentTCB_' c \<and>
     pxDelayedTaskList_' t = pxDelayedTaskList_' c \<and>
     pxOverflowDelayedTaskList_' t = pxOverflowDelayedTaskList_' c \<and>
     uxTopReadyPriority_' t = uxTopReadyPriority_' c \<and>
     uxCurrentNumberOfTasks_' t = uxCurrentNumberOfTasks_' c \<and>
     xTickCount_' t = xTickCount_' c \<and>
     uxSchedulerSuspended_' t = uxSchedulerSuspended_' c \<and>
     uxMissedTicks_' t = uxMissedTicks_' c \<and>
     xNumOfOverflows_' t = xNumOfOverflows_' c \<and>
     eal6_port_critical_depth_' t = eal6_port_critical_depth_' c \<and>
     eal6_port_interrupts_disabled_' t =
       eal6_port_interrupts_disabled_' c \<and>
     eal6_port_yield_count_' t = eal6_port_yield_count_' c"

corollary vTaskSwitchContext_suspended_strong_frame:
  assumes suspended: "uxSchedulerSuspended_' c \<noteq> 0"
  shows
    "vTaskSwitchContext' \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       xMissedYield_' t = 1 \<and>
       scheduler_switch_suspended_frame c t
     \<rbrace>"
proof -
  note exact = vTaskSwitchContext_suspended_result[OF suspended]
  show ?thesis
    apply (rule runs_to_weaken[OF exact])
    apply (clarsimp simp: scheduler_switch_suspended_frame_def)
    done
qed

theorem vTaskSwitchContext_suspended_refines:
  assumes rel: "scheduler_control_rel c a"
      and suspended: "sa_suspend_depth a \<noteq> 0"
  shows
    "vTaskSwitchContext' \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       t = xMissedYield_'_update (\<lambda>_. 1) c \<and>
       scheduler_control_rel t (task_switch_context_abs a)
     \<rbrace>"
proof -
  have source_suspended: "uxSchedulerSuspended_' c \<noteq> 0"
    using scheduler_control_rel_source_suspended[OF rel suspended] .
  have abstract_step:
    "task_switch_context_abs a =
       a\<lparr>sa_missed_yield := True\<rparr>"
    using task_switch_context_while_suspended[OF suspended] .
  have marked:
    "scheduler_control_rel
       (xMissedYield_'_update (\<lambda>_. 1) c)
       (a\<lparr>sa_missed_yield := True\<rparr>)"
    using scheduler_control_rel_set_missed_yield[OF rel] .
  note exact = vTaskSwitchContext_suspended_result[OF source_suspended]
  show ?thesis
    apply (rule runs_to_weaken[OF exact])
    using marked abstract_step
    apply clarsimp
    done
qed

end
