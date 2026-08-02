theory Scheduler_Resume_Outer_Quiet_Bool
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Outer_Scaffold.Scheduler_Resume_Outer_Scaffold"
begin

text \<open>
  Universal sequential quiet-resume leaf for the two legal Boolean encodings
  of xMissedYield.  The pending-ready ring and missed-tick debt are empty, so
  this is deliberately not the general resume theorem.  Within that branch,
  however, the heap, task set, priorities, tick, current task, root pointers,
  yield counter and every unrelated global remain arbitrary.

  The generated source order is: enter critical, decrement suspension depth,
  observe the empty pending list and zero missed-tick debt, optionally clear
  xMissedYield and invoke the proof-port yield, then exit critical.  Word
  addition below is the native modulo-2^32 counter effect; no no-wrap premise
  is used.
\<close>

definition scheduler_resume_bool_word :: "bool \<Rightarrow> 32 signed word"
where
  "scheduler_resume_bool_word b = (if b then 1 else 0)"

definition scheduler_resume_bool_counter_delta :: "bool \<Rightarrow> 32 word"
where
  "scheduler_resume_bool_counter_delta b = (if b then 1 else 0)"

definition scheduler_resume_outer_quiet_bool_state ::
  "bool \<Rightarrow> Scheduler_V611_Parse.globals \<Rightarrow>
   Scheduler_V611_Parse.globals"
where
  "scheduler_resume_outer_quiet_bool_state yielded c =
     Scheduler_V611_Parse.globals.eal6_port_yield_count_'_update
       (\<lambda>n. n + scheduler_resume_bool_counter_delta yielded)
       (Scheduler_V611_Parse.globals.xMissedYield_'_update
         (\<lambda>_. 0)
         (Scheduler_V611_Parse.globals.uxSchedulerSuspended_'_update
           (\<lambda>n. n - 1) c))"

lemma scheduler_resume_bool_word_sint:
  "sint (scheduler_resume_bool_word b) = resume_result_word b"
  by (cases b; simp add: scheduler_resume_bool_word_def resume_result_word_def)

lemma scheduler_resume_bool_encodings_agree:
  "uint (scheduler_resume_bool_counter_delta b) =
    sint (scheduler_resume_bool_word b)"
  by (cases b; simp add: scheduler_resume_bool_counter_delta_def
      scheduler_resume_bool_word_def)

lemma scheduler_resume_outer_quiet_bool_state_false:
  assumes missed_yield:
    "Scheduler_V611_Parse.globals.xMissedYield_' c = 0"
  shows
    "scheduler_resume_outer_quiet_bool_state False c =
       scheduler_resume_outer_quiet_state c"
  using missed_yield
  by (simp add: scheduler_resume_outer_quiet_bool_state_def
      scheduler_resume_outer_quiet_state_def scheduler_resume_bool_word_def
      scheduler_resume_bool_counter_delta_def)

text \<open>
  This is the new generated-source branch: an entry missed-yield bit of one
  forces exactly one call of eal6_port_yield.  In particular, the counter
  update is valid even at max_word, where it wraps to zero.
\<close>

theorem scheduler_xTaskResumeAll_outer_quiet_missed_yield_exact:
  fixes c :: Scheduler_V611_Parse.globals
  assumes suspended:
      "Scheduler_V611_Parse.globals.uxSchedulerSuspended_' c = 1"
    and depth:
      "Scheduler_V611_Parse.globals.eal6_port_critical_depth_' c = 0"
    and interrupts:
      "Scheduler_V611_Parse.globals.eal6_port_interrupts_disabled_' c = 0"
    and pending_guard:
      "c_guard Scheduler_V611_Parse.xPendingReadyList_'"
    and pending_empty:
      "Scheduler_V611_Parse.xLIST_C.uxNumberOfItems_C
        (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
          Scheduler_V611_Parse.xPendingReadyList_') = 0"
    and missed_ticks:
      "Scheduler_V611_Parse.globals.uxMissedTicks_' c = 0"
    and missed_yield:
      "Scheduler_V611_Parse.globals.xMissedYield_' c = 1"
    and current_tasks:
      "Scheduler_V611_Parse.globals.uxCurrentNumberOfTasks_' c \<noteq> 0"
  shows
    "Scheduler_V611_Delay_Translation.xTaskResumeAll' \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result (resume_result_word True) \<and>
       t = scheduler_resume_outer_quiet_bool_state True c
     \<rbrace>"
proof -
  have current_tasks_positive:
    "0 < Scheduler_V611_Parse.globals.uxCurrentNumberOfTasks_' c"
    using current_tasks by (simp add: word_gt_0)
  show ?thesis
    unfolding Scheduler_V611_Delay_Translation.xTaskResumeAll'_def
      Scheduler_V611_Tick_Translation.eal6_port_enter_critical'_def
      Scheduler_V611_Tick_Translation.eal6_port_exit_critical'_def
      Scheduler_V611_Delay_Translation.eal6_port_yield'_def
      vTaskIncrementTick'_def
      scheduler_resume_outer_quiet_bool_state_def
      scheduler_resume_bool_word_def scheduler_resume_bool_counter_delta_def
      resume_result_word_def
    apply runs_to_vcg
    apply (simp_all add: suspended depth interrupts pending_guard
        pending_empty missed_ticks missed_yield current_tasks
        current_tasks_positive h_val_heap_update)
    apply (subst runs_to_whileLoop_cond_fail)
     apply simp
    apply runs_to_vcg
    apply (simp_all add: suspended depth interrupts pending_guard
        pending_empty missed_ticks missed_yield current_tasks
        current_tasks_positive h_val_heap_update)
    done
qed

text \<open>
  The quantified Boolean is the entry xMissedYield value.  Thus this one
  theorem covers both legal encodings without fixing the branch in its public
  statement: false returns zero and performs no yield, while true returns one
  and performs exactly one yield.
\<close>

theorem scheduler_xTaskResumeAll_outer_quiet_bool_exact:
  fixes c :: Scheduler_V611_Parse.globals
    and yielded :: bool
  assumes suspended:
      "Scheduler_V611_Parse.globals.uxSchedulerSuspended_' c = 1"
    and depth:
      "Scheduler_V611_Parse.globals.eal6_port_critical_depth_' c = 0"
    and interrupts:
      "Scheduler_V611_Parse.globals.eal6_port_interrupts_disabled_' c = 0"
    and pending_guard:
      "c_guard Scheduler_V611_Parse.xPendingReadyList_'"
    and pending_empty:
      "Scheduler_V611_Parse.xLIST_C.uxNumberOfItems_C
        (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
          Scheduler_V611_Parse.xPendingReadyList_') = 0"
    and missed_ticks:
      "Scheduler_V611_Parse.globals.uxMissedTicks_' c = 0"
    and missed_yield:
      "Scheduler_V611_Parse.globals.xMissedYield_' c =
        scheduler_resume_bool_word yielded"
    and current_tasks:
      "Scheduler_V611_Parse.globals.uxCurrentNumberOfTasks_' c \<noteq> 0"
  shows
    "Scheduler_V611_Delay_Translation.xTaskResumeAll' \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result (resume_result_word yielded) \<and>
       t = scheduler_resume_outer_quiet_bool_state yielded c
     \<rbrace>"
proof (cases yielded)
  case False
  have missed_yield_zero:
    "Scheduler_V611_Parse.globals.xMissedYield_' c = 0"
    using missed_yield False
    by (simp add: scheduler_resume_bool_word_def)
  note source = scheduler_xTaskResumeAll_outer_quiet_general_exact
    [OF suspended depth interrupts pending_guard pending_empty missed_ticks
      missed_yield_zero current_tasks]
  show ?thesis
    apply (rule runs_to_weaken[OF source])
    using scheduler_resume_outer_quiet_bool_state_false[OF missed_yield_zero]
      False
    by (simp add: resume_result_word_def)
next
  case True
  have missed_yield_one:
    "Scheduler_V611_Parse.globals.xMissedYield_' c = 1"
    using missed_yield True
    by (simp add: scheduler_resume_bool_word_def)
  note source = scheduler_xTaskResumeAll_outer_quiet_missed_yield_exact
    [OF suspended depth interrupts pending_guard pending_empty missed_ticks
      missed_yield_one current_tasks]
  show ?thesis
    using True source by simp
qed

corollary scheduler_xTaskResumeAll_outer_quiet_bool_entry_bit_and_frames:
  fixes c :: Scheduler_V611_Parse.globals
    and yielded :: bool
  assumes suspended:
      "Scheduler_V611_Parse.globals.uxSchedulerSuspended_' c = 1"
    and depth:
      "Scheduler_V611_Parse.globals.eal6_port_critical_depth_' c = 0"
    and interrupts:
      "Scheduler_V611_Parse.globals.eal6_port_interrupts_disabled_' c = 0"
    and pending_guard:
      "c_guard Scheduler_V611_Parse.xPendingReadyList_'"
    and pending_empty:
      "Scheduler_V611_Parse.xLIST_C.uxNumberOfItems_C
        (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
          Scheduler_V611_Parse.xPendingReadyList_') = 0"
    and missed_ticks:
      "Scheduler_V611_Parse.globals.uxMissedTicks_' c = 0"
    and missed_yield:
      "Scheduler_V611_Parse.globals.xMissedYield_' c =
        scheduler_resume_bool_word yielded"
    and current_tasks:
      "Scheduler_V611_Parse.globals.uxCurrentNumberOfTasks_' c \<noteq> 0"
  shows
    "Scheduler_V611_Delay_Translation.xTaskResumeAll' \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result (sint
         (Scheduler_V611_Parse.globals.xMissedYield_' c)) \<and>
       t = scheduler_resume_outer_quiet_bool_state yielded c \<and>
       Scheduler_V611_Parse.globals.uxSchedulerSuspended_' t = 0 \<and>
       Scheduler_V611_Parse.globals.xMissedYield_' t = 0 \<and>
       Scheduler_V611_Parse.globals.eal6_port_yield_count_' t =
         Scheduler_V611_Parse.globals.eal6_port_yield_count_' c +
           scheduler_resume_bool_counter_delta yielded \<and>
       Scheduler_V611_Parse.globals.t_hrs_' t =
         Scheduler_V611_Parse.globals.t_hrs_' c \<and>
       Scheduler_V611_Parse.globals.pxCurrentTCB_' t =
         Scheduler_V611_Parse.globals.pxCurrentTCB_' c \<and>
       Scheduler_V611_Parse.globals.pxDelayedTaskList_' t =
         Scheduler_V611_Parse.globals.pxDelayedTaskList_' c \<and>
       Scheduler_V611_Parse.globals.pxOverflowDelayedTaskList_' t =
         Scheduler_V611_Parse.globals.pxOverflowDelayedTaskList_' c \<and>
       Scheduler_V611_Parse.globals.xTickCount_' t =
         Scheduler_V611_Parse.globals.xTickCount_' c \<and>
       Scheduler_V611_Parse.globals.uxCurrentNumberOfTasks_' t =
         Scheduler_V611_Parse.globals.uxCurrentNumberOfTasks_' c \<and>
       Scheduler_V611_Parse.globals.uxTopReadyPriority_' t =
         Scheduler_V611_Parse.globals.uxTopReadyPriority_' c \<and>
       Scheduler_V611_Parse.globals.xNumOfOverflows_' t =
         Scheduler_V611_Parse.globals.xNumOfOverflows_' c \<and>
       Scheduler_V611_Parse.globals.xSchedulerRunning_' t =
         Scheduler_V611_Parse.globals.xSchedulerRunning_' c \<and>
       Scheduler_V611_Parse.globals.eal6_port_critical_depth_' t = 0 \<and>
       Scheduler_V611_Parse.globals.eal6_port_interrupts_disabled_' t = 0
     \<rbrace>"
proof -
  note source = scheduler_xTaskResumeAll_outer_quiet_bool_exact
    [OF suspended depth interrupts pending_guard pending_empty missed_ticks
      missed_yield current_tasks]
  have result_bit:
    "resume_result_word yielded =
      sint (Scheduler_V611_Parse.globals.xMissedYield_' c)"
    using missed_yield scheduler_resume_bool_word_sint[of yielded]
    by simp
  show ?thesis
    apply (rule runs_to_weaken[OF source])
    using result_bit suspended depth interrupts
    by (simp add: scheduler_resume_outer_quiet_bool_state_def)
qed

end
