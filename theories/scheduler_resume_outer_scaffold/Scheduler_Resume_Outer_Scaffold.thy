theory Scheduler_Resume_Outer_Scaffold
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_General_Relation.Scheduler_Resume_General_Relation"
begin

text \<open>
  Source-ordered outermost-resume scaffold.  No task identity, priority,
  pending-ring length, missed-tick count, heap, root address, or alias pattern
  is fixed.  The loop invariants expose the exact prefix already processed and
  the suffix still visible at the concrete pending head.
\<close>

definition resume_outer_entry_abs ::
  "'tid scheduler_abs \<Rightarrow> 'tid scheduler_abs"
where
  "resume_outer_entry_abs s =
     s\<lparr>sa_suspend_depth := sa_suspend_depth s - 1\<rparr>"

definition resume_pending_nodes_require_yield ::
  "'tid scheduler_abs \<Rightarrow> 'tid node_kind list \<Rightarrow> bool"
where
  "resume_pending_nodes_require_yield base nodes \<longleftrightarrow>
     (\<exists>t. Event t \<in> set nodes \<and>
        (case sa_current base of
           None \<Rightarrow> False
         | Some current \<Rightarrow>
             sa_priority base current \<le> sa_priority base t))"

definition resume_pending_loop_inv ::
  "'tid scheduler_abs \<Rightarrow> 'tid node_kind list \<Rightarrow>
   'tid node_kind list \<Rightarrow> bool \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> bool"
where
  "resume_pending_loop_inv base done todo local_yield current \<longleftrightarrow>
     ring (sa_pending base) = done @ todo \<and>
     distinct (done @ todo) \<and>
     (\<forall>n \<in> set (done @ todo). \<exists>t. n = Event t) \<and>
     current = drain_pending_nodes_abs done base \<and>
     ring (sa_pending current) = todo \<and>
     local_yield = resume_pending_nodes_require_yield base done"

definition resume_missed_source_step_abs ::
  "'tid scheduler_abs \<Rightarrow> 'tid scheduler_abs"
where
  "resume_missed_source_step_abs s =
     (tick_unlocked_abs s)\<lparr>
       sa_missed_ticks := sa_missed_ticks s - 1\<rparr>"

fun resume_missed_source_steps_abs ::
  "nat \<Rightarrow> 'tid scheduler_abs \<Rightarrow> 'tid scheduler_abs"
where
  "resume_missed_source_steps_abs 0 s = s"
| "resume_missed_source_steps_abs (Suc n) s =
     resume_missed_source_steps_abs n (resume_missed_source_step_abs s)"

definition resume_missed_loop_inv ::
  "'tid scheduler_abs \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> bool"
where
  "resume_missed_loop_inv base debt0 processed current \<longleftrightarrow>
     sa_missed_ticks base = debt0 \<and>
     processed \<le> debt0 \<and>
     current = resume_missed_source_steps_abs processed base \<and>
     sa_missed_ticks current = debt0 - processed"

definition ResumeOuterDecomp ::
  "'tid scheduler_abs \<Rightarrow> bool \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> bool"
where
  "ResumeOuterDecomp s yielded t \<longleftrightarrow>
     sa_suspend_depth s = 1 \<and>
     sa_live s \<noteq> {} \<and>
     (let entry = resume_outer_entry_abs s;
          requested = resume_yield_required entry;
          drained = drain_pending_abs entry;
          replayed =
            replay_missed_abs (sa_missed_ticks drained) drained;
          caller_state =
            (if requested
             then replayed\<lparr>sa_missed_yield := False\<rparr>
             else replayed)
      in YieldAbs requested caller_state yielded t)"

theorem ResumeRel_outermost_decomposition:
  assumes outermost: "sa_suspend_depth s = 1"
    and populated: "sa_live s \<noteq> {}"
  shows
    "ResumeRel s yielded t \<longleftrightarrow>
     ResumeOuterDecomp s yielded t"
  using outermost populated
  by (simp add: ResumeRel_def ResumeOuterDecomp_def
      resume_outer_entry_abs_def Let_def)

text \<open>
  The next three predicates state information read by the generated loop but
  absent from raw_xlist_rel/sched_xlist_rel.  They are data relations, not
  fixed witnesses: every live TCB and every possible pending head is
  quantified.
\<close>

definition scheduler_resume_tcb_payload_rel ::
  "'tid scheduler_decode \<Rightarrow> Scheduler_V611_Parse.globals \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> bool"
where
  "scheduler_resume_tcb_payload_rel D c a \<longleftrightarrow>
     (let h = hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)
      in \<forall>t \<in> sa_live a.
        c_guard (sd_tcb_ptr D t) \<and>
        unat (Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
          (h_val h (sd_tcb_ptr D t))) = sa_priority a t \<and>
        Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
          (h_val h (scheduler_generic_item_ptr (sd_tcb_ptr D t))) =
            PTR_COERCE(Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow> unit)
              (sd_tcb_ptr D t) \<and>
        Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
          (h_val h (scheduler_event_item_ptr (sd_tcb_ptr D t))) =
            PTR_COERCE(Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow> unit)
              (sd_tcb_ptr D t))"

definition scheduler_pending_head_rel ::
  "'tid scheduler_decode \<Rightarrow> scheduler_roots \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> 'tid scheduler_abs \<Rightarrow> bool"
where
  "scheduler_pending_head_rel D R c a \<longleftrightarrow>
     (let h = hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c);
          lp = sr_pending R;
          head = Scheduler_V611_Parse.xMINI_LIST_ITEM_C.pxNext_C
            (Scheduler_V611_Parse.xLIST_C.xListEnd_C (h_val h lp))
      in \<forall>t todo. ring (sa_pending a) = Event t # todo \<longrightarrow>
        head = scheduler_event_item_ptr (sd_tcb_ptr D t) \<and>
        c_guard head \<and> c_guard (sd_tcb_ptr D t))"

definition scheduler_resume_rep_rel ::
  "'tid scheduler_decode \<Rightarrow> scheduler_roots \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> 'tid scheduler_abs \<Rightarrow> bool"
where
  "scheduler_resume_rep_rel D R c a \<longleftrightarrow>
     core_wf a \<and>
     scheduler_decode_rel D a \<and>
     scheduler_lists_rel D R c a \<and>
     scheduler_role_rel R c a \<and>
     scheduler_scalar_rel c a \<and>
     scheduler_current_rel D c a \<and>
     scheduler_resume_tcb_payload_rel D c a"

definition resume_result_word :: "bool \<Rightarrow> int"
where
  "resume_result_word yielded = (if yielded then 1 else 0)"

text \<open>
  Exact generated-source specialization for an outermost resume with no
  pending work, no missed ticks, and no missed-yield request.  The live task
  count is only required to be nonzero; it is not fixed to the old two-task
  witness.  Every heap byte, task identity, priority, list population and
  pointer remains symbolic, and the result changes only the suspension word.
\<close>

definition scheduler_resume_outer_quiet_state ::
  "Scheduler_V611_Parse.globals \<Rightarrow> Scheduler_V611_Parse.globals"
where
  "scheduler_resume_outer_quiet_state c =
     Scheduler_V611_Parse.globals.uxSchedulerSuspended_'_update
       (\<lambda>n. n - 1) c"

theorem scheduler_xTaskResumeAll_outer_quiet_general_exact:
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
      "Scheduler_V611_Parse.globals.xMissedYield_' c = 0"
    and current_tasks:
      "Scheduler_V611_Parse.globals.uxCurrentNumberOfTasks_' c \<noteq> 0"
  shows
    "Scheduler_V611_Delay_Translation.xTaskResumeAll' \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result 0 \<and> t = scheduler_resume_outer_quiet_state c
     \<rbrace>"
  unfolding Scheduler_V611_Delay_Translation.xTaskResumeAll'_def
    Scheduler_V611_Tick_Translation.eal6_port_enter_critical'_def
    Scheduler_V611_Tick_Translation.eal6_port_exit_critical'_def
    Scheduler_V611_Delay_Translation.eal6_port_yield'_def
    vTaskIncrementTick'_def
    scheduler_resume_outer_quiet_state_def
  apply runs_to_vcg
  apply (simp_all add: suspended depth interrupts pending_guard
      pending_empty missed_ticks missed_yield current_tasks h_val_heap_update)
  apply (subst runs_to_whileLoop_cond_fail)
   apply simp
  apply runs_to_vcg
  apply (simp_all add: suspended depth interrupts pending_guard
      pending_empty missed_ticks missed_yield current_tasks h_val_heap_update)
  done

text \<open>
  This consequence rule is the honest source-level handoff.  Its premise is
  the still-unproved generated-loop summary, preserving an arbitrary post
  representation predicate.  Once pending-drain and unlocked-tick source
  summaries establish ResumeOuterDecomp, no reopening or re-analysis of the
  final ResumeRel definition is needed.
\<close>

theorem scheduler_xTaskResumeAll_outer_summary_to_ResumeRel:
  fixes PostRel ::
    "Scheduler_V611_Parse.globals \<Rightarrow> 'tid scheduler_abs \<Rightarrow> bool"
  assumes outermost: "sa_suspend_depth a = 1"
    and populated: "sa_live a \<noteq> {}"
    and source_summary:
      "Scheduler_V611_Delay_Translation.xTaskResumeAll' \<bullet> c
       \<lbrace>\<lambda>r t.
         \<exists>yielded a'.
           r = Result (resume_result_word yielded) \<and>
           ResumeOuterDecomp a yielded a' \<and>
           PostRel t a'
       \<rbrace>"
  shows
    "Scheduler_V611_Delay_Translation.xTaskResumeAll' \<bullet> c
     \<lbrace>\<lambda>r t.
       \<exists>yielded a'.
         r = Result (resume_result_word yielded) \<and>
         ResumeRel a yielded a' \<and>
         PostRel t a'
     \<rbrace>"
proof -
  have decomp:
    "\<And>yielded a'. ResumeOuterDecomp a yielded a' \<Longrightarrow>
       ResumeRel a yielded a'"
    using ResumeRel_outermost_decomposition[OF outermost populated]
    by blast
  show ?thesis
    apply (rule runs_to_weaken[OF source_summary])
    using decomp by blast
qed

end
