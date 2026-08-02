theory Scheduler_Concurrent_State
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Task_Observation_Rel.Scheduler_Task_Observation_Rel"
    "EAL6_FreeRTOS_V611_Scheduler_Generic_Root_Universe_Coverage.Scheduler_Generic_Root_Universe_Coverage"
begin

section \<open>Concurrent contract boundary\<close>

text \<open>
  This theory is a pure rely/guarantee and linearisation-point interface for
  task-context/ISR interleavings.  It does not open generated C, and none of
  the relations below is claimed to be a generated-source refinement theorem.

  The state and all transition parameters are universally quantified.  In
  particular, no task identity, priority, tick, delay, Event key, pending-ring
  length, critical nesting depth, interrupt-mask history, or missed-work
  counter is fixed.  Concrete generated-source work must later prove that its
  source-ordered cutpoints implement the program steps and that its interrupt
  handlers implement the environment steps.

  scheduler_environment_step is deliberately the rely relation for the open
  scheduler-suspended window of the delay/resume protocol.  It does not
  underhandedly stand for ticks or event unblocks while the scheduler is
  quiescent; those change the Generic scheduler view immediately and require a
  separate ISR operation contract before any whole-scheduler concurrency
  theorem can be claimed.
\<close>

datatype scheduler_linear_phase =
    ConcurrentQuiescent
  | ConcurrentSuspendedWindow
  | ConcurrentResumeDrain
  | ConcurrentResumeLinearised

record 'tid concurrent_scheduler_state =
  cs_abs :: "'tid scheduler_abs"
  cs_allocated :: "'tid set"
  cs_termination :: "'tid node_ring"
  cs_critical_depth :: nat
  cs_interrupt_masked :: bool
  cs_saved_masks :: "bool list"
  cs_phase :: scheduler_linear_phase
  cs_resume_yielded :: "bool option"

fun saved_mask_stack_wf :: "bool list \<Rightarrow> bool" where
  "saved_mask_stack_wf [] = True"
| "saved_mask_stack_wf (m # ms) =
     (if ms = [] then True else m \<and> saved_mask_stack_wf ms)"

text \<open>
  The saved-mask stack is newest first.  Every saved mask except the oldest
  must be True: after the first critical entry, every nested entry observes
  interrupts already masked.  The oldest element remains arbitrary, so this
  also covers entry from a caller that arrived with interrupts masked.
\<close>

definition ConcurrentTaskDomainWF ::
  "'tid concurrent_scheduler_state \<Rightarrow> bool"
where
  "ConcurrentTaskDomainWF c \<longleftrightarrow>
     finite (cs_allocated c) \<and>
     sa_live (cs_abs c) \<subseteq> cs_allocated c \<and>
     xlist_wf (cs_termination c) \<and>
     generic_ring (cs_termination c) \<and>
     tail_cursor_wf (cs_termination c) \<and>
     generic_task_set (cs_termination c) =
       cs_allocated c - sa_live (cs_abs c)"

definition AllocatedTaskObservationRel ::
  "'tid scheduler_decode \<Rightarrow> heap_mem \<Rightarrow>
   'tid set \<Rightarrow> ('tid \<Rightarrow> nat) \<Rightarrow> bool"
where
  "AllocatedTaskObservationRel D h allocated priority \<longleftrightarrow>
     finite allocated \<and>
     (\<forall>t \<in> allocated.
       c_guard (sd_tcb_ptr D t) \<and>
       c_guard (scheduler_generic_item_ptr (sd_tcb_ptr D t)) \<and>
       c_guard (scheduler_event_item_ptr (sd_tcb_ptr D t)) \<and>
       priority t < 4 \<and>
       unat (Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
         (h_val h (sd_tcb_ptr D t))) = priority t \<and>
       Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
         (h_val h (sd_tcb_ptr D t)) < 4 \<and>
       Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
         (h_val h (scheduler_generic_item_ptr (sd_tcb_ptr D t))) =
           PTR_COERCE(Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow> unit)
             (sd_tcb_ptr D t) \<and>
       Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
         (h_val h (scheduler_event_item_ptr (sd_tcb_ptr D t))) =
           PTR_COERCE(Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow> unit)
             (sd_tcb_ptr D t))"

definition concurrent_control_wf ::
  "'tid concurrent_scheduler_state \<Rightarrow> bool"
where
  "concurrent_control_wf c \<longleftrightarrow>
     cs_critical_depth c = length (cs_saved_masks c) \<and>
     saved_mask_stack_wf (cs_saved_masks c) \<and>
     (cs_critical_depth c > 0 \<longrightarrow> cs_interrupt_masked c)"

definition environment_window_open ::
  "'tid concurrent_scheduler_state \<Rightarrow> bool"
where
  "environment_window_open c \<longleftrightarrow>
     cs_critical_depth c = 0 \<and> \<not> cs_interrupt_masked c"

definition program_region_protected ::
  "'tid concurrent_scheduler_state \<Rightarrow> bool"
where
  "program_region_protected c \<longleftrightarrow>
     cs_critical_depth c > 0 \<or> cs_interrupt_masked c"

definition stable_linear_phase :: "scheduler_linear_phase \<Rightarrow> bool"
where
  "stable_linear_phase ph \<longleftrightarrow>
     ph = ConcurrentQuiescent \<or> ph = ConcurrentSuspendedWindow"

definition concurrent_phase_wf ::
  "'tid concurrent_scheduler_state \<Rightarrow> bool"
where
  "concurrent_phase_wf c \<longleftrightarrow>
     (case cs_phase c of
        ConcurrentQuiescent \<Rightarrow> sa_suspend_depth (cs_abs c) = 0
      | ConcurrentSuspendedWindow \<Rightarrow>
          sa_suspend_depth (cs_abs c) > 0
      | ConcurrentResumeDrain \<Rightarrow>
          sa_suspend_depth (cs_abs c) > 0 \<and>
          program_region_protected c \<and>
          cs_resume_yielded c = None
      | ConcurrentResumeLinearised \<Rightarrow>
          program_region_protected c \<and>
          cs_resume_yielded c \<noteq> None)"

definition concurrent_state_wf ::
  "'tid concurrent_scheduler_state \<Rightarrow> bool"
where
  "concurrent_state_wf c \<longleftrightarrow>
     concurrent_control_wf c \<and> concurrent_phase_wf c"

text \<open>
  concurrent_state_wf is intentionally the control/phase invariant proved
  closed by the abstract interleaving algebra.  The stronger representation
  cutpoint separately conjoins core_wf and ConcurrentTaskDomainWF; calling the
  control/phase fact a heap or scheduler invariant would overstate it.
\<close>

lemma open_iff_not_protected:
  "environment_window_open c \<longleftrightarrow>
   \<not> program_region_protected c"
  by (auto simp: environment_window_open_def program_region_protected_def)

lemma concurrent_state_wf_controlD:
  "concurrent_state_wf c \<Longrightarrow> concurrent_control_wf c"
  by (simp add: concurrent_state_wf_def)

lemma concurrent_state_wf_phaseD:
  "concurrent_state_wf c \<Longrightarrow> concurrent_phase_wf c"
  by (simp add: concurrent_state_wf_def)

section \<open>Pending-ready Event interference\<close>

definition enqueue_pending_event_abs ::
  "('tid \<Rightarrow> 32 word) \<Rightarrow> 'tid \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> 'tid scheduler_abs"
where
  "enqueue_pending_event_abs K_E t a =
     a\<lparr>
       sa_pending := list_insert_end_abs (Event t) (K_E t) (sa_pending a),
       sa_event_waiting := sa_event_waiting a - {t}
     \<rparr>"

text \<open>
  GenericSchedulerViewEq deliberately forgets Event ownership and the two
  deferred-work scalars.  Thus an ISR may move a TCB's Event item from an
  external Event root to pending-ready while its distinct Generic item stays
  delayed or suspended.  This is the abstraction boundary needed by the
  pending-drain phases; it must not be strengthened to whole-state equality.
\<close>

definition GenericSchedulerViewEq ::
  "'tid scheduler_abs \<Rightarrow> 'tid scheduler_abs \<Rightarrow> bool"
where
  "GenericSchedulerViewEq a b \<longleftrightarrow>
     sa_live b = sa_live a \<and>
     sa_priority b = sa_priority a \<and>
     sa_wake b = sa_wake a \<and>
     sa_ready b = sa_ready a \<and>
     sa_delayed_a b = sa_delayed_a a \<and>
     sa_delayed_b b = sa_delayed_b a \<and>
     sa_current_role_a b = sa_current_role_a a \<and>
     sa_suspended b = sa_suspended a \<and>
     sa_tick b = sa_tick a \<and>
     sa_suspend_depth b = sa_suspend_depth a \<and>
     sa_top_ready b = sa_top_ready a \<and>
     sa_current b = sa_current a \<and>
     sa_overflows b = sa_overflows a \<and>
     sa_yield_count b = sa_yield_count a"

lemma GenericSchedulerViewEq_refl [simp]:
  "GenericSchedulerViewEq a a"
  by (simp add: GenericSchedulerViewEq_def)

lemma GenericSchedulerViewEq_sym:
  "GenericSchedulerViewEq a b \<Longrightarrow> GenericSchedulerViewEq b a"
  by (auto simp: GenericSchedulerViewEq_def)

lemma GenericSchedulerViewEq_trans:
  assumes "GenericSchedulerViewEq a b"
    and "GenericSchedulerViewEq b c"
  shows "GenericSchedulerViewEq a c"
  using assms by (auto simp: GenericSchedulerViewEq_def)

lemma enqueue_pending_event_generic_view [simp]:
  "GenericSchedulerViewEq a (enqueue_pending_event_abs K_E t a)"
  by (simp add: GenericSchedulerViewEq_def enqueue_pending_event_abs_def)

lemma enqueue_pending_event_key [simp]:
  "item_key (sa_pending (enqueue_pending_event_abs K_E t a)) (Event t) =
   K_E t"
  by (simp add: enqueue_pending_event_abs_def list_insert_end_abs_def)

lemma enqueue_pending_event_waiting [simp]:
  "sa_event_waiting (enqueue_pending_event_abs K_E t a) =
   sa_event_waiting a - {t}"
  by (simp add: enqueue_pending_event_abs_def)

lemma enqueue_pending_event_member:
  assumes wf: "xlist_wf (sa_pending a)"
  shows
    "Event t \<in>
       set (ring (sa_pending (enqueue_pending_event_abs K_E t a)))"
proof -
  have
    "set (ring (list_insert_end_abs (Event t) (K_E t) (sa_pending a))) =
     insert (Event t) (set (ring (sa_pending a)))"
    using list_insert_end_ring_set[OF wf] .
  then show ?thesis
    by (simp add: enqueue_pending_event_abs_def)
qed

end
