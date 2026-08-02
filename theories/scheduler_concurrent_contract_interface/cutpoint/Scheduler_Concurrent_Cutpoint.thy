theory Scheduler_Concurrent_Cutpoint
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Concurrent_Interleaving.Scheduler_Concurrent_Interleaving"
begin
section \<open>Representation cutpoint interface\<close>

text \<open>
  ConcurrentCutpointInterface uses the complete frozen root universes rather
  than accepting an opaque predicate that could be instantiated by True.  The
  Event universe is the distinguished generated pending root plus an arbitrary
  finite external-root set.  The Generic universe is exactly all four ready
  roots, both delayed roots, suspended, and termination-wait.

  The two projection predicates below are load-bearing.  The Event projection
  says both that the pending root denotes sa_pending and that membership in
  every external Event root is exactly sa_event_waiting.  The Generic
  projection connects every operational Generic root to the corresponding
  scheduler_abs ring and connects termination-wait to cs_termination.
  cs_allocated is deliberately distinct from sa_live: the former includes the
  arbitrary finite termination-wait population, while the latter is the
  active scheduler domain.  This closes the root-coverage hole without
  pretending that create/delete transitions themselves have been refined.

  This is only an endpoint/cutpoint interface.  Preservation across a concrete
  environment or program step requires a generated-source heap theorem for
  that step; no such theorem is assumed or manufactured here.
\<close>

definition event_family_waiting_tasks ::
  "xLIST_C ptr set \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow> 'tid set"
where
  "event_family_waiting_tasks external abs_event =
     {t. \<exists>lp\<in>external.
        Event t \<in> set (ring (abs_event lp))}"

definition EventSchedulerStateProjection ::
  "xLIST_C ptr set \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> bool"
where
  "EventSchedulerStateProjection external abs_event a \<longleftrightarrow>
     abs_event GeneratedPendingEventRoot = sa_pending a \<and>
     event_family_waiting_tasks external abs_event = sa_event_waiting a"

definition GenericSchedulerStateProjection ::
  "(xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow>
   'tid concurrent_scheduler_state \<Rightarrow> bool"
where
  "GenericSchedulerStateProjection abs_generic c \<longleftrightarrow>
     (\<forall>p<4.
        abs_generic
          (abi_list_ptr (sr_ready generated_scheduler_roots p)) =
        sa_ready (cs_abs c) p) \<and>
     abs_generic
       (abi_list_ptr (sr_delayed_a generated_scheduler_roots)) =
       sa_delayed_a (cs_abs c) \<and>
     abs_generic
       (abi_list_ptr (sr_delayed_b generated_scheduler_roots)) =
       sa_delayed_b (cs_abs c) \<and>
     abs_generic
       (abi_list_ptr (sr_suspended generated_scheduler_roots)) =
       sa_suspended (cs_abs c) \<and>
     abs_generic
       (abi_list_ptr Scheduler_V611_Parse.xTasksWaitingTermination_') =
       cs_termination c"

lemma GenericSchedulerViewEq_preserves_GenericSchedulerStateProjection:
  assumes view: "GenericSchedulerViewEq (cs_abs c) (cs_abs c')"
    and termination_frame: "cs_termination c' = cs_termination c"
    and projection: "GenericSchedulerStateProjection abs_generic c"
  shows "GenericSchedulerStateProjection abs_generic c'"
  using view termination_frame projection
  by (auto simp: GenericSchedulerViewEq_def
      GenericSchedulerStateProjection_def)

lemma environment_step_preserves_GenericSchedulerStateProjection:
  assumes step: "scheduler_environment_step K_E c c'"
    and projection: "GenericSchedulerStateProjection abs_generic c"
  shows "GenericSchedulerStateProjection abs_generic c'"
proof -
  have termination_frame: "cs_termination c' = cs_termination c"
    using environment_step_frames_task_domain[OF step] by simp
  show ?thesis
    by (rule GenericSchedulerViewEq_preserves_GenericSchedulerStateProjection[
          OF environment_step_preserves_generic_view[OF step]
             termination_frame projection])
qed

lemma environment_step_preserves_GenericRootFamilyCoverage:
  assumes step: "scheduler_environment_step K_E c c'"
    and coverage:
      "GenericRootFamilyCoverage
         D h GenericRootUniverse raw_generic abs_generic
         (cs_allocated c) K_G"
  shows
    "GenericRootFamilyCoverage
       D h GenericRootUniverse raw_generic abs_generic
       (cs_allocated c') K_G"
  using coverage environment_step_frames_task_domain[OF step]
  by simp

definition ConcurrentCutpointInterface ::
  "'tid scheduler_decode \<Rightarrow> heap_mem \<Rightarrow>
   xLIST_C ptr set \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow>
   ('tid \<Rightarrow> 32 word) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow>
   ('tid \<Rightarrow> 32 word) \<Rightarrow>
   'tid concurrent_scheduler_state \<Rightarrow> bool"
where
  "ConcurrentCutpointInterface
      D h external raw_event abs_event K_E raw_generic abs_generic K_G c
   \<longleftrightarrow>
     core_wf (cs_abs c) \<and>
     ConcurrentTaskDomainWF c \<and>
     TaskObservationRel D h (cs_abs c) \<and>
     AllocatedTaskObservationRel
       D h (cs_allocated c) (sa_priority (cs_abs c)) \<and>
     EventRootFamilyCoverage
       external D h raw_event abs_event (cs_allocated c) K_E \<and>
     EventSchedulerStateProjection external abs_event (cs_abs c) \<and>
     GenericRootFamilyCoverage
       D h GenericRootUniverse raw_generic abs_generic
       (cs_allocated c) K_G \<and>
     GenericSchedulerStateProjection abs_generic c \<and>
     concurrent_state_wf c"

lemma ConcurrentCutpointInterface_coreD:
  assumes
    "ConcurrentCutpointInterface
       D h external raw_event abs_event K_E raw_generic abs_generic K_G c"
  shows "core_wf (cs_abs c)"
  using assms by (simp add: ConcurrentCutpointInterface_def)

lemma ConcurrentCutpointInterface_observationD:
  assumes
    "ConcurrentCutpointInterface
       D h external raw_event abs_event K_E raw_generic abs_generic K_G c"
  shows "TaskObservationRel D h (cs_abs c)"
  using assms by (simp add: ConcurrentCutpointInterface_def)

lemma ConcurrentCutpointInterface_domainD:
  assumes
    "ConcurrentCutpointInterface
       D h external raw_event abs_event K_E raw_generic abs_generic K_G c"
  shows "ConcurrentTaskDomainWF c"
  using assms by (simp add: ConcurrentCutpointInterface_def)

lemma ConcurrentCutpointInterface_allocated_observationD:
  assumes
    "ConcurrentCutpointInterface
       D h external raw_event abs_event K_E raw_generic abs_generic K_G c"
  shows
    "AllocatedTaskObservationRel
       D h (cs_allocated c) (sa_priority (cs_abs c))"
  using assms by (simp add: ConcurrentCutpointInterface_def)

lemma ConcurrentCutpointInterface_event_coverageD:
  assumes
    "ConcurrentCutpointInterface
       D h external raw_event abs_event K_E raw_generic abs_generic K_G c"
  shows
    "EventRootFamilyCoverage
       external D h raw_event abs_event (cs_allocated c) K_E"
  using assms by (simp add: ConcurrentCutpointInterface_def)

lemma ConcurrentCutpointInterface_pendingD:
  assumes
    "ConcurrentCutpointInterface
       D h external raw_event abs_event K_E raw_generic abs_generic K_G c"
  shows "abs_event GeneratedPendingEventRoot = sa_pending (cs_abs c)"
  using assms
  by (simp add: ConcurrentCutpointInterface_def
      EventSchedulerStateProjection_def)

lemma ConcurrentCutpointInterface_event_waitingD:
  assumes
    "ConcurrentCutpointInterface
       D h external raw_event abs_event K_E raw_generic abs_generic K_G c"
  shows
    "event_family_waiting_tasks external abs_event =
       sa_event_waiting (cs_abs c)"
  using assms
  by (simp add: ConcurrentCutpointInterface_def
      EventSchedulerStateProjection_def)

lemma ConcurrentCutpointInterface_waiting_rootE:
  assumes cutpoint:
    "ConcurrentCutpointInterface
       D h external raw_event abs_event K_E raw_generic abs_generic K_G c"
    and waiting: "t \<in> sa_event_waiting (cs_abs c)"
  obtains lp where
    "lp \<in> external"
    "Event t \<in> set (ring (abs_event lp))"
proof -
  have
    "t \<in> event_family_waiting_tasks external abs_event"
    using waiting ConcurrentCutpointInterface_event_waitingD[OF cutpoint]
    by simp
  then obtain lp where
      root: "lp \<in> external"
    and member: "Event t \<in> set (ring (abs_event lp))"
    by (auto simp: event_family_waiting_tasks_def)
  show thesis by (rule that[OF root member])
qed

lemma ConcurrentCutpointInterface_generic_coverageD:
  assumes
    "ConcurrentCutpointInterface
       D h external raw_event abs_event K_E raw_generic abs_generic K_G c"
  shows
    "GenericRootFamilyCoverage
       D h GenericRootUniverse raw_generic abs_generic
       (cs_allocated c) K_G"
  using assms by (simp add: ConcurrentCutpointInterface_def)

lemma ConcurrentCutpointInterface_generic_projectionD:
  assumes
    "ConcurrentCutpointInterface
       D h external raw_event abs_event K_E raw_generic abs_generic K_G c"
  shows "GenericSchedulerStateProjection abs_generic c"
  using assms by (simp add: ConcurrentCutpointInterface_def)

lemma ConcurrentCutpointInterface_readyD:
  assumes cutpoint:
    "ConcurrentCutpointInterface
       D h external raw_event abs_event K_E raw_generic abs_generic K_G c"
    and priority: "p < 4"
  shows
    "abs_generic
       (abi_list_ptr (sr_ready generated_scheduler_roots p)) =
       sa_ready (cs_abs c) p"
  using ConcurrentCutpointInterface_generic_projectionD[OF cutpoint]
    priority
  by (auto simp: GenericSchedulerStateProjection_def)

lemma ConcurrentCutpointInterface_terminationD:
  assumes cutpoint:
    "ConcurrentCutpointInterface
       D h external raw_event abs_event K_E raw_generic abs_generic K_G c"
  shows
    "abs_generic
       (abi_list_ptr Scheduler_V611_Parse.xTasksWaitingTermination_') =
       cs_termination c"
  using ConcurrentCutpointInterface_generic_projectionD[OF cutpoint]
  by (simp add: GenericSchedulerStateProjection_def)

lemma ConcurrentCutpointInterface_state_wfD:
  assumes
    "ConcurrentCutpointInterface
       D h external raw_event abs_event K_E raw_generic abs_generic K_G c"
  shows "concurrent_state_wf c"
  using assms by (simp add: ConcurrentCutpointInterface_def)

text \<open>
  Generated-source connection points, all still open, are therefore:

    * task-context critical-entry/exit implements ProgEnterCritical and
      ProgExitCritical with the real port mask protocol;
    * vTaskSuspendAll implements ProgSuspendLinearise at arbitrary nesting
      depth;
    * ISR tick and switch requests during the scheduler-suspended window
      implement EnvTick/EnvYieldRequest; quiescent ISR semantics is a distinct
      source-connection theorem and is not hidden in this rely relation;
    * ISR resume moves an Event item from an arbitrary represented external
      Event root to pending-ready and implements EnvPendReady while framing its
      Generic item;
    * xTaskResumeAll's source-ordered pending drain and missed-tick replay
      implement ProgBeginResume, ProgResumeLinearise (ResumeRel), and
      ProgFinishResume;
    * each endpoint re-establishes ConcurrentCutpointInterface with the full
      Generic and Event root universes and both state projections;
    * creation, deletion, and reclamation must preserve cs_allocated and
      cs_termination in a separate lifecycle refinement before a
      whole-scheduler concurrency claim is possible.
\<close>

end
