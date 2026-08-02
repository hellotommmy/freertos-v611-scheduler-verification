theory Scheduler_Resume_Pending_Drain_Phases
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Task_Observation_Rel.Scheduler_Task_Observation_Rel"
    "EAL6_FreeRTOS_V611_Scheduler_Event_Root_Family_Rel.Scheduler_Event_Root_Family_Rel"
    "EAL6_FreeRTOS_V611_Scheduler_Delay_Suspended_Core.Scheduler_Delay_Suspended_Core"
    "EAL6_FreeRTOS_V611_Scheduler_Insert_End_Translation_General.Scheduler_Insert_End_Translation_General"
begin

text \<open>
  Universal source-order scaffold for the pending-ready drain inside
  xTaskResumeAll.  The pending Event ring has arbitrary finite length.  Every
  task identity, priority, Generic owner root, ready root, payload, cursor,
  address and surrounding family is symbolic.

  At the public one-item boundary the operation is Event removal from the
  pending root, Generic removal from that task's delayed/suspended owner,
  insertion into its priority-ready root, and accumulation of top/yield
  obligations.  Internally, the FreeRTOS macro prvAddTaskToReadyQueue writes
  uxTopReadyPriority before calling vListInsertEnd.  The phases below retain
  that actual order:

    LoopHead -> EventUnlinked -> GenericUnlinked -> TopRaised
             -> ReadyInserted -> YieldChecked.

  This matters because TopRaised is a legal transient cutpoint at which the
  raised cache need not yet be witnessed by the ready ring.  The completed
  ReadyInserted/YieldChecked boundary has both effects.

  Missed-tick replay and the final (xYieldRequired || xMissedYield) branch are
  deliberately outside this theory.  No theorem here claims the complete
  xTaskResumeAll body.
\<close>

datatype resume_pending_phase =
    RP_LoopHead
  | RP_EventUnlinked
  | RP_GenericUnlinked
  | RP_TopRaised
  | RP_ReadyInserted
  | RP_YieldChecked

record ('tid, 'root) resume_pending_context =
  rpc_live :: "'tid set"
  rpc_tasks :: "'tid list"
  rpc_generic_roots :: "'root set"
  rpc_event_roots :: "'root set"
  rpc_pending_root :: 'root
  rpc_generic_owner :: "'tid \<Rightarrow> 'root"
  rpc_ready_root :: "nat \<Rightarrow> 'root"
  rpc_priority :: "'tid \<Rightarrow> nat"
  rpc_current_priority :: nat
  rpc_K_G :: "'tid \<Rightarrow> 32 word"
  rpc_K_E :: "'tid \<Rightarrow> 32 word"
  rpc_entry_top :: nat

record ('tid, 'root) resume_pending_snapshot =
  rps_generic_family :: "'root \<Rightarrow> 'tid node_ring"
  rps_event_family :: "'root \<Rightarrow> 'tid node_ring"
  rps_generic_payload :: "'tid \<Rightarrow> 32 word"
  rps_event_payload :: "'tid \<Rightarrow> 32 word"
  rps_top :: nat
  rps_local_yield :: bool

definition resume_pending_context_wf ::
  "('tid, 'root) resume_pending_context \<Rightarrow> bool"
where
  "resume_pending_context_wf C \<longleftrightarrow>
     finite (rpc_live C) \<and>
     finite (rpc_generic_roots C) \<and>
     finite (rpc_event_roots C) \<and>
     distinct (rpc_tasks C) \<and>
     set (rpc_tasks C) \<subseteq> rpc_live C \<and>
     rpc_pending_root C \<in> rpc_event_roots C \<and>
     rpc_current_priority C < 4 \<and>
     rpc_entry_top C < 4 \<and>
     (\<forall>t\<in>rpc_live C. rpc_priority C t < 4) \<and>
     (\<forall>t\<in>rpc_live C.
        rpc_ready_root C (rpc_priority C t) \<in> rpc_generic_roots C) \<and>
     (\<forall>t\<in>set (rpc_tasks C).
        rpc_generic_owner C t \<in> rpc_generic_roots C \<and>
        (\<forall>u\<in>rpc_live C.
           rpc_generic_owner C t \<noteq>
             rpc_ready_root C (rpc_priority C u)))"

definition resume_pending_owner_roots ::
  "('tid, 'root) resume_pending_context \<Rightarrow> 'root set"
where
  "resume_pending_owner_roots C =
     rpc_generic_owner C ` set (rpc_tasks C)"

definition resume_pending_ready_roots ::
  "('tid, 'root) resume_pending_context \<Rightarrow> 'root set"
where
  "resume_pending_ready_roots C =
     rpc_ready_root C ` (rpc_priority C ` rpc_live C)"

lemma resume_pending_context_owner_roots:
  assumes wf: "resume_pending_context_wf C"
  shows
    "finite (resume_pending_owner_roots C) \<and>
     resume_pending_owner_roots C \<subseteq> rpc_generic_roots C"
  using wf
  by (auto simp: resume_pending_context_wf_def
      resume_pending_owner_roots_def)

lemma resume_pending_context_owner_ready_disjoint:
  assumes wf: "resume_pending_context_wf C"
  shows
    "resume_pending_owner_roots C \<inter>
       resume_pending_ready_roots C = {}"
  using wf
  by (auto simp: resume_pending_context_wf_def
      resume_pending_owner_roots_def resume_pending_ready_roots_def)

definition resume_pending_family_shape ::
  "('tid, 'root) resume_pending_context \<Rightarrow>
   ('tid, 'root) resume_pending_snapshot \<Rightarrow> bool"
where
  "resume_pending_family_shape C S \<longleftrightarrow>
     (\<forall>g\<in>rpc_generic_roots C.
        xlist_wf (rps_generic_family S g) \<and>
        generic_ring (rps_generic_family S g) \<and>
        set (ring (rps_generic_family S g)) \<subseteq>
          Generic ` rpc_live C) \<and>
     (\<forall>e\<in>rpc_event_roots C.
        xlist_wf (rps_event_family S e) \<and>
        event_ring (rps_event_family S e) \<and>
        set (ring (rps_event_family S e)) \<subseteq>
          Event ` rpc_live C) \<and>
     (\<forall>g\<in>rpc_generic_roots C. \<forall>g'\<in>rpc_generic_roots C.
        g \<noteq> g' \<longrightarrow>
        set (ring (rps_generic_family S g)) \<inter>
          set (ring (rps_generic_family S g')) = {}) \<and>
     (\<forall>e\<in>rpc_event_roots C. \<forall>e'\<in>rpc_event_roots C.
        e \<noteq> e' \<longrightarrow>
        set (ring (rps_event_family S e)) \<inter>
          set (ring (rps_event_family S e')) = {}) \<and>
     (\<forall>g\<in>rpc_generic_roots C. \<forall>t\<in>rpc_live C.
        Generic t \<in> set (ring (rps_generic_family S g)) \<longrightarrow>
        item_key (rps_generic_family S g) (Generic t) = rpc_K_G C t) \<and>
     (\<forall>e\<in>rpc_event_roots C. \<forall>t\<in>rpc_live C.
        Event t \<in> set (ring (rps_event_family S e)) \<longrightarrow>
        item_key (rps_event_family S e) (Event t) = rpc_K_E C t) \<and>
     (\<forall>t\<in>rpc_live C.
        rps_generic_payload S t = rpc_K_G C t \<and>
        rps_event_payload S t = rpc_K_E C t)"

definition resume_pending_entry_rel ::
  "('tid, 'root) resume_pending_context \<Rightarrow>
   ('tid, 'root) resume_pending_snapshot \<Rightarrow> bool"
where
  "resume_pending_entry_rel C S \<longleftrightarrow>
     resume_pending_context_wf C \<and>
     resume_pending_family_shape C S \<and>
     ring (rps_event_family S (rpc_pending_root C)) =
       map Event (rpc_tasks C) \<and>
     (\<forall>t\<in>set (rpc_tasks C).
        Generic t \<in>
          set (ring (rps_generic_family S (rpc_generic_owner C t))) \<and>
        (\<forall>g\<in>rpc_generic_roots C.
           Generic t \<in> set (ring (rps_generic_family S g)) \<longleftrightarrow>
             g = rpc_generic_owner C t) \<and>
        item_key (rps_generic_family S (rpc_generic_owner C t))
          (Generic t) = rpc_K_G C t) \<and>
     rps_top S = rpc_entry_top C \<and>
     \<not> rps_local_yield S"

definition resume_pending_event_unlink_state ::
  "('tid, 'root) resume_pending_context \<Rightarrow> 'tid \<Rightarrow>
   ('tid, 'root) resume_pending_snapshot \<Rightarrow>
   ('tid, 'root) resume_pending_snapshot"
where
  "resume_pending_event_unlink_state C t S =
     S\<lparr>rps_event_family :=
       (rps_event_family S)
         (rpc_pending_root C :=
           list_remove_abs (Event t)
             (rps_event_family S (rpc_pending_root C)))\<rparr>"

definition resume_pending_generic_unlink_state ::
  "('tid, 'root) resume_pending_context \<Rightarrow> 'tid \<Rightarrow>
   ('tid, 'root) resume_pending_snapshot \<Rightarrow>
   ('tid, 'root) resume_pending_snapshot"
where
  "resume_pending_generic_unlink_state C t S =
     S\<lparr>rps_generic_family :=
       (rps_generic_family S)
         (rpc_generic_owner C t :=
           list_remove_abs (Generic t)
             (rps_generic_family S (rpc_generic_owner C t)))\<rparr>"

definition resume_pending_raise_top_state ::
  "('tid, 'root) resume_pending_context \<Rightarrow> 'tid \<Rightarrow>
   ('tid, 'root) resume_pending_snapshot \<Rightarrow>
   ('tid, 'root) resume_pending_snapshot"
where
  "resume_pending_raise_top_state C t S =
     S\<lparr>rps_top := max (rps_top S) (rpc_priority C t)\<rparr>"

definition resume_pending_ready_insert_state ::
  "('tid, 'root) resume_pending_context \<Rightarrow> 'tid \<Rightarrow>
   ('tid, 'root) resume_pending_snapshot \<Rightarrow>
   ('tid, 'root) resume_pending_snapshot"
where
  "resume_pending_ready_insert_state C t S =
     (let target = rpc_ready_root C (rpc_priority C t)
      in S\<lparr>rps_generic_family :=
           (rps_generic_family S)
             (target := list_insert_end_abs (Generic t) (rpc_K_G C t)
               (rps_generic_family S target))\<rparr>)"

definition resume_pending_yield_check_state ::
  "('tid, 'root) resume_pending_context \<Rightarrow> 'tid \<Rightarrow>
   ('tid, 'root) resume_pending_snapshot \<Rightarrow>
   ('tid, 'root) resume_pending_snapshot"
where
  "resume_pending_yield_check_state C t S =
     S\<lparr>rps_local_yield :=
       rps_local_yield S \<or>
         rpc_current_priority C \<le> rpc_priority C t\<rparr>"

definition resume_pending_complete_one ::
  "('tid, 'root) resume_pending_context \<Rightarrow> 'tid \<Rightarrow>
   ('tid, 'root) resume_pending_snapshot \<Rightarrow>
   ('tid, 'root) resume_pending_snapshot"
where
  "resume_pending_complete_one C t S =
     resume_pending_yield_check_state C t
       (resume_pending_ready_insert_state C t
         (resume_pending_raise_top_state C t
           (resume_pending_generic_unlink_state C t
             (resume_pending_event_unlink_state C t S))))"

fun resume_pending_process_prefix ::
  "('tid, 'root) resume_pending_context \<Rightarrow> 'tid list \<Rightarrow>
   ('tid, 'root) resume_pending_snapshot \<Rightarrow>
   ('tid, 'root) resume_pending_snapshot"
where
  "resume_pending_process_prefix C [] S = S"
| "resume_pending_process_prefix C (t # ts) S =
     resume_pending_process_prefix C ts
       (resume_pending_complete_one C t S)"

fun resume_pending_top_after ::
  "('tid, 'root) resume_pending_context \<Rightarrow> 'tid list \<Rightarrow>
   nat \<Rightarrow> nat"
where
  "resume_pending_top_after C [] n = n"
| "resume_pending_top_after C (t # ts) n =
     resume_pending_top_after C ts (max n (rpc_priority C t))"

fun resume_pending_snapshot_at ::
  "('tid, 'root) resume_pending_context \<Rightarrow> 'tid \<Rightarrow>
   resume_pending_phase \<Rightarrow>
   ('tid, 'root) resume_pending_snapshot \<Rightarrow>
   ('tid, 'root) resume_pending_snapshot"
where
  "resume_pending_snapshot_at C t RP_LoopHead S = S"
| "resume_pending_snapshot_at C t RP_EventUnlinked S =
     resume_pending_event_unlink_state C t S"
| "resume_pending_snapshot_at C t RP_GenericUnlinked S =
     resume_pending_generic_unlink_state C t
       (resume_pending_event_unlink_state C t S)"
| "resume_pending_snapshot_at C t RP_TopRaised S =
     resume_pending_raise_top_state C t
       (resume_pending_generic_unlink_state C t
         (resume_pending_event_unlink_state C t S))"
| "resume_pending_snapshot_at C t RP_ReadyInserted S =
     resume_pending_ready_insert_state C t
       (resume_pending_raise_top_state C t
         (resume_pending_generic_unlink_state C t
           (resume_pending_event_unlink_state C t S)))"
| "resume_pending_snapshot_at C t RP_YieldChecked S =
     resume_pending_complete_one C t S"

fun resume_pending_visible_tasks ::
  "resume_pending_phase \<Rightarrow> 'tid list \<Rightarrow> 'tid list"
where
  "resume_pending_visible_tasks RP_LoopHead todo = todo"
| "resume_pending_visible_tasks RP_EventUnlinked todo = tl todo"
| "resume_pending_visible_tasks RP_GenericUnlinked todo = tl todo"
| "resume_pending_visible_tasks RP_TopRaised todo = tl todo"
| "resume_pending_visible_tasks RP_ReadyInserted todo = tl todo"
| "resume_pending_visible_tasks RP_YieldChecked todo = tl todo"

definition resume_pending_loop_phase_inv ::
  "('tid, 'root) resume_pending_context \<Rightarrow>
   ('tid, 'root) resume_pending_snapshot \<Rightarrow>
   'tid list \<Rightarrow> 'tid list \<Rightarrow> resume_pending_phase \<Rightarrow>
   ('tid, 'root) resume_pending_snapshot \<Rightarrow> bool"
where
  "resume_pending_loop_phase_inv C entry processed todo phase current \<longleftrightarrow>
     resume_pending_entry_rel C entry \<and>
     rpc_tasks C = processed @ todo \<and>
     distinct (processed @ todo) \<and>
     (todo = [] \<longrightarrow> phase = RP_LoopHead) \<and>
     current =
       (case todo of
          [] \<Rightarrow> resume_pending_process_prefix C processed entry
        | t # rest \<Rightarrow>
            resume_pending_snapshot_at C t phase
              (resume_pending_process_prefix C processed entry)) \<and>
     ring (rps_event_family current (rpc_pending_root C)) =
       map Event (resume_pending_visible_tasks phase todo)"

definition resume_pending_loop_measure :: "'tid list \<Rightarrow> nat"
where
  "resume_pending_loop_measure todo = length todo"

definition resume_pending_outer_head_bridge ::
  "'tid scheduler_abs \<Rightarrow>
   ('tid, 'root) resume_pending_context \<Rightarrow>
   ('tid, 'root) resume_pending_snapshot \<Rightarrow>
   'tid list \<Rightarrow> 'tid list \<Rightarrow>
   ('tid, 'root) resume_pending_snapshot \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> bool"
where
  "resume_pending_outer_head_bridge
      base C entry processed todo current abstract_current \<longleftrightarrow>
     resume_pending_loop_phase_inv C entry processed todo RP_LoopHead current \<and>
     resume_pending_loop_inv base (map Event processed) (map Event todo)
       (rps_local_yield current) abstract_current"

inductive resume_pending_phase_step ::
  "resume_pending_phase \<Rightarrow> resume_pending_phase \<Rightarrow> bool"
where
  RP_step_event:
    "resume_pending_phase_step RP_LoopHead RP_EventUnlinked"
| RP_step_generic:
    "resume_pending_phase_step RP_EventUnlinked RP_GenericUnlinked"
| RP_step_top:
    "resume_pending_phase_step RP_GenericUnlinked RP_TopRaised"
| RP_step_ready:
    "resume_pending_phase_step RP_TopRaised RP_ReadyInserted"
| RP_step_yield:
    "resume_pending_phase_step RP_ReadyInserted RP_YieldChecked"

lemma resume_pending_process_prefix_append:
  "resume_pending_process_prefix C (xs @ ys) s =
   resume_pending_process_prefix C ys
     (resume_pending_process_prefix C xs s)"
  by (induction xs arbitrary: s) simp_all

lemma resume_pending_complete_one_is_yield_cut:
  "resume_pending_snapshot_at C t RP_YieldChecked S =
   resume_pending_complete_one C t S"
  by simp

lemma resume_pending_process_prefix_payload_frame:
  "rps_generic_payload (resume_pending_process_prefix C processed s) =
     rps_generic_payload s \<and>
   rps_event_payload (resume_pending_process_prefix C processed s) =
     rps_event_payload s"
proof (induction processed arbitrary: s)
  case Nil
  show ?case by simp
next
  case (Cons t ts)
  show ?case
    using Cons.IH[of "resume_pending_complete_one C t s"]
    by (simp add: resume_pending_complete_one_def
        resume_pending_event_unlink_state_def
        resume_pending_generic_unlink_state_def
        resume_pending_raise_top_state_def
        resume_pending_ready_insert_state_def
        resume_pending_yield_check_state_def Let_def)
qed

lemma resume_pending_process_prefix_top:
  "rps_top (resume_pending_process_prefix C processed s) =
   resume_pending_top_after C processed (rps_top s)"
proof (induction processed arbitrary: s)
  case Nil
  show ?case by simp
next
  case (Cons t ts)
  show ?case
    using Cons.IH[of "resume_pending_complete_one C t s"]
    by (simp add: resume_pending_complete_one_def
        resume_pending_event_unlink_state_def
        resume_pending_generic_unlink_state_def
        resume_pending_raise_top_state_def
        resume_pending_ready_insert_state_def
        resume_pending_yield_check_state_def Let_def)
qed

lemma resume_pending_event_unlink_ring:
  "ring (rps_event_family (resume_pending_event_unlink_state C t S)
      (rpc_pending_root C)) =
   remove1 (Event t)
     (ring (rps_event_family S (rpc_pending_root C)))"
  by (simp add: resume_pending_event_unlink_state_def list_remove_abs_def)

lemma resume_pending_complete_one_event_ring:
  "ring (rps_event_family (resume_pending_complete_one C t S)
      (rpc_pending_root C)) =
   remove1 (Event t)
     (ring (rps_event_family S (rpc_pending_root C)))"
  by (simp add: resume_pending_complete_one_def
      resume_pending_event_unlink_state_def
      resume_pending_generic_unlink_state_def
      resume_pending_raise_top_state_def
      resume_pending_ready_insert_state_def
      resume_pending_yield_check_state_def list_remove_abs_def Let_def)

lemma resume_pending_process_prefix_pending_ring:
  assumes ring:
    "ring (rps_event_family s (rpc_pending_root C)) =
       map Event (processed @ todo)"
    and distinct: "distinct (processed @ todo)"
  shows
    "ring (rps_event_family
       (resume_pending_process_prefix C processed s) (rpc_pending_root C)) =
       map Event todo"
  using ring distinct
proof (induction processed arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons t processed)
  have first:
    "ring (rps_event_family
       (resume_pending_complete_one C t s) (rpc_pending_root C)) =
       map Event (processed @ todo)"
    using Cons.prems
    by (simp add: resume_pending_complete_one_event_ring)
  have rest_distinct: "distinct (processed @ todo)"
    using Cons.prems by simp
  show ?case
    using Cons.IH[OF first rest_distinct] by simp
qed

lemma resume_pending_loop_phase_inv_initial:
  assumes entry: "resume_pending_entry_rel C S"
  shows
    "resume_pending_loop_phase_inv C S [] (rpc_tasks C)
       RP_LoopHead S"
proof -
  from entry have entry_context: "resume_pending_context_wf C"
    unfolding resume_pending_entry_rel_def
    by (elim conjE) assumption
  from entry have entry_family: "resume_pending_family_shape C S"
    unfolding resume_pending_entry_rel_def
    by (elim conjE) assumption
  from entry have entry_pending:
    "ring (rps_event_family S (rpc_pending_root C)) =
       map Event (rpc_tasks C)"
    unfolding resume_pending_entry_rel_def
    by (elim conjE) assumption
  from entry_context have tasks_distinct: "distinct (rpc_tasks C)"
    unfolding resume_pending_context_wf_def
    by (elim conjE) assumption

  have task_split: "rpc_tasks C = [] @ rpc_tasks C"
    by (simp only: append.simps(1))
  have empty_phase:
    "rpc_tasks C = [] \<longrightarrow> RP_LoopHead = RP_LoopHead"
    by (intro impI, rule refl)
  have fold_base: "resume_pending_process_prefix C [] S = S"
    by (rule resume_pending_process_prefix.simps(1))
  have loop_head_base:
    "\<And>t. resume_pending_snapshot_at C t RP_LoopHead S = S"
    by (rule resume_pending_snapshot_at.simps(1))
  have current_cases:
    "S =
      (case rpc_tasks C of
         [] \<Rightarrow> resume_pending_process_prefix C [] S
       | t # rest \<Rightarrow>
           resume_pending_snapshot_at C t RP_LoopHead
             (resume_pending_process_prefix C [] S))"
  proof (cases "rpc_tasks C")
    case Nil
    show ?thesis
      by (simp only: Nil fold_base list.case)
  next
    case (Cons t rest)
    show ?thesis
      by (simp only: Cons fold_base loop_head_base list.case)
  qed

  show ?thesis
    unfolding resume_pending_loop_phase_inv_def
  proof (intro conjI)
    show "resume_pending_entry_rel C S"
      by (rule entry)
    show "rpc_tasks C = [] @ rpc_tasks C"
      by (rule task_split)
    show "distinct ([] @ rpc_tasks C)"
      using tasks_distinct by (simp only: append.simps(1))
    show "rpc_tasks C = [] \<longrightarrow> RP_LoopHead = RP_LoopHead"
      by (rule empty_phase)
    show
      "S =
        (case rpc_tasks C of
           [] \<Rightarrow> resume_pending_process_prefix C [] S
         | t # rest \<Rightarrow>
             resume_pending_snapshot_at C t RP_LoopHead
               (resume_pending_process_prefix C [] S))"
      by (rule current_cases)
    show
      "ring (rps_event_family S (rpc_pending_root C)) =
         map Event
           (resume_pending_visible_tasks RP_LoopHead (rpc_tasks C))"
      using entry_pending
      by (simp only: resume_pending_visible_tasks.simps(1))
  qed
qed

lemma resume_pending_loop_phase_inv_event_step:
  assumes inv:
    "resume_pending_loop_phase_inv C entry processed (t # rest)
       RP_LoopHead current"
  shows
    "resume_pending_loop_phase_inv C entry processed (t # rest)
       RP_EventUnlinked (resume_pending_event_unlink_state C t current)"
  using inv
  by (auto simp: resume_pending_loop_phase_inv_def
      resume_pending_event_unlink_state_def list_remove_abs_def)

lemma resume_pending_loop_phase_inv_generic_step:
  assumes inv:
    "resume_pending_loop_phase_inv C entry processed (t # rest)
       RP_EventUnlinked current"
  shows
    "resume_pending_loop_phase_inv C entry processed (t # rest)
       RP_GenericUnlinked (resume_pending_generic_unlink_state C t current)"
  using inv
  by (auto simp: resume_pending_loop_phase_inv_def
      resume_pending_event_unlink_state_def
      resume_pending_generic_unlink_state_def list_remove_abs_def)

lemma resume_pending_loop_phase_inv_top_step:
  assumes inv:
    "resume_pending_loop_phase_inv C entry processed (t # rest)
       RP_GenericUnlinked current"
  shows
    "resume_pending_loop_phase_inv C entry processed (t # rest)
       RP_TopRaised (resume_pending_raise_top_state C t current)"
  using inv
  by (auto simp: resume_pending_loop_phase_inv_def
      resume_pending_event_unlink_state_def
      resume_pending_generic_unlink_state_def
      resume_pending_raise_top_state_def list_remove_abs_def)

lemma resume_pending_loop_phase_inv_ready_step:
  assumes inv:
    "resume_pending_loop_phase_inv C entry processed (t # rest)
       RP_TopRaised current"
  shows
    "resume_pending_loop_phase_inv C entry processed (t # rest)
       RP_ReadyInserted (resume_pending_ready_insert_state C t current)"
  using inv
  by (auto simp: resume_pending_loop_phase_inv_def
      resume_pending_event_unlink_state_def
      resume_pending_generic_unlink_state_def
      resume_pending_raise_top_state_def
      resume_pending_ready_insert_state_def list_remove_abs_def Let_def)

lemma resume_pending_loop_phase_inv_yield_step:
  assumes inv:
    "resume_pending_loop_phase_inv C entry processed (t # rest)
       RP_ReadyInserted current"
  shows
    "resume_pending_loop_phase_inv C entry processed (t # rest)
       RP_YieldChecked (resume_pending_yield_check_state C t current)"
proof -
  let ?base = "resume_pending_process_prefix C processed entry"

  have event_state:
    "resume_pending_snapshot_at C t RP_EventUnlinked ?base =
       resume_pending_event_unlink_state C t ?base"
    by (rule resume_pending_snapshot_at.simps(2))
  have generic_state:
    "resume_pending_snapshot_at C t RP_GenericUnlinked ?base =
       resume_pending_generic_unlink_state C t
         (resume_pending_snapshot_at C t RP_EventUnlinked ?base)"
    by (simp only: resume_pending_snapshot_at.simps event_state)
  have top_state:
    "resume_pending_snapshot_at C t RP_TopRaised ?base =
       resume_pending_raise_top_state C t
         (resume_pending_snapshot_at C t RP_GenericUnlinked ?base)"
    by (simp only: resume_pending_snapshot_at.simps
        event_state generic_state)
  have ready_state:
    "resume_pending_snapshot_at C t RP_ReadyInserted ?base =
       resume_pending_ready_insert_state C t
         (resume_pending_snapshot_at C t RP_TopRaised ?base)"
    by (simp only: resume_pending_snapshot_at.simps
        event_state generic_state top_state)
  have yield_state:
    "resume_pending_yield_check_state C t
       (resume_pending_snapshot_at C t RP_ReadyInserted ?base) =
     resume_pending_snapshot_at C t RP_YieldChecked ?base"
    by (simp only: resume_pending_snapshot_at.simps
        resume_pending_complete_one_def event_state generic_state
        top_state ready_state)

  from inv have entry_fact: "resume_pending_entry_rel C entry"
    unfolding resume_pending_loop_phase_inv_def
    by (elim conjE) assumption
  from inv have tasks_fact: "rpc_tasks C = processed @ (t # rest)"
    unfolding resume_pending_loop_phase_inv_def
    by (elim conjE) assumption
  from inv have distinct_fact: "distinct (processed @ (t # rest))"
    unfolding resume_pending_loop_phase_inv_def
    by (elim conjE) assumption
  from inv have current_case:
    "current =
      (case t # rest of
         [] \<Rightarrow> resume_pending_process_prefix C processed entry
       | u # us \<Rightarrow>
           resume_pending_snapshot_at C u RP_ReadyInserted
             (resume_pending_process_prefix C processed entry))"
    unfolding resume_pending_loop_phase_inv_def
    by (elim conjE) assumption
  from inv have pending_case:
    "ring (rps_event_family current (rpc_pending_root C)) =
       map Event
         (resume_pending_visible_tasks RP_ReadyInserted (t # rest))"
    unfolding resume_pending_loop_phase_inv_def
    by (elim conjE) assumption

  have current_ready:
    "current = resume_pending_snapshot_at C t RP_ReadyInserted ?base"
    using current_case by (simp only: list.case)
  have post_current:
    "resume_pending_yield_check_state C t current =
       resume_pending_snapshot_at C t RP_YieldChecked ?base"
  proof -
    have current_cong:
      "resume_pending_yield_check_state C t current =
       resume_pending_yield_check_state C t
         (resume_pending_snapshot_at C t RP_ReadyInserted ?base)"
      by (rule arg_cong[OF current_ready])
    show ?thesis
      using current_cong yield_state by (rule trans)
  qed
  have visible_same:
    "resume_pending_visible_tasks RP_ReadyInserted (t # rest) =
       resume_pending_visible_tasks RP_YieldChecked (t # rest)"
    by (simp only: resume_pending_visible_tasks.simps)
  have event_frame:
    "rps_event_family (resume_pending_yield_check_state C t current) =
       rps_event_family current"
    by (cases current)
      (simp only: resume_pending_yield_check_state_def
        resume_pending_snapshot.select_convs
        resume_pending_snapshot.update_convs)
  have ring_frame:
    "ring (rps_event_family
       (resume_pending_yield_check_state C t current)
       (rpc_pending_root C)) =
     ring (rps_event_family current (rpc_pending_root C))"
    by (rule arg_cong[OF event_frame])
  have post_pending:
    "ring (rps_event_family
       (resume_pending_yield_check_state C t current)
       (rpc_pending_root C)) =
     map Event
       (resume_pending_visible_tasks RP_YieldChecked (t # rest))"
  proof -
    have visible_cong:
      "map Event
         (resume_pending_visible_tasks RP_ReadyInserted (t # rest)) =
       map Event
         (resume_pending_visible_tasks RP_YieldChecked (t # rest))"
      by (rule arg_cong[OF visible_same])
    have frame_then_pending:
      "ring (rps_event_family
         (resume_pending_yield_check_state C t current)
         (rpc_pending_root C)) =
       map Event
         (resume_pending_visible_tasks RP_ReadyInserted (t # rest))"
      using ring_frame pending_case by (rule trans)
    show ?thesis
      using frame_then_pending visible_cong by (rule trans)
  qed

  show ?thesis
    unfolding resume_pending_loop_phase_inv_def
  proof (intro conjI)
    show "resume_pending_entry_rel C entry"
      by (rule entry_fact)
    show "rpc_tasks C = processed @ (t # rest)"
      by (rule tasks_fact)
    show "distinct (processed @ (t # rest))"
      by (rule distinct_fact)
    show "t # rest = [] \<longrightarrow> RP_YieldChecked = RP_LoopHead"
    proof
      assume impossible: "t # rest = []"
      have reverse: "[] = t # rest"
        by (rule sym[OF impossible])
      have nil_ne_cons: "[] \<noteq> t # rest"
        by (rule list.distinct(1))
      from nil_ne_cons reverse have False
        by contradiction
      then show "RP_YieldChecked = RP_LoopHead"
        by (rule FalseE)
    qed
    show
      "resume_pending_yield_check_state C t current =
        (case t # rest of
           [] \<Rightarrow> resume_pending_process_prefix C processed entry
         | u # us \<Rightarrow>
             resume_pending_snapshot_at C u RP_YieldChecked
               (resume_pending_process_prefix C processed entry))"
      using post_current by (simp only: list.case)
    show
      "ring (rps_event_family
         (resume_pending_yield_check_state C t current)
         (rpc_pending_root C)) =
       map Event
         (resume_pending_visible_tasks RP_YieldChecked (t # rest))"
      by (rule post_pending)
  qed
qed

lemma resume_pending_loop_phase_inv_source_step:
  assumes step: "resume_pending_phase_step phase next"
    and inv:
      "resume_pending_loop_phase_inv C entry processed (t # rest)
         phase current"
  obtains next_current where
    "resume_pending_loop_phase_inv C entry processed (t # rest)
       next next_current"
proof -
  from step inv that show thesis
    apply cases
    subgoal
      by (hypsubst;
          blast intro: resume_pending_loop_phase_inv_event_step)
    subgoal
      by (hypsubst;
          blast intro: resume_pending_loop_phase_inv_generic_step)
    subgoal
      by (hypsubst;
          blast intro: resume_pending_loop_phase_inv_top_step)
    subgoal
      by (hypsubst;
          blast intro: resume_pending_loop_phase_inv_ready_step)
    subgoal
      by (hypsubst;
          blast intro: resume_pending_loop_phase_inv_yield_step)
    done
qed

lemma resume_pending_loop_phase_inv_deterministic:
  assumes left:
      "resume_pending_loop_phase_inv C entry processed todo phase left"
    and right:
      "resume_pending_loop_phase_inv C entry processed todo phase right"
  shows "left = right"
  using left right by (auto simp: resume_pending_loop_phase_inv_def)

lemma resume_pending_loop_phase_inv_commit:
  assumes inv:
    "resume_pending_loop_phase_inv C entry processed (t # rest)
       RP_YieldChecked current"
  shows
    "resume_pending_loop_phase_inv C entry (processed @ [t]) rest
       RP_LoopHead current"
proof -
  from inv have entry: "resume_pending_entry_rel C entry"
    unfolding resume_pending_loop_phase_inv_def by blast
  from inv have tasks: "rpc_tasks C = processed @ (t # rest)"
    unfolding resume_pending_loop_phase_inv_def by blast
  from inv have distinct: "distinct (processed @ (t # rest))"
    unfolding resume_pending_loop_phase_inv_def by blast
  from inv have current_case:
    "current =
      (case t # rest of
         [] \<Rightarrow> resume_pending_process_prefix C processed entry
       | u # us \<Rightarrow>
           resume_pending_snapshot_at C u RP_YieldChecked
             (resume_pending_process_prefix C processed entry))"
    unfolding resume_pending_loop_phase_inv_def by blast
  have current:
    "current = resume_pending_complete_one C t
       (resume_pending_process_prefix C processed entry)"
    using current_case
    by (simp only: list.case resume_pending_snapshot_at.simps)
  from inv have pending_case:
    "ring (rps_event_family current (rpc_pending_root C)) =
       map Event
         (resume_pending_visible_tasks RP_YieldChecked (t # rest))"
    unfolding resume_pending_loop_phase_inv_def by blast
  have tl_cons: "tl (t # rest) = rest"
    by simp
  have pending:
    "ring (rps_event_family current (rpc_pending_root C)) =
       map Event rest"
    using pending_case
    by (simp only: resume_pending_visible_tasks.simps tl_cons)

  have next_state:
    "resume_pending_process_prefix C (processed @ [t]) entry = current"
  proof -
    have append:
      "resume_pending_process_prefix C (processed @ [t]) entry =
       resume_pending_process_prefix C [t]
         (resume_pending_process_prefix C processed entry)"
      by (rule resume_pending_process_prefix_append)
    have singleton:
      "resume_pending_process_prefix C [t]
         (resume_pending_process_prefix C processed entry) =
       resume_pending_complete_one C t
         (resume_pending_process_prefix C processed entry)"
      by (simp only: resume_pending_process_prefix.simps)
    show ?thesis
    proof (rule trans)
      show
        "resume_pending_process_prefix C (processed @ [t]) entry =
         resume_pending_process_prefix C [t]
           (resume_pending_process_prefix C processed entry)"
        by (rule append)
      show
        "resume_pending_process_prefix C [t]
           (resume_pending_process_prefix C processed entry) = current"
      proof (rule trans)
        show
          "resume_pending_process_prefix C [t]
             (resume_pending_process_prefix C processed entry) =
           resume_pending_complete_one C t
             (resume_pending_process_prefix C processed entry)"
          by (rule singleton)
        show
          "resume_pending_complete_one C t
             (resume_pending_process_prefix C processed entry) = current"
          by (rule current[symmetric])
      qed
    qed
  qed
  have tasks_next:
    "rpc_tasks C = (processed @ [t]) @ rest"
    using tasks by (simp only: append_assoc append.simps)
  have distinct_next: "distinct ((processed @ [t]) @ rest)"
    using distinct by (simp only: append_assoc append.simps)
  have empty_phase:
    "rest = [] \<longrightarrow> RP_LoopHead = RP_LoopHead"
    by (intro impI, rule refl)
  have loop_head_current:
    "current =
      (case rest of
         [] \<Rightarrow>
           resume_pending_process_prefix C (processed @ [t]) entry
       | u # us \<Rightarrow>
           resume_pending_snapshot_at C u RP_LoopHead
             (resume_pending_process_prefix C (processed @ [t]) entry))"
  proof (cases rest)
    case Nil
    show ?thesis
      using next_state by (simp only: Nil list.case)
  next
    case (Cons u us)
    show ?thesis
      using next_state
      by (simp only: Cons list.case resume_pending_snapshot_at.simps)
  qed
  have pending_next:
    "ring (rps_event_family current (rpc_pending_root C)) =
       map Event (resume_pending_visible_tasks RP_LoopHead rest)"
    using pending
    by (simp only: resume_pending_visible_tasks.simps(1))

  show ?thesis
    unfolding resume_pending_loop_phase_inv_def
  proof (intro conjI)
    show "resume_pending_entry_rel C entry"
      by (rule entry)
    show "rpc_tasks C = (processed @ [t]) @ rest"
      by (rule tasks_next)
    show "distinct ((processed @ [t]) @ rest)"
      by (rule distinct_next)
    show "rest = [] \<longrightarrow> RP_LoopHead = RP_LoopHead"
      by (rule empty_phase)
    show
      "current =
        (case rest of
           [] \<Rightarrow>
             resume_pending_process_prefix C (processed @ [t]) entry
         | u # us \<Rightarrow>
             resume_pending_snapshot_at C u RP_LoopHead
               (resume_pending_process_prefix C (processed @ [t]) entry))"
      by (rule loop_head_current)
    show
      "ring (rps_event_family current (rpc_pending_root C)) =
       map Event (resume_pending_visible_tasks RP_LoopHead rest)"
      by (rule pending_next)
  qed
qed

lemma resume_pending_loop_measure_commit:
  "resume_pending_loop_measure rest <
   resume_pending_loop_measure (t # rest)"
  by (simp add: resume_pending_loop_measure_def)

lemma resume_pending_outer_head_bridge_pending_agree:
  assumes bridge:
    "resume_pending_outer_head_bridge
       base C entry processed todo current abstract_current"
  shows
    "ring (rps_event_family current (rpc_pending_root C)) =
       ring (sa_pending abstract_current)"
  using bridge
  by (auto simp: resume_pending_outer_head_bridge_def
      resume_pending_loop_phase_inv_def resume_pending_loop_inv_def)

lemma resume_pending_complete_one_local_yield:
  "rps_local_yield (resume_pending_complete_one C t s) \<longleftrightarrow>
   rps_local_yield s \<or>
     rpc_current_priority C \<le> rpc_priority C t"
  by (cases s)
    (simp only: resume_pending_complete_one_def
      resume_pending_event_unlink_state_def
      resume_pending_generic_unlink_state_def
      resume_pending_raise_top_state_def
      resume_pending_ready_insert_state_def
      resume_pending_yield_check_state_def Let_def
      resume_pending_snapshot.select_convs
      resume_pending_snapshot.update_convs)

lemma resume_pending_process_prefix_local_yield:
  "rps_local_yield (resume_pending_process_prefix C processed s) \<longleftrightarrow>
   rps_local_yield s \<or>
     (\<exists>t\<in>set processed.
        rpc_current_priority C \<le> rpc_priority C t)"
proof (induction processed arbitrary: s)
  case Nil
  show ?case
    by (simp only: resume_pending_process_prefix.simps
        list.set bex_simps simp_thms)
next
  case (Cons t ts)
  have tail:
    "rps_local_yield
       (resume_pending_process_prefix C ts
         (resume_pending_complete_one C t s)) \<longleftrightarrow>
     rps_local_yield (resume_pending_complete_one C t s) \<or>
       (\<exists>u\<in>set ts.
          rpc_current_priority C \<le> rpc_priority C u)"
    by (rule Cons.IH)
  have head:
    "rps_local_yield (resume_pending_complete_one C t s) \<longleftrightarrow>
     rps_local_yield s \<or>
       rpc_current_priority C \<le> rpc_priority C t"
    by (rule resume_pending_complete_one_local_yield)
  show ?case
    using tail head
    by (simp only: resume_pending_process_prefix.simps
        list.set bex_simps simp_thms disj_assoc)
qed

end
