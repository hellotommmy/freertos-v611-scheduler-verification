theory Scheduler_Resume_General_Relation
  imports
    "EAL6_FreeRTOS_V611_Scheduler_P2_Control_Leaves.Scheduler_P2_Control_Leaves"
    "EAL6_FreeRTOS_V611_Scheduler_Delay_Zero_Refinement.Scheduler_V611_Delay_Zero_Refinement"
begin

text \<open>
  A source-ordered abstract contract for xTaskResumeAll.  All task identities,
  rings, priorities and missed-tick counts remain quantified.  The concrete
  two-task state near the end is only a discovery witness showing that pending
  draining and missed-tick replay do not commute; it is not an acceptance
  theorem and occurs in no premise of the general resume relation below.
\<close>

definition resume_remove_generic_abs ::
  "'tid \<Rightarrow> 'tid scheduler_abs \<Rightarrow> 'tid scheduler_abs"
where
  "resume_remove_generic_abs t s =
     s\<lparr>
       sa_delayed_a := list_remove_abs (Generic t) (sa_delayed_a s),
       sa_delayed_b := list_remove_abs (Generic t) (sa_delayed_b s),
       sa_suspended := list_remove_abs (Generic t) (sa_suspended s)
     \<rparr>"

text \<open>
  A pending-ready task still owns its Generic item through exactly one of the
  two physical delayed rings or the suspended ring.  Its C xItemValue is a
  persistent item payload: vListRemove and vListInsertEnd do not rewrite it.
  In particular, a genuinely suspended task may retain a nonzero value from
  an earlier delay.  The total selector below therefore reads the value from
  the physical source ring before any removal; it deliberately does not infer
  a default value from @{const sa_wake}.

  The delayed-ring tests are physical A then physical B, independent of the
  current/overflow role pointers.  Under @{const core_wf}, pending ownership
  makes exactly one of those tests or the suspended fallback applicable.
\<close>

definition pending_generic_key_abs ::
  "'tid \<Rightarrow> 'tid scheduler_abs \<Rightarrow> 32 word"
where
  "pending_generic_key_abs t s =
     (if Generic t \<in> set (ring (sa_delayed_a s))
      then item_key (sa_delayed_a s) (Generic t)
      else if Generic t \<in> set (ring (sa_delayed_b s))
      then item_key (sa_delayed_b s) (Generic t)
      else item_key (sa_suspended s) (Generic t))"

definition resume_add_ready_with_key_abs ::
  "'tid \<Rightarrow> 32 word \<Rightarrow> 'tid scheduler_abs \<Rightarrow>
   'tid scheduler_abs"
where
  "resume_add_ready_with_key_abs t k s =
     (let p = sa_priority s t;
          q = sa_ready s p
      in s\<lparr>
           sa_ready := (sa_ready s)
             (p := list_insert_end_abs (Generic t) k q),
           sa_wake := (sa_wake s)(t := None),
           sa_event_waiting := sa_event_waiting s - {t},
           sa_top_ready := max (sa_top_ready s) p
         \<rparr>)"

definition resume_one_pending_abs ::
  "'tid \<Rightarrow> 'tid scheduler_abs \<Rightarrow> 'tid scheduler_abs"
where
  "resume_one_pending_abs t s =
     (let k = pending_generic_key_abs t s;
          s0 = s\<lparr>
           sa_pending := list_remove_abs (Event t) (sa_pending s)\<rparr>;
           s1 = resume_remove_generic_abs t s0
      in resume_add_ready_with_key_abs t k s1)"

lemma pending_generic_key_abs_delayed_a:
  assumes owned:
    "Generic t \<in> set (ring (sa_delayed_a s))"
  shows
    "pending_generic_key_abs t s =
       item_key (sa_delayed_a s) (Generic t)"
  using owned by (simp add: pending_generic_key_abs_def)

lemma pending_generic_key_abs_delayed_b:
  assumes not_a:
      "Generic t \<notin> set (ring (sa_delayed_a s))"
    and owned:
      "Generic t \<in> set (ring (sa_delayed_b s))"
  shows
    "pending_generic_key_abs t s =
       item_key (sa_delayed_b s) (Generic t)"
  using not_a owned by (simp add: pending_generic_key_abs_def)

lemma pending_generic_key_abs_suspended:
  assumes not_a:
      "Generic t \<notin> set (ring (sa_delayed_a s))"
    and not_b:
      "Generic t \<notin> set (ring (sa_delayed_b s))"
  shows
    "pending_generic_key_abs t s =
       item_key (sa_suspended s) (Generic t)"
  using not_a not_b by (simp add: pending_generic_key_abs_def)

lemma core_wf_pending_generic_key_has_physical_source:
  assumes wf: "core_wf s"
    and pending: "Event t \<in> set (ring (sa_pending s))"
  shows
    "(Generic t \<in> set (ring (sa_delayed_a s)) \<and>
       pending_generic_key_abs t s =
         item_key (sa_delayed_a s) (Generic t)) \<or>
     (Generic t \<in> set (ring (sa_delayed_b s)) \<and>
       pending_generic_key_abs t s =
         item_key (sa_delayed_b s) (Generic t)) \<or>
     (Generic t \<in> set (ring (sa_suspended s)) \<and>
       pending_generic_key_abs t s =
         item_key (sa_suspended s) (Generic t))"
proof -
  have located:
    "Generic t \<in> set (ring (sa_delayed_a s)) \<or>
     Generic t \<in> set (ring (sa_delayed_b s)) \<or>
     Generic t \<in> set (ring (sa_suspended s))"
    using wf pending
    by (auto simp: core_wf_def membership_wf_def event_task_set_def
        generic_task_set_def Let_def)
  show ?thesis
    using located by (auto simp: pending_generic_key_abs_def)
qed

lemma resume_add_ready_with_key_abs_ready_key:
  "item_key
     (sa_ready (resume_add_ready_with_key_abs t k s) (sa_priority s t))
     (Generic t) = k"
  by (simp add: resume_add_ready_with_key_abs_def
      list_insert_end_abs_def Let_def)

lemma resume_one_pending_abs_preserves_captured_generic_key:
  "item_key
     (sa_ready (resume_one_pending_abs t s) (sa_priority s t))
     (Generic t) = pending_generic_key_abs t s"
  by (simp add: resume_one_pending_abs_def resume_remove_generic_abs_def
      resume_add_ready_with_key_abs_def list_insert_end_abs_def Let_def)

corollary core_wf_resume_one_pending_abs_preserves_physical_source_key:
  assumes wf: "core_wf s"
    and pending: "Event t \<in> set (ring (sa_pending s))"
  shows
    "(Generic t \<in> set (ring (sa_delayed_a s)) \<and>
       item_key
         (sa_ready (resume_one_pending_abs t s) (sa_priority s t))
         (Generic t) = item_key (sa_delayed_a s) (Generic t)) \<or>
     (Generic t \<in> set (ring (sa_delayed_b s)) \<and>
       item_key
         (sa_ready (resume_one_pending_abs t s) (sa_priority s t))
         (Generic t) = item_key (sa_delayed_b s) (Generic t)) \<or>
     (Generic t \<in> set (ring (sa_suspended s)) \<and>
       item_key
         (sa_ready (resume_one_pending_abs t s) (sa_priority s t))
         (Generic t) = item_key (sa_suspended s) (Generic t))"
proof -
  have source:
    "(Generic t \<in> set (ring (sa_delayed_a s)) \<and>
       pending_generic_key_abs t s =
         item_key (sa_delayed_a s) (Generic t)) \<or>
     (Generic t \<in> set (ring (sa_delayed_b s)) \<and>
       pending_generic_key_abs t s =
         item_key (sa_delayed_b s) (Generic t)) \<or>
     (Generic t \<in> set (ring (sa_suspended s)) \<and>
       pending_generic_key_abs t s =
         item_key (sa_suspended s) (Generic t))"
    by (rule core_wf_pending_generic_key_has_physical_source[OF wf pending])
  have ready:
    "item_key
       (sa_ready (resume_one_pending_abs t s) (sa_priority s t))
       (Generic t) = pending_generic_key_abs t s"
    by (rule resume_one_pending_abs_preserves_captured_generic_key)
  from source show ?thesis
  proof
    assume delayed_a:
      "Generic t \<in> set (ring (sa_delayed_a s)) \<and>
       pending_generic_key_abs t s =
         item_key (sa_delayed_a s) (Generic t)"
    then show ?thesis using ready by auto
  next
    assume delayed_b_or_suspended:
      "(Generic t \<in> set (ring (sa_delayed_b s)) \<and>
        pending_generic_key_abs t s =
          item_key (sa_delayed_b s) (Generic t)) \<or>
       (Generic t \<in> set (ring (sa_suspended s)) \<and>
        pending_generic_key_abs t s =
          item_key (sa_suspended s) (Generic t))"
    then show ?thesis
    proof
      assume delayed_b:
        "Generic t \<in> set (ring (sa_delayed_b s)) \<and>
         pending_generic_key_abs t s =
           item_key (sa_delayed_b s) (Generic t)"
      then show ?thesis using ready by auto
    next
      assume suspended:
        "Generic t \<in> set (ring (sa_suspended s)) \<and>
         pending_generic_key_abs t s =
           item_key (sa_suspended s) (Generic t)"
      then show ?thesis using ready by auto
    qed
  qed
qed

fun drain_pending_nodes_abs ::
  "'tid node_kind list \<Rightarrow> 'tid scheduler_abs \<Rightarrow>
   'tid scheduler_abs"
where
  "drain_pending_nodes_abs [] s = s"
| "drain_pending_nodes_abs (Event t # ns) s =
     drain_pending_nodes_abs ns (resume_one_pending_abs t s)"
| "drain_pending_nodes_abs (Generic t # ns) s =
     drain_pending_nodes_abs ns s"

definition drain_pending_abs ::
  "'tid scheduler_abs \<Rightarrow> 'tid scheduler_abs"
where
  "drain_pending_abs s =
     drain_pending_nodes_abs (ring (sa_pending s)) s"

text \<open>
  The generated source calls vTaskIncrementTick before decrementing the missed
  count.  With the proof configuration's tick hook disabled, one replay step
  is therefore exactly unlocked-tick followed by setting the remaining count.
\<close>

fun replay_missed_abs ::
  "nat \<Rightarrow> 'tid scheduler_abs \<Rightarrow> 'tid scheduler_abs"
where
  "replay_missed_abs 0 s = s"
| "replay_missed_abs (Suc n) s =
     replay_missed_abs n
       ((tick_unlocked_abs s)\<lparr>sa_missed_ticks := n\<rparr>)"

definition resume_pending_requires_yield ::
  "'tid scheduler_abs \<Rightarrow> bool"
where
  "resume_pending_requires_yield s \<longleftrightarrow>
     (\<exists>t. Event t \<in> set (ring (sa_pending s)) \<and>
        (case sa_current s of
           None \<Rightarrow> False
         | Some current \<Rightarrow>
             sa_priority s current \<le> sa_priority s t))"

definition resume_yield_required ::
  "'tid scheduler_abs \<Rightarrow> bool"
where
  "resume_yield_required s \<longleftrightarrow>
     resume_pending_requires_yield s \<or>
     sa_missed_ticks s > 0 \<or>
     sa_missed_yield s"

definition YieldAbs ::
  "bool \<Rightarrow> 'tid scheduler_abs \<Rightarrow> bool \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> bool"
where
  "YieldAbs requested s yielded t \<longleftrightarrow>
     (if requested
      then yielded \<and> t = request_yield s
      else \<not> yielded \<and> t = s)"

definition ResumeRel ::
  "'tid scheduler_abs \<Rightarrow> bool \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> bool"
where
  "ResumeRel s yielded t \<longleftrightarrow>
     sa_suspend_depth s > 0 \<and>
     (let s0 = s\<lparr>sa_suspend_depth := sa_suspend_depth s - 1\<rparr>
      in if sa_suspend_depth s0 \<noteq> 0 \<or> sa_live s0 = {}
         then \<not> yielded \<and> t = s0
         else
           let requested = resume_yield_required s0;
               s1 = drain_pending_abs s0;
               s2 = replay_missed_abs (sa_missed_ticks s1) s1;
               caller_state =
                 (if requested
                  then s2\<lparr>sa_missed_yield := False\<rparr>
                  else s2)
           in YieldAbs requested caller_state yielded t)"

lemma YieldAbs_false [simp]:
  "YieldAbs False s yielded t \<longleftrightarrow> (\<not> yielded \<and> t = s)"
  by (simp add: YieldAbs_def)

lemma YieldAbs_true [simp]:
  "YieldAbs True s yielded t \<longleftrightarrow>
   (yielded \<and> t = request_yield s)"
  by (simp add: YieldAbs_def)

lemma drain_pending_abs_empty [simp]:
  assumes "ring (sa_pending s) = []"
  shows "drain_pending_abs s = s"
  using assms by (simp add: drain_pending_abs_def)

lemma replay_missed_abs_clears_count:
  "sa_missed_ticks (replay_missed_abs n
      (s\<lparr>sa_missed_ticks := n\<rparr>)) = 0"
proof (induction n arbitrary: s)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case
    by (simp add: tick_unlocked_abs_def Let_def
        swap_delayed_roles_def put_current_delayed_def)
qed

text \<open>
  The proof-port yield helper is a real generated source theorem.  This bridge
  connects its exact state to the true branch of @{const YieldAbs} and to the
  existing modular concrete/abstract yield-counter relation.  It deliberately
  says nothing about the caller's preceding xMissedYield clear.
\<close>

theorem scheduler_eal6_port_yield_refines_YieldAbs_true:
  assumes counter:
    "yield_count_mod_rel
       (Scheduler_V611_Parse.globals.eal6_port_yield_count_' c)
       (sa_yield_count a)"
  shows
    "Scheduler_V611_Delay_Translation.eal6_port_yield' \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       YieldAbs True a True (request_yield a) \<and>
       yield_count_mod_rel
         (Scheduler_V611_Parse.globals.eal6_port_yield_count_' t)
         (sa_yield_count (request_yield a))
     \<rbrace>"
proof -
  note source = scheduler_eal6_port_yield_exact[where c=c]
  note count = yield_count_mod_rel_request[OF counter]
  show ?thesis
    apply (rule runs_to_weaken[OF source])
    using count
    by (auto simp: YieldAbs_def request_yield_def p2_yield_state_def)
qed

definition resume_interference_example :: "nat scheduler_abs"
where
  "resume_interference_example =
     \<lparr>
       sa_live = {0, 1},
       sa_priority = (\<lambda>_. 0),
       sa_wake = (\<lambda>t. if t = 0 then Some 1 else None),
       sa_event_waiting = {},
       sa_ready = (\<lambda>p.
         if p = 0
         then list_insert_end_abs (Generic 1) 0 empty_node_ring
         else empty_node_ring),
       sa_delayed_a =
         list_insert_ordered_abs (Generic 0) 1 empty_node_ring,
       sa_delayed_b = empty_node_ring,
       sa_current_role_a = True,
       sa_pending =
         list_insert_end_abs (Event 0) 0 empty_node_ring,
       sa_suspended = empty_node_ring,
       sa_tick = 0,
       sa_missed_ticks = 1,
       sa_suspend_depth = 0,
       sa_missed_yield = False,
       sa_top_ready = 0,
       sa_current = Some 1,
       sa_overflows = 0,
       sa_yield_count = 0
     \<rparr>"

lemma resume_discovery_drain_and_replay_do_not_commute:
  "ring (sa_ready
      (replay_missed_abs 1
        (drain_pending_abs resume_interference_example)) 0) \<noteq>
   ring (sa_ready
      (drain_pending_abs
        (replay_missed_abs 1 resume_interference_example)) 0)"
  by (simp add: resume_interference_example_def drain_pending_abs_def
      resume_one_pending_abs_def pending_generic_key_abs_def
      resume_remove_generic_abs_def resume_add_ready_with_key_abs_def
      tick_unlocked_abs_def due_nodes_def remove_nodes_def
      add_ready_node.simps list_insert_end_abs_def
      list_insert_ordered_abs_def list_remove_abs_def empty_node_ring_def
      current_delayed_ring_def put_current_delayed_def Let_def)

end
