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

definition resume_one_pending_abs ::
  "'tid \<Rightarrow> 'tid scheduler_abs \<Rightarrow> 'tid scheduler_abs"
where
  "resume_one_pending_abs t s =
     (let s0 = s\<lparr>
          sa_pending := list_remove_abs (Event t) (sa_pending s)\<rparr>;
          s1 = resume_remove_generic_abs t s0
      in add_ready_node (Generic t) s1)"

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
      resume_one_pending_abs_def resume_remove_generic_abs_def
      tick_unlocked_abs_def due_nodes_def remove_nodes_def
      add_ready_node.simps list_insert_end_abs_def
      list_insert_ordered_abs_def list_remove_abs_def empty_node_ring_def
      current_delayed_ring_def put_current_delayed_def Let_def)

end
