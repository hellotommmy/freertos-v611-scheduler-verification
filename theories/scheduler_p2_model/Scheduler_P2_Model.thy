theory Scheduler_P2_Model
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Abstract_Model.Scheduler_Abstract_Model"
begin

text \<open>
  Closed pure witness for the trace-driven P2 boundary.  This theory contains
  no generated C state: its purpose is to check the proposed abstract endpoint
  before a concrete TCB/list decoder and footprint are introduced.
\<close>

datatype p2_tid = P2_IDLE | P2_RUN

fun p2_priority :: "p2_tid \<Rightarrow> nat" where
  "p2_priority P2_IDLE = 0"
| "p2_priority P2_RUN = 2"

definition p2_idle_ready :: "p2_tid node_ring" where
  "p2_idle_ready =
     list_insert_end_abs (Generic P2_IDLE) 0 empty_node_ring"

definition p2_run_ready :: "p2_tid node_ring" where
  "p2_run_ready =
     list_insert_end_abs (Generic P2_RUN) 0 empty_node_ring"

definition p2_run_delayed :: "p2_tid node_ring" where
  "p2_run_delayed =
     list_insert_ordered_abs (Generic P2_RUN) 7 empty_node_ring"

definition p2_pre :: "p2_tid scheduler_abs" where
  "p2_pre =
     \<lparr>
       sa_live = {P2_IDLE, P2_RUN},
       sa_priority = p2_priority,
       sa_wake = (\<lambda>_. None),
       sa_event_waiting = {},
       sa_ready =
         (\<lambda>p. if p = 0 then p2_idle_ready
              else if p = 2 then p2_run_ready
              else empty_node_ring),
       sa_delayed_a = empty_node_ring,
       sa_delayed_b = empty_node_ring,
       sa_current_role_a = True,
       sa_pending = empty_node_ring,
       sa_suspended = empty_node_ring,
       sa_tick = 5,
       sa_missed_ticks = 0,
       sa_suspend_depth = 0,
       sa_missed_yield = False,
       sa_top_ready = 2,
       sa_current = Some P2_RUN,
       sa_overflows = 0,
       sa_yield_count = 0
     \<rparr>"

definition p2_post :: "p2_tid scheduler_abs" where
  "p2_post =
     \<lparr>
       sa_live = {P2_IDLE, P2_RUN},
       sa_priority = p2_priority,
       sa_wake = (\<lambda>t. if t = P2_RUN then Some 7 else None),
       sa_event_waiting = {},
       sa_ready =
         (\<lambda>p. if p = 0 then p2_idle_ready else empty_node_ring),
       sa_delayed_a = p2_run_delayed,
       sa_delayed_b = empty_node_ring,
       sa_current_role_a = True,
       sa_pending = empty_node_ring,
       sa_suspended = empty_node_ring,
       sa_tick = 5,
       sa_missed_ticks = 0,
       sa_suspend_depth = 0,
       sa_missed_yield = False,
       sa_top_ready = 2,
       sa_current = Some P2_RUN,
       sa_overflows = 0,
       sa_yield_count = 1
     \<rparr>"

lemma p2_ready_fields[simp]:
  "ring p2_idle_ready = [Generic P2_IDLE] \<and>
   cursor p2_idle_ready = Some (Generic P2_IDLE) \<and>
   ring p2_run_ready = [Generic P2_RUN] \<and>
   cursor p2_run_ready = Some (Generic P2_RUN)"
  by (simp add: p2_idle_ready_def p2_run_ready_def empty_node_ring_def
      list_insert_end_abs_def)

lemma p2_delayed_fields[simp]:
  "ring p2_run_delayed = [Generic P2_RUN] \<and>
   cursor p2_run_delayed = None \<and>
   item_key p2_run_delayed (Generic P2_RUN) = 7"
  by (simp add: p2_run_delayed_def empty_node_ring_def
      list_insert_ordered_abs_def Let_def)

theorem task_delay_abs_2_p2:
  "task_delay_abs 2 p2_pre = p2_post"
  by (simp add: task_delay_abs_def p2_pre_def p2_post_def
      block_task_at_def request_yield_def p2_run_ready_def
      p2_run_delayed_def empty_node_ring_def list_remove_abs_def
      list_insert_end_abs_def list_insert_ordered_abs_def
      current_delayed_ring_def put_current_delayed_def Let_def fun_eq_iff)

lemma p2_pre_settled:
  "settled_wf p2_pre"
  apply (auto simp: settled_wf_def core_wf_def ring_shape_wf_def
      role_wf_def membership_wf_def time_wf_def ready_cache_wf_def
      current_wf_def generic_ring_def event_ring_def tail_cursor_wf_def
      ready_task_set_def generic_task_set_def event_task_set_def
      delayed_key_agrees_def current_delayed_ring_def
      overflow_delayed_ring_def p2_pre_def p2_idle_ready_def
      p2_run_ready_def empty_node_ring_def list_insert_end_abs_def
      xlist_wf_def Let_def)
  subgoal for t p by (cases t) auto
  subgoal by (rule bexI[where x=0]) simp_all
  subgoal by (rule bexI[where x=2]) simp_all
  done

lemma p2_post_core:
  "core_wf p2_post"
  apply (auto simp: core_wf_def ring_shape_wf_def role_wf_def
      membership_wf_def time_wf_def ready_cache_wf_def current_wf_def
      generic_ring_def event_ring_def tail_cursor_wf_def
      ready_task_set_def generic_task_set_def event_task_set_def
      delayed_key_agrees_def current_delayed_ring_def
      overflow_delayed_ring_def p2_post_def p2_idle_ready_def
      p2_run_delayed_def empty_node_ring_def list_insert_end_abs_def
      list_insert_ordered_abs_def xlist_wf_def Let_def)
  subgoal for t p by (cases t) auto
  subgoal
    apply (erule_tac x=0 in ballE)
     apply simp_all
    done
  done

lemma p2_post_phase_observations:
  "sa_tick p2_post = 5 \<and>
   sa_current p2_post = Some P2_RUN \<and>
   sa_top_ready p2_post = 2 \<and>
   ring (sa_ready p2_post 2) = [] \<and>
   ring (current_delayed_ring p2_post) = [Generic P2_RUN] \<and>
   sa_wake p2_post P2_RUN = Some 7 \<and>
   sa_yield_count p2_post = 1"
  by (simp add: p2_post_def current_delayed_ring_def p2_run_delayed_def
      empty_node_ring_def list_insert_ordered_abs_def Let_def)

lemma p2_post_not_settled:
  "\<not> settled_wf p2_post"
  by (simp add: settled_wf_def p2_post_def empty_node_ring_def)

end
