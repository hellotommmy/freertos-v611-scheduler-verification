theory Scheduler_Universal_Delay_Arithmetic
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Abstract_Model.Scheduler_Abstract_Model"
begin

text \<open>
  Universal pure semantics for the positive-delay branch.  No tick, delay,
  task identity, priority, ring, or list length is fixed.  The only delayed
  list branch is the source-derived unsigned-word test wake < current tick.
\<close>

definition positive_delay_state ::
  "32 word \<Rightarrow> 'tid \<Rightarrow> 'tid scheduler_abs \<Rightarrow>
   'tid scheduler_abs"
where
  "positive_delay_state ticks t s =
     request_yield (block_task_at (sa_tick s + ticks) t s)"

lemma task_delay_abs_positive_current:
  assumes ticks: "ticks \<noteq> 0"
    and current: "sa_current s = Some t"
  shows "task_delay_abs ticks s = positive_delay_state ticks t s"
  using ticks current
  by (simp add: task_delay_abs_def positive_delay_state_def)

lemma task_delay_abs_positive_no_current:
  assumes ticks: "ticks \<noteq> 0"
    and current: "sa_current s = None"
  shows "task_delay_abs ticks s = request_yield s"
  using ticks current by (simp add: task_delay_abs_def)

lemma positive_delay_state_wake:
  "sa_wake (positive_delay_state ticks t s) t =
     Some (sa_tick s + ticks)"
  by (simp add: positive_delay_state_def request_yield_def
      block_task_at_def put_current_delayed_def put_overflow_delayed_def
      Let_def split: if_splits)

lemma positive_delay_state_other_wake:
  assumes other: "u \<noteq> t"
  shows
    "sa_wake (positive_delay_state ticks t s) u = sa_wake s u"
  using other
  by (simp add: positive_delay_state_def request_yield_def
      block_task_at_def put_current_delayed_def put_overflow_delayed_def
      Let_def split: if_splits)

lemma positive_delay_state_ready_at_priority:
  "sa_ready (positive_delay_state ticks t s) (sa_priority s t) =
     list_remove_abs (Generic t) (sa_ready s (sa_priority s t))"
  by (simp add: positive_delay_state_def request_yield_def
      block_task_at_def put_current_delayed_def put_overflow_delayed_def
      Let_def split: if_splits)

lemma positive_delay_state_other_ready:
  assumes other: "p \<noteq> sa_priority s t"
  shows "sa_ready (positive_delay_state ticks t s) p = sa_ready s p"
  using other
  by (simp add: positive_delay_state_def request_yield_def
      block_task_at_def put_current_delayed_def put_overflow_delayed_def
      Let_def split: if_splits)

lemma positive_delay_state_ready_ring:
  "ring (sa_ready (positive_delay_state ticks t s) (sa_priority s t)) =
     remove1 (Generic t) (ring (sa_ready s (sa_priority s t)))"
  by (simp add: positive_delay_state_ready_at_priority list_remove_abs_def)

lemma positive_delay_state_delayed_branch:
  "let wake = sa_tick s + ticks
   in if wake < sa_tick s
     then
       overflow_delayed_ring (positive_delay_state ticks t s) =
         list_insert_ordered_abs (Generic t) wake
           (overflow_delayed_ring s) \<and>
       current_delayed_ring (positive_delay_state ticks t s) =
         current_delayed_ring s
     else
       current_delayed_ring (positive_delay_state ticks t s) =
         list_insert_ordered_abs (Generic t) wake
           (current_delayed_ring s) \<and>
       overflow_delayed_ring (positive_delay_state ticks t s) =
         overflow_delayed_ring s"
  by (cases "sa_current_role_a s")
     (simp_all add: positive_delay_state_def request_yield_def
       block_task_at_def current_delayed_ring_def overflow_delayed_ring_def
       put_current_delayed_def put_overflow_delayed_def Let_def)

lemma positive_delay_state_frames:
  "sa_live (positive_delay_state ticks t s) = sa_live s \<and>
   sa_priority (positive_delay_state ticks t s) = sa_priority s \<and>
   sa_event_waiting (positive_delay_state ticks t s) = sa_event_waiting s \<and>
   sa_current_role_a (positive_delay_state ticks t s) =
     sa_current_role_a s \<and>
   sa_pending (positive_delay_state ticks t s) = sa_pending s \<and>
   sa_suspended (positive_delay_state ticks t s) = sa_suspended s \<and>
   sa_tick (positive_delay_state ticks t s) = sa_tick s \<and>
   sa_missed_ticks (positive_delay_state ticks t s) = sa_missed_ticks s \<and>
   sa_suspend_depth (positive_delay_state ticks t s) = sa_suspend_depth s \<and>
   sa_missed_yield (positive_delay_state ticks t s) = sa_missed_yield s \<and>
   sa_top_ready (positive_delay_state ticks t s) = sa_top_ready s \<and>
   sa_current (positive_delay_state ticks t s) = sa_current s \<and>
   sa_overflows (positive_delay_state ticks t s) = sa_overflows s \<and>
   sa_yield_count (positive_delay_state ticks t s) =
     Suc (sa_yield_count s)"
  by (simp add: positive_delay_state_def request_yield_def
      block_task_at_def put_current_delayed_def put_overflow_delayed_def
      Let_def split: if_splits)

theorem task_delay_abs_positive_universal_effects:
  assumes ticks: "ticks \<noteq> 0"
    and current: "sa_current s = Some t"
  defines "wake \<equiv> sa_tick s + ticks"
  shows
    "task_delay_abs ticks s = positive_delay_state ticks t s \<and>
     sa_wake (task_delay_abs ticks s) t = Some wake \<and>
     (\<forall>u. u \<noteq> t \<longrightarrow>
        sa_wake (task_delay_abs ticks s) u = sa_wake s u) \<and>
     sa_ready (task_delay_abs ticks s) (sa_priority s t) =
       list_remove_abs (Generic t) (sa_ready s (sa_priority s t)) \<and>
     (\<forall>p. p \<noteq> sa_priority s t \<longrightarrow>
        sa_ready (task_delay_abs ticks s) p = sa_ready s p) \<and>
     (if wake < sa_tick s
      then
        overflow_delayed_ring (task_delay_abs ticks s) =
          list_insert_ordered_abs (Generic t) wake
            (overflow_delayed_ring s) \<and>
        current_delayed_ring (task_delay_abs ticks s) =
          current_delayed_ring s
      else
        current_delayed_ring (task_delay_abs ticks s) =
          list_insert_ordered_abs (Generic t) wake
            (current_delayed_ring s) \<and>
        overflow_delayed_ring (task_delay_abs ticks s) =
          overflow_delayed_ring s) \<and>
     sa_current (task_delay_abs ticks s) = Some t \<and>
     sa_tick (task_delay_abs ticks s) = sa_tick s \<and>
     sa_yield_count (task_delay_abs ticks s) = Suc (sa_yield_count s)"
proof -
  show ?thesis
    using ticks current
    by (cases "sa_current_role_a s")
       (simp_all add: task_delay_abs_def positive_delay_state_def
         request_yield_def block_task_at_def current_delayed_ring_def
         overflow_delayed_ring_def put_current_delayed_def
         put_overflow_delayed_def wake_def Let_def split: if_splits)
qed

theorem task_delay_abs_all_inputs_capstone:
  "task_delay_abs ticks s =
     (if ticks = 0
      then request_yield s
      else case sa_current s of
        None \<Rightarrow> request_yield s
      | Some t \<Rightarrow> positive_delay_state ticks t s) \<and>
   (ticks = 0 \<longrightarrow> task_delay_abs ticks s = request_yield s) \<and>
   (ticks \<noteq> 0 \<and> sa_current s = None \<longrightarrow>
      task_delay_abs ticks s = request_yield s) \<and>
   (\<forall>t. ticks \<noteq> 0 \<and> sa_current s = Some t \<longrightarrow>
      task_delay_abs ticks s = positive_delay_state ticks t s) \<and>
   sa_current (task_delay_abs ticks s) = sa_current s \<and>
   sa_tick (task_delay_abs ticks s) = sa_tick s \<and>
   sa_yield_count (task_delay_abs ticks s) = Suc (sa_yield_count s)"
  by (cases "ticks = 0"; cases "sa_current s")
     (simp_all add: task_delay_abs_def positive_delay_state_def
       request_yield_def block_task_at_def put_current_delayed_def
       put_overflow_delayed_def Let_def split: if_splits)

end
