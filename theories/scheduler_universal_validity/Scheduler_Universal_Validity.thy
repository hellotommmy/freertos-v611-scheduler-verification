theory Scheduler_Universal_Validity
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Abstract_Model.Scheduler_Abstract_Model"
begin

text \<open>
  Universal abstract validity bricks for the frozen four-priority scheduler
  model.  None of the results below fixes the live-task set, a priority
  assignment, a tick, a delay, or a ready-list length.

  The tempting statement that delaying the current task preserves every ready
  member is false without a distinctness premise: if the current task is the
  only member of its ready ring, list removal makes that ring empty.  The first
  lemma records this definition-shaped counterexample.  The surviving theorem
  says exactly that blocking one task preserves every different ready task.
\<close>

lemma remove_only_ready_member_counterexample:
  "ring
     (list_remove_abs (Generic t)
       (list_insert_end_abs (Generic t) k empty_node_ring)) = []"
  by (simp add: list_remove_abs_def list_insert_end_abs_def
      empty_node_ring_def)

lemma list_remove_abs_preserves_distinct_member:
  assumes member: "y \<in> set (ring q)"
      and distinct: "y \<noteq> x"
  shows "y \<in> set (ring (list_remove_abs x q))"
  using member distinct
  by (simp add: list_remove_abs_def)

lemma block_task_at_preserves_other_ready_member:
  assumes member:
      "Generic other \<in> set (ring (sa_ready s p))"
      and distinct: "other \<noteq> current"
  shows
    "Generic other \<in>
       set (ring (sa_ready (block_task_at wake current s) p))"
proof (cases "sa_priority s current = p")
  case True
  then show ?thesis
    using member distinct
    by (simp add: block_task_at_def Let_def
        put_current_delayed_def put_overflow_delayed_def
        list_remove_abs_def)
next
  case False
  then show ?thesis
    using member
    by (simp add: block_task_at_def Let_def
        put_current_delayed_def put_overflow_delayed_def)
qed

theorem task_delay_abs_preserves_other_ready_member:
  assumes current: "sa_current s = Some current"
      and member:
        "Generic other \<in> set (ring (sa_ready s p))"
      and distinct: "other \<noteq> current"
  shows
    "Generic other \<in>
       set (ring (sa_ready (task_delay_abs ticks s) p))"
proof (cases "ticks = 0")
  case True
  then show ?thesis
    using member
    by (simp add: task_delay_abs_def request_yield_def)
next
  case False
  then show ?thesis
    using current
      block_task_at_preserves_other_ready_member[OF member distinct]
    by (simp add: task_delay_abs_def request_yield_def)
qed

theorem task_delay_abs_some_ready_task_remains:
  assumes current: "sa_current s = Some current"
      and other_ready:
        "Generic other \<in> set (ring (sa_ready s p))"
      and priority_bound: "p < 4"
      and distinct: "other \<noteq> current"
  shows
    "\<exists>q<4. \<exists>t.
       Generic t \<in>
         set (ring (sa_ready (task_delay_abs ticks s) q))"
proof -
  have other_preserved:
    "Generic other \<in>
       set (ring (sa_ready (task_delay_abs ticks s) p))"
    by (rule task_delay_abs_preserves_other_ready_member[
          OF current other_ready distinct])
  show ?thesis
  proof (rule exI[where x = p], intro conjI)
    show "p < 4"
      by (rule priority_bound)
    show "\<exists>t.
        Generic t \<in>
          set (ring (sa_ready (task_delay_abs ticks s) p))"
      using other_preserved by blast
  qed
qed

corollary task_delay_abs_positive_preserves_idle_ready:
  assumes positive: "ticks \<noteq> 0"
      and current: "sa_current s = Some current"
      and idle_ready:
        "Generic idle \<in> set (ring (sa_ready s 0))"
      and idle_distinct: "idle \<noteq> current"
  shows
    "Generic idle \<in>
       set (ring (sa_ready (task_delay_abs ticks s) 0))"
  using task_delay_abs_preserves_other_ready_member[
      OF current idle_ready idle_distinct, of ticks]
  by simp

corollary task_delay_abs_positive_ready_zero_nonempty:
  assumes positive: "ticks \<noteq> 0"
      and current: "sa_current s = Some current"
      and idle_ready:
        "Generic idle \<in> set (ring (sa_ready s 0))"
      and idle_distinct: "idle \<noteq> current"
  shows
    "ring (sa_ready (task_delay_abs ticks s) 0) \<noteq> []"
  using task_delay_abs_positive_preserves_idle_ready[
      OF positive current idle_ready idle_distinct]
  by auto

theorem task_delay_abs_positive_some_ready_task_remains:
  assumes positive: "ticks \<noteq> 0"
      and current: "sa_current s = Some current"
      and idle_ready:
        "Generic idle \<in> set (ring (sa_ready s 0))"
      and idle_distinct: "idle \<noteq> current"
  shows
    "\<exists>p<4. \<exists>t.
       Generic t \<in>
         set (ring (sa_ready (task_delay_abs ticks s) p))"
proof -
  have idle_preserved:
    "Generic idle \<in>
       set (ring (sa_ready (task_delay_abs ticks s) 0))"
    by (rule task_delay_abs_positive_preserves_idle_ready[
          OF positive current idle_ready idle_distinct])
  show ?thesis
  proof (rule exI[where x = 0], intro conjI)
    show "(0 :: nat) < 4"
      by simp
    show "\<exists>t.
        Generic t \<in>
          set (ring (sa_ready (task_delay_abs ticks s) 0))"
      using idle_preserved by blast
  qed
qed

end
