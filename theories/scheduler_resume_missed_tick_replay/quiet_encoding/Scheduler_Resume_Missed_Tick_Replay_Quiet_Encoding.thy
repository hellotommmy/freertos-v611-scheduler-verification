theory Scheduler_Resume_Missed_Tick_Replay_Quiet_Encoding
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Missed_Tick_Replay_Pending_Join.Scheduler_Resume_Missed_Tick_Replay_Pending_Join"
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Outer_Quiet_Bool.Scheduler_Resume_Outer_Quiet_Bool"
begin

text \<open>
  Quiet-Boolean interface.  The existing generated-source quiet theorem uses
  the same signed return encoding and modulo-2^32 yield-counter delta.  The
  theorem below only identifies that endpoint encoding; it does not misuse
  the quiet theorem as a proof of the preceding nonempty replay loop.
\<close>

theorem missed_tick_outer_quiet_bool_encoding:
  "scheduler_resume_bool_word
      (fst (missed_tick_outer_finish r)) =
     (if missed_tick_outer_requested r then 1 else 0) \<and>
   scheduler_resume_bool_counter_delta
      (fst (missed_tick_outer_finish r)) =
     (if missed_tick_outer_requested r then 1 else 0)"
  by (simp add: missed_tick_outer_finish_def
      scheduler_resume_bool_word_def
      scheduler_resume_bool_counter_delta_def Let_def)

text \<open>
  Generated-source composition obligations intentionally left open:

  * derive the concrete while head from the completed pending-drain state and
    relate uxMissedTicks to mtrs_source_count/remaining;
  * at every body iteration, compose the generated vTaskIncrementTick theorem
    (including its arbitrary due-prefix/Event-family proof) before the concrete
    uxMissedTicks decrement;
  * prove the concrete while guard and word decrement preserve
    missed_tick_count_rel and discharge the natural measure;
  * compose the post-loop configUSE_PREEMPTION assignment with
    missed_tick_mark_replay_yield;
  * join pending-yield, replay-debt and xMissedYield through the concrete
    final OR, then use the quiet-Boolean return/counter interface for exactly
    one port yield.

  Until those obligations are checked, this theory is an invariant and
  compositional specification, not a complete C refinement theorem.
\<close>

end
