theory Scheduler_Resume_Missed_Tick_Replay_Tick_Wrap
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Missed_Tick_Replay_Steps_Invariant.Scheduler_Resume_Missed_Tick_Replay_Steps_Invariant"
begin

text \<open>
  Wrap is not a separate fixed test.  For every symbolic replay index k, if
  the word tick at that cutpoint increments to zero, the next source step
  swaps the semantic current/overflow roles and increments the overflow
  ledger.  Physical delayed rings remain where they are, as guaranteed by the
  due-prefix tick entry.
\<close>

definition missed_tick_wrap_at ::
  "'tid missed_tick_replay_state \<Rightarrow> nat \<Rightarrow> bool"
where
  "missed_tick_wrap_at entry k \<longleftrightarrow>
     sa_tick (mtrs_scheduler (missed_tick_steps k entry)) + 1 = 0"

theorem missed_tick_steps_wrap_at:
  assumes wrap: "missed_tick_wrap_at entry k"
  defines "before \<equiv> missed_tick_steps k entry"
  defines "after \<equiv> missed_tick_steps (Suc k) entry"
  shows
    "sa_tick (mtrs_scheduler after) = 0 \<and>
     sa_current_role_a (mtrs_scheduler after) =
       (\<not> sa_current_role_a (mtrs_scheduler before)) \<and>
     sa_overflows (mtrs_scheduler after) =
       Suc (sa_overflows (mtrs_scheduler before))"
proof -
  have wrap_before:
    "sa_tick (mtrs_scheduler before) + 1 = 0"
    using wrap unfolding missed_tick_wrap_at_def before_def by simp
  note role = missed_tick_body_wrap_role[OF wrap_before]
  show ?thesis
    using role wrap_before unfolding after_def before_def by simp
qed

theorem missed_tick_steps_no_wrap_at:
  assumes no_wrap: "\<not> missed_tick_wrap_at entry k"
  shows
    "sa_current_role_a
       (mtrs_scheduler (missed_tick_steps (Suc k) entry)) =
       sa_current_role_a
         (mtrs_scheduler (missed_tick_steps k entry)) \<and>
     sa_overflows
       (mtrs_scheduler (missed_tick_steps (Suc k) entry)) =
       sa_overflows
         (mtrs_scheduler (missed_tick_steps k entry))"
  using missed_tick_body_no_wrap_role[
      where r="missed_tick_steps k entry"] no_wrap
  by (simp add: missed_tick_wrap_at_def)

end
