theory Scheduler_Resume_Missed_Tick_Replay_Core
  imports
    "Word_Lib.More_Word"
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Invariant.Scheduler_Due_Prefix_Invariant"
begin

text \<open>
  Universal relation-level model of the missed-tick replay in
  xTaskResumeAll.  The generated source order is load-bearing:

    while (uxMissedTicks > 0) {
      vTaskIncrementTick();
      --uxMissedTicks;
    }

  A replay state therefore carries both the source 32-bit counter and its
  natural-number loop ghost.  A body step first applies the full unlocked
  tick transformer (including an arbitrary due prefix and a possible epoch
  wrap) and only then decrements both counters.  The scheduler state contains
  arbitrary live tasks, priorities, Generic/Event membership, keys, rings,
  cursors and physical-role choices; no task, priority, tick, counter, list
  length, or wrap position is fixed here.

  This is deliberately a relation layer before generated-source composition.
  It reuses the checked due-prefix endpoint equation and exposes the exact
  interfaces needed after the pending drain and before the final Boolean
  yield branch.  It does not claim that the generated xTaskResumeAll while
  loop has yet been connected to this relation.
\<close>

record 'tid missed_tick_replay_state =
  mtrs_scheduler :: "'tid scheduler_abs"
  mtrs_remaining :: nat
  mtrs_source_count :: "32 word"
  mtrs_yield_required :: bool

definition missed_tick_count_rel ::
  "'tid missed_tick_replay_state \<Rightarrow> bool"
where
  "missed_tick_count_rel r \<longleftrightarrow>
     mtrs_source_count r = of_nat (mtrs_remaining r) \<and>
     mtrs_remaining r < 2 ^ LENGTH(32) \<and>
     sa_missed_ticks (mtrs_scheduler r) = mtrs_remaining r"

definition missed_tick_replay_entry ::
  "'tid scheduler_abs \<Rightarrow> 32 word \<Rightarrow> bool \<Rightarrow>
   'tid missed_tick_replay_state"
where
  "missed_tick_replay_entry s w pending_yield =
     \<lparr>mtrs_scheduler = s\<lparr>sa_missed_ticks := unat w\<rparr>,
      mtrs_remaining = unat w,
      mtrs_source_count = w,
      mtrs_yield_required = pending_yield\<rparr>"

definition missed_tick_body_step ::
  "'tid missed_tick_replay_state \<Rightarrow>
   'tid missed_tick_replay_state"
where
  "missed_tick_body_step r =
     (let ticked = tick_unlocked_abs (mtrs_scheduler r);
          remaining = mtrs_remaining r - 1;
          source_count = mtrs_source_count r - 1
      in r\<lparr>
           mtrs_scheduler := ticked\<lparr>sa_missed_ticks := remaining\<rparr>,
           mtrs_remaining := remaining,
           mtrs_source_count := source_count
         \<rparr>)"

fun missed_tick_steps ::
  "nat \<Rightarrow> 'tid missed_tick_replay_state \<Rightarrow>
   'tid missed_tick_replay_state"
where
  "missed_tick_steps 0 r = r"
| "missed_tick_steps (Suc n) r =
     missed_tick_body_step (missed_tick_steps n r)"

definition missed_tick_measure ::
  "'tid missed_tick_replay_state \<Rightarrow> nat"
where
  "missed_tick_measure r = mtrs_remaining r"

definition missed_tick_loop_inv ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
   'tid missed_tick_replay_state \<Rightarrow>
   'tid missed_tick_replay_state \<Rightarrow> bool"
where
  "missed_tick_loop_inv total_count done remaining entry current \<longleftrightarrow>
     missed_tick_count_rel entry \<and>
     total_count = mtrs_remaining entry \<and>
     total_count = done + remaining \<and>
     current = missed_tick_steps done entry \<and>
     missed_tick_count_rel current \<and>
     mtrs_remaining current = remaining \<and>
     mtrs_yield_required current = mtrs_yield_required entry"

text \<open>Basic scalar and frame facts for the source-order body.\<close>

lemma missed_tick_entry_count_rel [simp]:
  "missed_tick_count_rel (missed_tick_replay_entry s w y)"
proof -
  have bound: "unat w < 2 ^ LENGTH(32)"
    by (rule unat_lt2p)
  show ?thesis
    using bound
    by (simp add: missed_tick_count_rel_def missed_tick_replay_entry_def)
qed

lemma missed_tick_body_scheduler [simp]:
  "mtrs_scheduler (missed_tick_body_step r) =
   (tick_unlocked_abs (mtrs_scheduler r))
      \<lparr>sa_missed_ticks := mtrs_remaining r - 1\<rparr>"
  by (simp add: missed_tick_body_step_def Let_def)

lemma missed_tick_body_remaining [simp]:
  "mtrs_remaining (missed_tick_body_step r) =
   mtrs_remaining r - 1"
  by (simp add: missed_tick_body_step_def Let_def)

lemma missed_tick_body_source_count [simp]:
  "mtrs_source_count (missed_tick_body_step r) =
   mtrs_source_count r - 1"
  by (simp add: missed_tick_body_step_def Let_def)

lemma missed_tick_body_yield_frame [simp]:
  "mtrs_yield_required (missed_tick_body_step r) =
   mtrs_yield_required r"
  by (simp add: missed_tick_body_step_def Let_def)

lemma missed_tick_body_count_rel:
  assumes rel: "missed_tick_count_rel r"
    and positive: "mtrs_remaining r > 0"
  shows "missed_tick_count_rel (missed_tick_body_step r)"
proof -
  obtain n where remaining: "mtrs_remaining r = Suc n"
    using positive by (cases "mtrs_remaining r") auto
  have bound: "n < 2 ^ LENGTH(32)"
    using rel remaining by (auto simp: missed_tick_count_rel_def)
  have source: "mtrs_source_count r = of_nat (Suc n)"
    using rel remaining by (simp add: missed_tick_count_rel_def)
  show ?thesis
    using bound source remaining
    by (simp add: missed_tick_count_rel_def missed_tick_body_step_def
        Let_def)
qed

lemma missed_tick_body_measure_decreases:
  assumes positive: "mtrs_remaining r > 0"
  shows
    "missed_tick_measure (missed_tick_body_step r) <
     missed_tick_measure r"
  using positive by (simp add: missed_tick_measure_def)

end
