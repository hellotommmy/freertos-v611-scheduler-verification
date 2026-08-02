theory Scheduler_Resume_Missed_Tick_Replay_Steps_Invariant
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Missed_Tick_Replay_Frame.Scheduler_Resume_Missed_Tick_Replay_Frame"
begin

text \<open>Arbitrary-length composition and the loop invariant.\<close>

lemma missed_tick_steps_add:
  "missed_tick_steps (m + n) r =
   missed_tick_steps n (missed_tick_steps m r)"
  by (induction n) simp_all

lemma missed_tick_steps_yield_frame [simp]:
  "mtrs_yield_required (missed_tick_steps n r) =
   mtrs_yield_required r"
  by (induction n) simp_all

lemma missed_tick_steps_tick [simp]:
  "sa_tick (mtrs_scheduler (missed_tick_steps n r)) =
   sa_tick (mtrs_scheduler r) + of_nat n"
  by (induction n) simp_all

lemma missed_tick_steps_missed_yield_frame [simp]:
  "sa_missed_yield (mtrs_scheduler (missed_tick_steps n r)) =
   sa_missed_yield (mtrs_scheduler r)"
  by (induction n) simp_all

lemma missed_tick_steps_yield_count_frame [simp]:
  "sa_yield_count (mtrs_scheduler (missed_tick_steps n r)) =
   sa_yield_count (mtrs_scheduler r)"
  by (induction n) simp_all

lemma missed_tick_steps_countdown:
  assumes rel: "missed_tick_count_rel r"
    and within: "n \<le> mtrs_remaining r"
  shows
    "missed_tick_count_rel (missed_tick_steps n r) \<and>
     mtrs_remaining (missed_tick_steps n r) =
       mtrs_remaining r - n"
  using rel within
proof (induction n arbitrary: r)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have n_within: "n \<le> mtrs_remaining r"
    using Suc.prems by simp
  obtain mid_rel mid_remaining where mid:
    "missed_tick_count_rel (missed_tick_steps n r)"
    "mtrs_remaining (missed_tick_steps n r) =
       mtrs_remaining r - n"
    using Suc.IH[OF Suc.prems(1) n_within] by blast
  have positive:
    "mtrs_remaining (missed_tick_steps n r) > 0"
    using Suc.prems(2) mid(2) by simp
  have next_rel:
    "missed_tick_count_rel
       (missed_tick_body_step (missed_tick_steps n r))"
    by (rule missed_tick_body_count_rel[OF mid(1) positive])
  show ?case
    using next_rel mid(2) Suc.prems(2) by simp
qed

lemma missed_tick_loop_inv_initial:
  assumes rel: "missed_tick_count_rel entry"
  shows
    "missed_tick_loop_inv (mtrs_remaining entry) 0
       (mtrs_remaining entry) entry entry"
  using rel by (simp add: missed_tick_loop_inv_def)

theorem missed_tick_loop_inv_step:
  assumes inv:
    "missed_tick_loop_inv total_count done (Suc remaining) entry current"
  shows
    "missed_tick_loop_inv total_count (Suc done) remaining entry
       (missed_tick_body_step current) \<and>
     missed_tick_measure (missed_tick_body_step current) <
       missed_tick_measure current"
proof -
  have entry_rel: "missed_tick_count_rel entry"
    and total_eq: "total_count = mtrs_remaining entry"
    and split: "total_count = done + Suc remaining"
    and current: "current = missed_tick_steps done entry"
    and current_rel: "missed_tick_count_rel current"
    and current_remaining: "mtrs_remaining current = Suc remaining"
    and yield_frame:
      "mtrs_yield_required current = mtrs_yield_required entry"
    using inv unfolding missed_tick_loop_inv_def by blast+
  have next_rel: "missed_tick_count_rel (missed_tick_body_step current)"
    by (rule missed_tick_body_count_rel[OF current_rel])
       (simp add: current_remaining)
  have next_state:
    "missed_tick_body_step current = missed_tick_steps (Suc done) entry"
    using current by simp
  have next_inv:
    "missed_tick_loop_inv total_count (Suc done) remaining entry
       (missed_tick_body_step current)"
    using entry_rel total_eq split current current_remaining yield_frame
      next_rel next_state
    by (simp add: missed_tick_loop_inv_def)
  have decrease:
    "missed_tick_measure (missed_tick_body_step current) <
       missed_tick_measure current"
    by (rule missed_tick_body_measure_decreases)
       (simp add: current_remaining)
  show ?thesis using next_inv decrease by blast
qed

theorem missed_tick_loop_inv_at_any_split:
  assumes rel: "missed_tick_count_rel entry"
    and split: "total_count = done + remaining"
    and total_eq: "total_count = mtrs_remaining entry"
  shows
    "missed_tick_loop_inv total_count done remaining entry
       (missed_tick_steps done entry)"
proof -
  have within: "done \<le> mtrs_remaining entry"
    using split total_eq by simp
  obtain current_rel current_remaining where current:
    "missed_tick_count_rel (missed_tick_steps done entry)"
    "mtrs_remaining (missed_tick_steps done entry) =
       mtrs_remaining entry - done"
    using missed_tick_steps_countdown[OF rel within] by blast
  show ?thesis
    using rel split total_eq current
    by (simp add: missed_tick_loop_inv_def)
qed

theorem missed_tick_loop_zero_exit:
  assumes inv:
    "missed_tick_loop_inv total_count total_count 0 entry current"
  shows
    "current = missed_tick_steps total_count entry \<and>
     mtrs_remaining current = 0 \<and>
     mtrs_source_count current = 0 \<and>
     sa_missed_ticks (mtrs_scheduler current) = 0 \<and>
     mtrs_yield_required current = mtrs_yield_required entry"
  using inv
  by (auto simp: missed_tick_loop_inv_def missed_tick_count_rel_def)

theorem missed_tick_run_exact:
  assumes rel: "missed_tick_count_rel entry"
  defines "total_count \<equiv> mtrs_remaining entry"
  defines "final \<equiv> missed_tick_steps total_count entry"
  shows
    "missed_tick_loop_inv total_count total_count 0 entry final \<and>
     mtrs_source_count final = 0 \<and>
     sa_missed_ticks (mtrs_scheduler final) = 0 \<and>
     sa_tick (mtrs_scheduler final) =
       sa_tick (mtrs_scheduler entry) + of_nat total_count"
proof -
  have inv:
    "missed_tick_loop_inv total_count total_count 0 entry final"
    unfolding total_count_def final_def
    by (rule missed_tick_loop_inv_at_any_split[OF rel]) simp_all
  note exit = missed_tick_loop_zero_exit[OF inv]
  show ?thesis using inv exit unfolding final_def by simp
qed

end
