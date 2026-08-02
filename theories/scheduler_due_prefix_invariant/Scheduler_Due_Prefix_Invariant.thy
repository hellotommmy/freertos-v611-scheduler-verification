theory Scheduler_Due_Prefix_Invariant
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Abstract_Model.Scheduler_Abstract_Model"
begin

text \<open>
  Pure, universally quantified loop algebra for the unlocked tick's arbitrary
  due prefix.  No task, priority, tick, key, delayed-list length, cursor, or
  wrap branch is fixed.  Concrete traces may motivate this invariant, but no
  concrete witness occurs in its statement.

  The loop view is phase-accurate at the granularity needed after the existing
  one-due cutpoints have been composed: a ghost prefix has been processed, a
  suffix of due Generic nodes remains, and a future suffix is untouched.  A
  Result body step moves exactly one head from remaining to processed and
  strictly decreases the remaining-length measure.  When no due node remains,
  an empty physical suffix is the normal while-guard exit, whereas a nonempty
  future suffix is the source's exceptional future-head exit.  The enclosing
  source finally turns both terminal controls into the public normal result.

  This theory intentionally has no concrete Event-root family.  The abstract
  @{const add_ready_node} removes a task from the logical
  @{const sa_event_waiting} set, but it cannot express the conditional
  intrusive Event-item removal, its count/cursor repair, or frames for an
  arbitrary finite family of Event roots.  Consequently the results below are
  the Generic/tick abstract fold skeleton only.  Event-family preservation and
  generated-source loop composition remain separate open obligations; none of
  these lemmas is a whole-source vTaskIncrementTick refinement.
\<close>

definition due_future_nodes ::
  "32 word \<Rightarrow> 'tid node_ring \<Rightarrow> 'tid node_kind list"
where
  "due_future_nodes now q =
     dropWhile (\<lambda>n. item_key q n \<le> now) (ring q)"

definition ordered_generic_delayed_ring :: "'tid node_ring \<Rightarrow> bool"
where
  "ordered_generic_delayed_ring q \<longleftrightarrow>
     xlist_wf q \<and>
     generic_ring q \<and>
     sorted (map (item_key q) (ring q))"

text \<open>List facts used to expose the canonical due/future split.\<close>

lemma due_takeWhile_memberD:
  assumes member: "x \<in> set (takeWhile P xs)"
  shows "P x"
  using member by (induction xs) auto

lemma due_takeWhile_member_in_list:
  assumes member: "x \<in> set (takeWhile P xs)"
  shows "x \<in> set xs"
  using member by (induction xs) auto

lemma due_dropWhile_headD:
  assumes head: "dropWhile P xs = x # rest"
  shows "\<not> P x"
  using head
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  show ?case
  proof (cases "P a")
    case True
    then have tail: "dropWhile P xs = x # rest"
      using Cons.prems by simp
    show ?thesis by (rule Cons.IH[OF tail])
  next
    case False
    then have "a = x"
      using Cons.prems by simp
    then show ?thesis using False by simp
  qed
qed

lemma due_sorted_dropWhile_all_future:
  fixes key :: "'a \<Rightarrow> 'b::linorder"
  assumes ordered: "sorted (map key xs)"
  shows
    "\<forall>x\<in>set (dropWhile (\<lambda>y. key y \<le> now) xs).
       now < key x"
  using ordered
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  show ?case
  proof (cases "key a \<le> now")
    case True
    with Cons show ?thesis by simp
  next
    case False
    have head_future: "now < key a"
      using False by simp
    have tail_lower: "\<forall>x\<in>set xs. key a \<le> key x"
      using Cons.prems by simp
    show ?thesis
      using False head_future tail_lower by auto
  qed
qed

lemma due_nodes_future_decomposition:
  "ring q = due_nodes now q @ due_future_nodes now q"
  by (simp add: due_nodes_def due_future_nodes_def)

lemma due_nodes_member_is_due:
  assumes member: "n \<in> set (due_nodes now q)"
  shows "item_key q n \<le> now"
proof -
  have in_prefix:
    "n \<in> set
      (takeWhile (\<lambda>x. item_key q x \<le> now) (ring q))"
    using member by (simp add: due_nodes_def)
  show ?thesis
    by (rule due_takeWhile_memberD[OF in_prefix])
qed

lemma due_future_head_is_future:
  assumes future: "due_future_nodes now q = n # rest"
  shows "now < item_key q n"
proof -
  have head:
    "dropWhile (\<lambda>x. item_key q x \<le> now) (ring q) = n # rest"
    using future by (simp add: due_future_nodes_def)
  have "\<not> item_key q n \<le> now"
    by (rule due_dropWhile_headD[OF head])
  then show ?thesis by simp
qed

lemma ordered_due_future_all_future:
  assumes ordered: "ordered_generic_delayed_ring q"
    and member: "n \<in> set (due_future_nodes now q)"
  shows "now < item_key q n"
  using due_sorted_dropWhile_all_future[
      of "item_key q" "ring q" now] ordered member
  by (auto simp: ordered_generic_delayed_ring_def due_future_nodes_def)

lemma ordered_due_node_is_generic:
  assumes ordered: "ordered_generic_delayed_ring q"
    and member: "n \<in> set (due_nodes now q)"
  shows "\<exists>t. n = Generic t"
proof -
  have in_prefix:
    "n \<in> set
      (takeWhile (\<lambda>x. item_key q x \<le> now) (ring q))"
    using member by (simp add: due_nodes_def)
  have in_ring: "n \<in> set (ring q)"
    by (rule due_takeWhile_member_in_list[OF in_prefix])
  show ?thesis
    using ordered in_ring
    by (auto simp: ordered_generic_delayed_ring_def generic_ring_def)
qed

text \<open>
  Removing a prefix is kept as an exact list ledger.  The removed items retain
  their payload map in @{const list_remove_abs}; only ring and possibly cursor
  change.  Distinctness is what rules out a removed prefix item reappearing in
  the suffix.
\<close>

lemma due_ring_remove_nodes:
  "ring (remove_nodes ns q) = fold remove1 ns (ring q)"
proof (induction ns arbitrary: q)
  case Nil
  then show ?case by (simp add: remove_nodes_def)
next
  case (Cons n ns)
  have induction_step:
    "ring (fold list_remove_abs ns (list_remove_abs n q)) =
     fold remove1 ns (ring (list_remove_abs n q))"
    using Cons.IH[of "list_remove_abs n q"]
    by (simp add: remove_nodes_def)
  show ?case
    using induction_step
    by (simp add: remove_nodes_def list_remove_abs_def)
qed

lemma due_fold_remove1_prefix:
  assumes distinct: "distinct (prefix @ suffix)"
  shows "fold remove1 prefix (prefix @ suffix) = suffix"
  using distinct
proof (induction prefix arbitrary: suffix)
  case Nil
  then show ?case by simp
next
  case (Cons n prefix)
  then show ?case by simp
qed

lemma due_remove_nodes_prefix_ring:
  assumes split: "ring q = prefix @ suffix"
    and distinct: "distinct (prefix @ suffix)"
  shows "ring (remove_nodes prefix q) = suffix"
  using due_ring_remove_nodes[of prefix q]
    due_fold_remove1_prefix[OF distinct] split
  by simp

lemma due_remove_nodes_append [simp]:
  "remove_nodes (xs @ [n]) q =
   list_remove_abs n (remove_nodes xs q)"
  by (simp add: remove_nodes_def)

text \<open>
  The normalized fold state removes the processed Generic prefix from the
  captured delayed ring and folds the corresponding ready transitions.  This
  is exactly the endpoint shape used by @{const tick_unlocked_abs}.
\<close>

definition due_prefix_fold_state ::
  "'tid scheduler_abs \<Rightarrow> 'tid node_kind list \<Rightarrow>
   'tid scheduler_abs"
where
  "due_prefix_fold_state entry processed =
     fold add_ready_node processed
       (put_current_delayed
         (remove_nodes processed (current_delayed_ring entry)) entry)"

lemma due_current_delayed_after_put [simp]:
  "current_delayed_ring (put_current_delayed q s) = q"
  by (cases "sa_current_role_a s")
     (simp_all add: current_delayed_ring_def put_current_delayed_def)

lemma due_put_current_identity [simp]:
  "put_current_delayed (current_delayed_ring s) s = s"
  by (cases "sa_current_role_a s")
     (simp_all add: current_delayed_ring_def put_current_delayed_def)

lemma due_put_current_overwrite [simp]:
  "put_current_delayed q'
     (put_current_delayed q s) = put_current_delayed q' s"
  by (cases "sa_current_role_a s")
     (simp_all add: put_current_delayed_def)

lemma due_add_ready_frames_current_delayed [simp]:
  "current_delayed_ring (add_ready_node n s) = current_delayed_ring s"
  by (cases n; cases s)
     (simp_all add: current_delayed_ring_def Let_def)

lemma due_fold_add_ready_frames_current_delayed [simp]:
  "current_delayed_ring (fold add_ready_node ns s) =
   current_delayed_ring s"
  by (induction ns arbitrary: s) simp_all

lemma due_put_current_add_ready_commute:
  "put_current_delayed q (add_ready_node n s) =
   add_ready_node n (put_current_delayed q s)"
  by (cases n; cases s)
     (simp_all add: put_current_delayed_def Let_def)

lemma due_put_current_fold_add_ready_commute:
  "put_current_delayed q (fold add_ready_node ns s) =
   fold add_ready_node ns (put_current_delayed q s)"
  by (induction ns arbitrary: s)
     (simp_all add: due_put_current_add_ready_commute)

lemma due_prefix_fold_state_current_delayed [simp]:
  "current_delayed_ring (due_prefix_fold_state entry processed) =
   remove_nodes processed (current_delayed_ring entry)"
  by (simp add: due_prefix_fold_state_def)

lemma due_prefix_fold_state_ring [simp]:
  "ring (current_delayed_ring
     (due_prefix_fold_state entry processed)) =
   ring (remove_nodes processed (current_delayed_ring entry))"
  by simp

definition due_prefix_result_step_abs ::
  "'tid scheduler_abs \<Rightarrow> 'tid node_kind list \<Rightarrow>
   'tid node_kind \<Rightarrow> 'tid scheduler_abs"
where
  "due_prefix_result_step_abs entry processed n =
     due_prefix_fold_state entry (processed @ [n])"

lemma due_prefix_result_step_fold_exposed:
  "due_prefix_result_step_abs entry processed n =
   add_ready_node n
     (fold add_ready_node processed
       (put_current_delayed
         (list_remove_abs n
           (remove_nodes processed (current_delayed_ring entry))) entry))"
  by (simp add: due_prefix_result_step_abs_def due_prefix_fold_state_def)

lemma due_prefix_result_step_is_one_generic_step:
  assumes current: "current = due_prefix_fold_state entry processed"
    and generic: "n = Generic t"
  shows
    "due_prefix_result_step_abs entry processed n =
     add_ready_node n
       (put_current_delayed
         (list_remove_abs n (current_delayed_ring current)) current)"
  using current generic
  by (simp add: due_prefix_result_step_abs_def
      due_prefix_fold_state_def due_put_current_fold_add_ready_commute)

datatype due_prefix_control =
    DueLoopBodyResult
  | DueLoopGuardNormal
  | DueLoopFutureHeadExn

fun due_prefix_control_of ::
  "'a list \<Rightarrow> 'a list \<Rightarrow> due_prefix_control"
where
  "due_prefix_control_of (n # remaining) future = DueLoopBodyResult"
| "due_prefix_control_of [] [] = DueLoopGuardNormal"
| "due_prefix_control_of [] (n # future) = DueLoopFutureHeadExn"

fun due_prefix_finally_returns :: "due_prefix_control \<Rightarrow> bool"
where
  "due_prefix_finally_returns DueLoopBodyResult = False"
| "due_prefix_finally_returns DueLoopGuardNormal = True"
| "due_prefix_finally_returns DueLoopFutureHeadExn = True"

definition due_prefix_measure :: "'a list \<Rightarrow> nat"
where
  "due_prefix_measure remaining = length remaining"

definition due_prefix_loop_inv ::
  "32 word \<Rightarrow> 'tid scheduler_abs \<Rightarrow>
   'tid node_kind list \<Rightarrow> 'tid node_kind list \<Rightarrow>
   'tid node_kind list \<Rightarrow> 'tid scheduler_abs \<Rightarrow> bool"
where
  "due_prefix_loop_inv now entry processed remaining future current \<longleftrightarrow>
     (let q = current_delayed_ring entry;
          due = due_nodes now q
      in ordered_generic_delayed_ring q \<and>
         future = due_future_nodes now q \<and>
         ring q = due @ future \<and>
         due = processed @ remaining \<and>
         current = due_prefix_fold_state entry processed \<and>
         ring (current_delayed_ring current) = remaining @ future)"

lemma due_prefix_loop_inv_initial:
  assumes ordered:
    "ordered_generic_delayed_ring (current_delayed_ring entry)"
  shows
    "due_prefix_loop_inv now entry []
       (due_nodes now (current_delayed_ring entry))
       (due_future_nodes now (current_delayed_ring entry)) entry"
  using ordered due_nodes_future_decomposition[
      of "current_delayed_ring entry" now]
  by (simp add: due_prefix_loop_inv_def due_prefix_fold_state_def
      remove_nodes_def Let_def)

theorem due_prefix_loop_inv_at_any_split:
  assumes ordered:
      "ordered_generic_delayed_ring (current_delayed_ring entry)"
    and future:
      "future = due_future_nodes now (current_delayed_ring entry)"
    and split:
      "due_nodes now (current_delayed_ring entry) = processed @ remaining"
  shows
    "due_prefix_loop_inv now entry processed remaining future
       (due_prefix_fold_state entry processed)"
proof -
  let ?q = "current_delayed_ring entry"
  let ?due = "due_nodes now ?q"
  have decomposition: "ring ?q = ?due @ future"
    using due_nodes_future_decomposition[of ?q now] future by simp
  have ring_split: "ring ?q = processed @ (remaining @ future)"
    using decomposition split by (simp add: append_assoc)
  have ring_distinct: "distinct (ring ?q)"
    using ordered
    by (simp add: ordered_generic_delayed_ring_def xlist_wf_def)
  have split_distinct: "distinct (processed @ (remaining @ future))"
    using ring_distinct ring_split by simp
  have removed:
    "ring (remove_nodes processed ?q) = remaining @ future"
    by (rule due_remove_nodes_prefix_ring[OF ring_split split_distinct])
  show ?thesis
    using ordered future split decomposition removed
    by (simp add: due_prefix_loop_inv_def Let_def)
qed

lemma due_prefix_loop_inv_due_splitD:
  assumes inv:
    "due_prefix_loop_inv now entry processed remaining future current"
  shows
    "due_nodes now (current_delayed_ring entry) =
       processed @ remaining"
  using inv
  unfolding due_prefix_loop_inv_def Let_def
  by blast

lemma due_prefix_loop_inv_currentD:
  assumes inv:
    "due_prefix_loop_inv now entry processed remaining future current"
  shows "current = due_prefix_fold_state entry processed"
  using inv
  unfolding due_prefix_loop_inv_def Let_def
  by blast

lemma due_prefix_loop_inv_ringD:
  assumes inv:
    "due_prefix_loop_inv now entry processed remaining future current"
  shows "ring (current_delayed_ring current) = remaining @ future"
  using inv
  unfolding due_prefix_loop_inv_def Let_def
  by blast

lemma due_prefix_loop_inv_result_head:
  assumes inv:
      "due_prefix_loop_inv now entry processed (n # remaining)
         future current"
  shows
    "item_key (current_delayed_ring entry) n \<le> now \<and>
     (\<exists>t. n = Generic t) \<and>
     due_prefix_control_of (n # remaining) future = DueLoopBodyResult"
proof -
  let ?q = "current_delayed_ring entry"
  have split:
    "due_nodes now ?q = processed @ (n # remaining)"
    by (rule due_prefix_loop_inv_due_splitD[OF inv])
  have member: "n \<in> set (due_nodes now ?q)"
    using split by auto
  have ordered: "ordered_generic_delayed_ring ?q"
    using inv
    unfolding due_prefix_loop_inv_def Let_def
    by blast
  show ?thesis
    using due_nodes_member_is_due[OF member]
      ordered_due_node_is_generic[OF ordered member]
    by simp
qed

lemma due_prefix_result_step_decreases:
  "due_prefix_measure remaining <
   due_prefix_measure (n # remaining)"
  by (simp add: due_prefix_measure_def)

theorem due_prefix_result_step_preserves_inv:
  assumes inv:
    "due_prefix_loop_inv now entry processed (n # remaining)
       future current"
  shows
    "due_prefix_loop_inv now entry (processed @ [n]) remaining future
       (due_prefix_result_step_abs entry processed n)"
proof -
  let ?q = "current_delayed_ring entry"
  let ?due = "due_nodes now ?q"
  have ordered: "ordered_generic_delayed_ring ?q"
    using inv
    unfolding due_prefix_loop_inv_def Let_def
    by blast
  have future_def: "future = due_future_nodes now ?q"
    using inv
    unfolding due_prefix_loop_inv_def Let_def
    by blast
  have due_split: "?due = processed @ (n # remaining)"
    by (rule due_prefix_loop_inv_due_splitD[OF inv])
  have due_split': "?due = (processed @ [n]) @ remaining"
    using due_split by (simp add: append_assoc)
  have post:
    "due_prefix_loop_inv now entry (processed @ [n]) remaining future
       (due_prefix_fold_state entry (processed @ [n]))"
    by (rule due_prefix_loop_inv_at_any_split[
        OF ordered future_def due_split'])
  show ?thesis
    using post by (simp add: due_prefix_result_step_abs_def)
qed

theorem due_prefix_result_step_sound:
  assumes inv:
    "due_prefix_loop_inv now entry processed (n # remaining)
       future current"
  shows
    "due_prefix_control_of (n # remaining) future = DueLoopBodyResult \<and>
     item_key (current_delayed_ring entry) n \<le> now \<and>
     (\<exists>t. n = Generic t) \<and>
     due_prefix_loop_inv now entry (processed @ [n]) remaining future
       (due_prefix_result_step_abs entry processed n) \<and>
     due_prefix_measure remaining <
       due_prefix_measure (n # remaining)"
  using due_prefix_loop_inv_result_head[OF inv]
    due_prefix_result_step_preserves_inv[OF inv]
    due_prefix_result_step_decreases[of remaining n]
  by blast

corollary due_prefix_result_step_is_source_order_one_due:
  assumes inv:
    "due_prefix_loop_inv now entry processed (n # remaining)
       future current"
  shows
    "\<exists>t. n = Generic t \<and>
       due_prefix_result_step_abs entry processed n =
         add_ready_node n
           (put_current_delayed
             (list_remove_abs n (current_delayed_ring current)) current)"
proof -
  obtain t where generic: "n = Generic t"
    using due_prefix_loop_inv_result_head[OF inv] by blast
  have current: "current = due_prefix_fold_state entry processed"
    by (rule due_prefix_loop_inv_currentD[OF inv])
  have step:
    "due_prefix_result_step_abs entry processed n =
       add_ready_node n
         (put_current_delayed
           (list_remove_abs n (current_delayed_ring current)) current)"
    by (rule due_prefix_result_step_is_one_generic_step[
        OF current generic])
  show ?thesis using generic step by blast
qed

lemma due_prefix_loop_inv_finished:
  assumes inv:
    "due_prefix_loop_inv now entry processed [] future current"
  shows
    "processed = due_nodes now (current_delayed_ring entry) \<and>
     current = due_prefix_fold_state entry
       (due_nodes now (current_delayed_ring entry)) \<and>
     ring (current_delayed_ring current) = future"
  using inv
  by (auto simp: due_prefix_loop_inv_def Let_def)

theorem due_prefix_empty_normal_exit:
  assumes inv:
    "due_prefix_loop_inv now entry processed [] [] current"
  shows
    "due_prefix_control_of [] [] = DueLoopGuardNormal \<and>
     due_prefix_finally_returns (due_prefix_control_of [] []) \<and>
     processed = due_nodes now (current_delayed_ring entry) \<and>
     current = due_prefix_fold_state entry
       (due_nodes now (current_delayed_ring entry)) \<and>
     ring (current_delayed_ring current) = []"
proof -
  have control:
    "due_prefix_control_of [] [] = DueLoopGuardNormal"
    by simp
  have returns:
    "due_prefix_finally_returns (due_prefix_control_of [] [])"
    by simp
  have finished:
    "processed = due_nodes now (current_delayed_ring entry) \<and>
     current = due_prefix_fold_state entry
       (due_nodes now (current_delayed_ring entry)) \<and>
     ring (current_delayed_ring current) = []"
    by (rule due_prefix_loop_inv_finished[OF inv])
  show ?thesis using control returns finished by blast
qed

theorem due_prefix_future_head_exception_exit:
  assumes inv:
    "due_prefix_loop_inv now entry processed [] (n # future) current"
  shows
    "due_prefix_control_of [] (n # future) = DueLoopFutureHeadExn \<and>
     due_prefix_finally_returns
       (due_prefix_control_of [] (n # future)) \<and>
     now < item_key (current_delayed_ring entry) n \<and>
     (\<forall>x\<in>set (n # future).
       now < item_key (current_delayed_ring entry) x) \<and>
     processed = due_nodes now (current_delayed_ring entry) \<and>
     current = due_prefix_fold_state entry
       (due_nodes now (current_delayed_ring entry)) \<and>
     ring (current_delayed_ring current) = n # future"
proof -
  let ?q = "current_delayed_ring entry"
  have future_rev:
    "n # future = due_future_nodes now ?q"
    using inv
    unfolding due_prefix_loop_inv_def Let_def
    by blast
  have future_def:
    "due_future_nodes now ?q = n # future"
    using future_rev by simp
  have ordered: "ordered_generic_delayed_ring ?q"
    using inv
    unfolding due_prefix_loop_inv_def Let_def
    by blast
  have head_future: "now < item_key ?q n"
    by (rule due_future_head_is_future[OF future_def])
  have all_future:
    "\<forall>x\<in>set (n # future). now < item_key ?q x"
  proof (intro ballI)
    fix x
    assume member: "x \<in> set (n # future)"
    have "x \<in> set (due_future_nodes now ?q)"
      using member future_def by simp
    then show "now < item_key ?q x"
      by (rule ordered_due_future_all_future[OF ordered])
  qed
  have control:
    "due_prefix_control_of [] (n # future) = DueLoopFutureHeadExn"
    by simp
  have returns:
    "due_prefix_finally_returns
       (due_prefix_control_of [] (n # future))"
    by simp
  have finished:
    "processed = due_nodes now (current_delayed_ring entry) \<and>
     current = due_prefix_fold_state entry
       (due_nodes now (current_delayed_ring entry)) \<and>
     ring (current_delayed_ring current) = n # future"
    by (rule due_prefix_loop_inv_finished[OF inv])
  show ?thesis
    using control returns head_future all_future finished by blast
qed

text \<open>
  Re-express the tick prefix before the loop without importing a generated C
  theory.  At wrap this changes only the semantic current/overflow role and the
  overflow count, exactly as @{const tick_unlocked_abs}; physical rings stay in
  place.
\<close>

definition due_tick_entry_abs ::
  "'tid scheduler_abs \<Rightarrow> 'tid scheduler_abs"
where
  "due_tick_entry_abs s =
     (let next = sa_tick s + 1;
          s0 = s\<lparr>sa_tick := next\<rparr>
      in if next = 0 then swap_delayed_roles s0 else s0)"

definition due_tick_sequence_abs ::
  "'tid scheduler_abs \<Rightarrow> 'tid node_kind list"
where
  "due_tick_sequence_abs s =
     due_nodes (sa_tick (due_tick_entry_abs s))
       (current_delayed_ring (due_tick_entry_abs s))"

lemma due_tick_entry_tick [simp]:
  "sa_tick (due_tick_entry_abs s) = sa_tick s + 1"
  by (simp add: due_tick_entry_abs_def swap_delayed_roles_def Let_def)

theorem tick_unlocked_abs_is_due_prefix_fold:
  "tick_unlocked_abs s =
   due_prefix_fold_state (due_tick_entry_abs s)
     (due_tick_sequence_abs s)"
  by (simp add: tick_unlocked_abs_def due_tick_entry_abs_def
      due_tick_sequence_abs_def due_prefix_fold_state_def
      swap_delayed_roles_def Let_def)

theorem due_tick_loop_initial:
  assumes ordered:
    "ordered_generic_delayed_ring
       (current_delayed_ring (due_tick_entry_abs s))"
  shows
    "due_prefix_loop_inv (sa_tick (due_tick_entry_abs s))
       (due_tick_entry_abs s) [] (due_tick_sequence_abs s)
       (due_future_nodes (sa_tick (due_tick_entry_abs s))
         (current_delayed_ring (due_tick_entry_abs s)))
       (due_tick_entry_abs s)"
proof -
  have initial:
    "due_prefix_loop_inv (sa_tick (due_tick_entry_abs s))
       (due_tick_entry_abs s) []
       (due_nodes (sa_tick (due_tick_entry_abs s))
         (current_delayed_ring (due_tick_entry_abs s)))
       (due_future_nodes (sa_tick (due_tick_entry_abs s))
         (current_delayed_ring (due_tick_entry_abs s)))
       (due_tick_entry_abs s)"
    by (rule due_prefix_loop_inv_initial[OF ordered])
  show ?thesis
    using initial by (simp add: due_tick_sequence_abs_def)
qed

theorem due_tick_terminal_state_matches_tick_unlocked_abs:
  assumes inv:
    "due_prefix_loop_inv (sa_tick (due_tick_entry_abs s))
       (due_tick_entry_abs s) processed [] future current"
  shows "current = tick_unlocked_abs s"
proof -
  have current:
    "current = due_prefix_fold_state (due_tick_entry_abs s)
       (due_nodes (sa_tick (due_tick_entry_abs s))
         (current_delayed_ring (due_tick_entry_abs s)))"
    using due_prefix_loop_inv_finished[OF inv] by blast
  show ?thesis
    using current tick_unlocked_abs_is_due_prefix_fold[of s]
    by (simp add: due_tick_sequence_abs_def)
qed

corollary due_tick_normal_exit_matches_tick_unlocked_abs:
  assumes inv:
    "due_prefix_loop_inv (sa_tick (due_tick_entry_abs s))
       (due_tick_entry_abs s) processed [] [] current"
  shows
    "due_prefix_control_of [] [] = DueLoopGuardNormal \<and>
     due_prefix_finally_returns (due_prefix_control_of [] []) \<and>
     current = tick_unlocked_abs s"
  using due_tick_terminal_state_matches_tick_unlocked_abs[OF inv]
  by simp

corollary due_tick_future_exn_matches_tick_unlocked_abs:
  assumes inv:
    "due_prefix_loop_inv (sa_tick (due_tick_entry_abs s))
       (due_tick_entry_abs s) processed [] (n # future) current"
  shows
    "due_prefix_control_of [] (n # future) = DueLoopFutureHeadExn \<and>
     due_prefix_finally_returns
       (due_prefix_control_of [] (n # future)) \<and>
     sa_tick (due_tick_entry_abs s) <
       item_key (current_delayed_ring (due_tick_entry_abs s)) n \<and>
     current = tick_unlocked_abs s"
  using due_prefix_future_head_exception_exit[OF inv]
    due_tick_terminal_state_matches_tick_unlocked_abs[OF inv]
  by blast

text \<open>
  Boundary of this session: the arbitrary due-prefix induction, strict variant,
  canonical future-head exit, wrap-parametric entry, and exact agreement with
  @{const remove_nodes}/@{const add_ready_node} in
  @{const tick_unlocked_abs} are represented here.  Still open are (1) lifting
  every Result step through the six one-due raw/source phases, (2) preserving
  the complete finite Event-root family in the linked branch, (3) the actual
  generated while/throw/finally VCG, and (4) scheduler scalar/root/heap relation
  reconstruction at the endpoint.  Those are source/refinement obligations,
  not assumptions hidden in this abstract invariant.
\<close>

end
