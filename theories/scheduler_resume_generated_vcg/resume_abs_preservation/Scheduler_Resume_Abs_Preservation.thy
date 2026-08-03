theory Scheduler_Resume_Abs_Preservation
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Abs_Kit.Scheduler_Resume_Abs_Kit"
begin

text \<open>
  The abstract one-task resume preserves the core well-formedness
  invariant.  This is the first invariant-preservation theorem for any
  abstract scheduler step in this development; the drained gate relation
  cannot be re-established without it.  The hypotheses are exactly what the
  gate supplies: a well-formed state and a pending task.  Everything else --
  that the task is live, blocked on one of the three generic lists, and
  absent from every ready queue -- is derived from membership
  well-formedness, not assumed.
\<close>

section \<open>Component equations of the abstract one-task resume\<close>

lemma resume_one_pending_abs_components:
  "sa_live (resume_one_pending_abs t s) = sa_live s \<and>
   sa_priority (resume_one_pending_abs t s) = sa_priority s \<and>
   sa_current (resume_one_pending_abs t s) = sa_current s \<and>
   sa_current_role_a (resume_one_pending_abs t s) = sa_current_role_a s \<and>
   sa_tick (resume_one_pending_abs t s) = sa_tick s \<and>
   sa_suspend_depth (resume_one_pending_abs t s) = sa_suspend_depth s \<and>
   sa_missed_ticks (resume_one_pending_abs t s) = sa_missed_ticks s \<and>
   sa_missed_yield (resume_one_pending_abs t s) = sa_missed_yield s \<and>
   sa_overflows (resume_one_pending_abs t s) = sa_overflows s \<and>
   sa_yield_count (resume_one_pending_abs t s) = sa_yield_count s \<and>
   sa_pending (resume_one_pending_abs t s) =
     list_remove_abs (Event t) (sa_pending s) \<and>
   sa_delayed_a (resume_one_pending_abs t s) =
     list_remove_abs (Generic t) (sa_delayed_a s) \<and>
   sa_delayed_b (resume_one_pending_abs t s) =
     list_remove_abs (Generic t) (sa_delayed_b s) \<and>
   sa_suspended (resume_one_pending_abs t s) =
     list_remove_abs (Generic t) (sa_suspended s) \<and>
   sa_ready (resume_one_pending_abs t s) =
     (sa_ready s)
       (sa_priority s t :=
         list_insert_end_abs (Generic t) (pending_generic_key_abs t s)
           (sa_ready s (sa_priority s t))) \<and>
   sa_wake (resume_one_pending_abs t s) = (sa_wake s)(t := None) \<and>
   sa_event_waiting (resume_one_pending_abs t s) =
     sa_event_waiting s - {t} \<and>
   sa_top_ready (resume_one_pending_abs t s) =
     max (sa_top_ready s) (sa_priority s t)"
  by (simp add: resume_one_pending_abs_def
      resume_remove_generic_abs_def resume_add_ready_with_key_abs_def
      Let_def)

section \<open>Well-formedness of the two ring primitives\<close>

lemma xlist_wf_remove:
  assumes wf: "xlist_wf q"
  shows "xlist_wf (list_remove_abs x q)"
proof -
  have distinct: "distinct (ring q)"
    using wf by (simp add: xlist_wf_def)
  have distinct': "distinct (remove1 x (ring q))"
    using distinct by simp
  show ?thesis
  proof (cases "cursor q = Some x")
    case True
    show ?thesis
    proof (cases "predecessor x (ring q)")
      case None
      then show ?thesis
        using True distinct'
        by (simp add: list_remove_abs_def xlist_wf_def)
    next
      case (Some p)
      have "p \<in> set (remove1 x (ring q))"
        by (rule predecessor_not_removed[OF distinct Some])
      then show ?thesis
        using True Some distinct'
        by (simp add: list_remove_abs_def xlist_wf_def)
    qed
  next
    case False
    show ?thesis
    proof (cases "cursor q")
      case None
      then show ?thesis
        using False distinct'
        by (simp add: list_remove_abs_def xlist_wf_def)
    next
      case (Some c)
      have c_member: "c \<in> set (ring q)"
        using wf Some by (simp add: xlist_wf_def)
      have c_not_x: "c \<noteq> x"
        using False Some by auto
      have "c \<in> set (remove1 x (ring q))"
        using c_member c_not_x distinct by (simp add: set_remove1_eq)
      then show ?thesis
        using False Some distinct'
        by (simp add: list_remove_abs_def xlist_wf_def)
    qed
  qed
qed

lemma xlist_wf_insert_end:
  assumes wf: "xlist_wf q"
    and fresh: "x \<notin> set (ring q)"
  shows "xlist_wf (list_insert_end_abs x k q)"
proof (cases "cursor q")
  case None
  show ?thesis
    using wf fresh None
    by (simp add: list_insert_end_abs_def xlist_wf_def)
next
  case (Some c)
  have c_member: "c \<in> set (ring q)"
    using wf Some by (simp add: xlist_wf_def)
  have distinct: "distinct (ring q)"
    using wf by (simp add: xlist_wf_def)
  have set': "set (insert_after c x (ring q)) = insert x (set (ring q))"
    by (rule set_insert_after[OF c_member])
  have distinct': "distinct (insert_after c x (ring q))"
    by (rule distinct_insert_after[OF distinct fresh c_member])
  show ?thesis
    using Some set' distinct'
    by (simp add: list_insert_end_abs_def xlist_wf_def)
qed

section \<open>Tail cursors under member removal and end insertion\<close>

lemma tail_cursor_wf_remove:
  assumes wf: "xlist_wf q"
    and tail: "tail_cursor_wf q"
    and member: "x \<in> set (ring q)"
  shows "tail_cursor_wf (list_remove_abs x q)"
proof -
  have distinct: "distinct (ring q)"
    using wf by (simp add: xlist_wf_def)
  have nonempty: "ring q \<noteq> []"
    using member by auto
  have cursor: "cursor q = Some (last (ring q))"
    using tail nonempty by (simp add: tail_cursor_wf_def)
  show ?thesis
  proof (cases "x = last (ring q)")
    case True
    have removed: "remove1 x (ring q) = butlast (ring q)"
      using distinct nonempty True by (simp add: remove1_last_butlast)
    show ?thesis
    proof (cases "butlast (ring q) = []")
      case True_empty: True
      have single: "ring q = [x]"
        using True True_empty nonempty
        by (metis append_butlast_last_id append_Nil)
      have pred_none: "predecessor x (ring q) = None"
        using single by simp
      show ?thesis
        using cursor True pred_none removed True_empty
        by (simp add: list_remove_abs_def tail_cursor_wf_def)
    next
      case False_nonempty: False
      have long: "2 \<le> length (ring q)"
        using nonempty False_nonempty
        by (cases "ring q" rule: rev_cases) (auto simp: Suc_le_eq)
      have pred:
        "predecessor x (ring q) = Some (last (butlast (ring q)))"
        using predecessor_last[OF distinct long] True by simp
      show ?thesis
        using cursor True pred removed False_nonempty
        by (simp add: list_remove_abs_def tail_cursor_wf_def)
    qed
  next
    case False
    have cursor_stays: "cursor q \<noteq> Some x"
      using cursor False by simp
    have removed_nonempty: "remove1 x (ring q) \<noteq> []"
    proof
      assume empty: "remove1 x (ring q) = []"
      obtain "as" bs where split: "ring q = as @ x # bs"
          and fresh_as: "x \<notin> set as"
        using split_list_first[OF member] by blast
      have "remove1 x (ring q) = as @ bs"
        using split fresh_as by (simp add: remove1_append)
      then have "ring q = [x]"
        using empty split by simp
      then show False using False by simp
    qed
    have last_same: "last (remove1 x (ring q)) = last (ring q)"
      by (rule last_remove1_not_last[OF distinct member False])
    show ?thesis
      using cursor cursor_stays removed_nonempty last_same
      by (simp add: list_remove_abs_def tail_cursor_wf_def)
  qed
qed

lemma tail_cursor_wf_insert_end:
  assumes wf: "xlist_wf q"
    and tail: "tail_cursor_wf q"
  shows "tail_cursor_wf (list_insert_end_abs x k q)"
proof (cases "cursor q")
  case None
  have empty: "ring q = []"
    using tail None by (simp add: tail_cursor_wf_def split: if_splits)
  show ?thesis
    using None empty
    by (simp add: list_insert_end_abs_def tail_cursor_wf_def)
next
  case (Some c)
  have nonempty: "ring q \<noteq> []"
    using tail Some by (auto simp: tail_cursor_wf_def split: if_splits)
  have c_last: "c = last (ring q)"
    using tail Some nonempty by (simp add: tail_cursor_wf_def)
  have distinct: "distinct (ring q)"
    using wf by (simp add: xlist_wf_def)
  have appended:
    "insert_after c x (ring q) = ring q @ [x]"
    using insert_after_last_append[OF distinct nonempty] c_last by simp
  show ?thesis
    using Some appended
    by (simp add: list_insert_end_abs_def tail_cursor_wf_def)
qed

section \<open>Task sets under the two ring primitives\<close>

lemma generic_task_set_remove:
  assumes distinct: "distinct (ring q)"
  shows
    "generic_task_set (list_remove_abs (Generic t) q) =
     generic_task_set q - {t}"
  using distinct
  by (auto simp: generic_task_set_def list_remove_abs_def
      set_remove1_eq)

lemma event_task_set_remove:
  assumes distinct: "distinct (ring q)"
  shows
    "event_task_set (list_remove_abs (Event t) q) =
     event_task_set q - {t}"
  using distinct
  by (auto simp: event_task_set_def list_remove_abs_def
      set_remove1_eq)

lemma ring_set_insert_end:
  assumes wf: "xlist_wf q"
  shows
    "set (ring (list_insert_end_abs x k q)) = insert x (set (ring q))"
proof (cases "cursor q")
  case None
  then show ?thesis by (simp add: list_insert_end_abs_def)
next
  case (Some c)
  have c_member: "c \<in> set (ring q)"
    using wf Some by (simp add: xlist_wf_def)
  show ?thesis
    using Some set_insert_after[OF c_member]
    by (simp add: list_insert_end_abs_def)
qed

lemma generic_task_set_insert_end:
  assumes wf: "xlist_wf q"
  shows
    "generic_task_set (list_insert_end_abs (Generic t) k q) =
     insert t (generic_task_set q)"
  using ring_set_insert_end[OF wf]
  by (auto simp: generic_task_set_def)

lemma generic_ring_remove:
  "generic_ring q \<Longrightarrow> generic_ring (list_remove_abs x q)"
  using set_remove1_subset[of x "ring q"]
  by (auto simp: generic_ring_def list_remove_abs_def)

lemma event_ring_remove:
  "event_ring q \<Longrightarrow> event_ring (list_remove_abs x q)"
  using set_remove1_subset[of x "ring q"]
  by (auto simp: event_ring_def list_remove_abs_def)

lemma generic_ring_insert_end:
  assumes wf: "xlist_wf q"
    and generic: "generic_ring q"
  shows "generic_ring (list_insert_end_abs (Generic t) k q)"
  using generic ring_set_insert_end[OF wf]
  by (auto simp: generic_ring_def)

lemma list_remove_abs_nonmember:
  assumes wf: "xlist_wf q"
    and fresh: "x \<notin> set (ring q)"
  shows "list_remove_abs x q = q"
proof -
  have cursor_not_x: "cursor q \<noteq> Some x"
    using wf fresh by (auto simp: xlist_wf_def split: option.splits)
  show ?thesis
    using fresh cursor_not_x
    by (simp add: list_remove_abs_def remove1_idem)
qed

lemma item_key_remove:
  "item_key (list_remove_abs x q) = item_key q"
  by (simp add: list_remove_abs_def)

section \<open>The abstract one-task resume preserves core well-formedness\<close>

theorem core_wf_resume_one_pending_abs:
  assumes wf: "core_wf s"
    and pending: "Event t \<in> set (ring (sa_pending s))"
  shows "core_wf (resume_one_pending_abs t s)"
proof -
  let ?k = "pending_generic_key_abs t s"
  let ?p0 = "sa_priority s t"
  have eq:
    "resume_one_pending_abs t s =
       s\<lparr>sa_pending := list_remove_abs (Event t) (sa_pending s),
          sa_delayed_a := list_remove_abs (Generic t) (sa_delayed_a s),
          sa_delayed_b := list_remove_abs (Generic t) (sa_delayed_b s),
          sa_suspended := list_remove_abs (Generic t) (sa_suspended s),
          sa_ready := (sa_ready s)
            (?p0 := list_insert_end_abs (Generic t) ?k
              (sa_ready s ?p0)),
          sa_wake := (sa_wake s)(t := None),
          sa_event_waiting := sa_event_waiting s - {t},
          sa_top_ready := max (sa_top_ready s) ?p0\<rparr>"
    by (simp add: resume_one_pending_abs_def
        resume_remove_generic_abs_def resume_add_ready_with_key_abs_def
        Let_def)
  have members: "membership_wf s"
    using wf by (simp add: core_wf_def)
  have shapes: "ring_shape_wf s"
    using wf by (simp add: core_wf_def)
  have roles: "role_wf s"
    using wf by (simp add: core_wf_def)
  have time: "time_wf s"
    using wf by (simp add: core_wf_def)
  have cache: "ready_cache_wf s"
    using wf by (simp add: core_wf_def)
  have t_pending_set: "t \<in> event_task_set (sa_pending s)"
    using pending by (simp add: event_task_set_def)
  have live_t: "t \<in> sa_live s"
    using members t_pending_set
    by (auto simp: membership_wf_def Let_def)
  have pri_t: "?p0 < 4"
    using wf live_t by (simp add: core_wf_def)
  have t_blocked:
    "t \<in> generic_task_set (sa_delayed_a s) \<union>
         generic_task_set (sa_delayed_b s) \<union>
         generic_task_set (sa_suspended s)"
    using members t_pending_set
    by (auto simp: membership_wf_def Let_def)
  have t_not_ready: "t \<notin> ready_task_set s"
    using members t_blocked
    by (auto simp: membership_wf_def Let_def)
  have fresh_ready:
    "\<And>p. p < 4 \<Longrightarrow> Generic t \<notin> set (ring (sa_ready s p))"
    using t_not_ready
    by (auto simp: ready_task_set_def generic_task_set_def)
  have wf_ready: "\<And>p. p < 4 \<Longrightarrow> xlist_wf (sa_ready s p)"
    using shapes by (simp add: ring_shape_wf_def)
  have wf_pending: "xlist_wf (sa_pending s)"
    using shapes by (simp add: ring_shape_wf_def)
  have wf_da: "xlist_wf (sa_delayed_a s)"
    using shapes by (simp add: ring_shape_wf_def)
  have wf_db: "xlist_wf (sa_delayed_b s)"
    using shapes by (simp add: ring_shape_wf_def)
  have wf_susp: "xlist_wf (sa_suspended s)"
    using shapes by (simp add: ring_shape_wf_def)

  have shape':
    "ring_shape_wf (resume_one_pending_abs t s)"
    unfolding ring_shape_wf_def eq
    using wf_ready wf_pending wf_da wf_db wf_susp pri_t fresh_ready
    by (auto intro!: xlist_wf_remove xlist_wf_insert_end)

  have delayed_a_cursor:
    "cursor (list_remove_abs (Generic t) (sa_delayed_a s)) = None"
    using roles
    by (simp add: role_wf_def list_remove_abs_def)
  have delayed_b_cursor:
    "cursor (list_remove_abs (Generic t) (sa_delayed_b s)) = None"
    using roles
    by (simp add: role_wf_def list_remove_abs_def)
  have pending_tail:
    "tail_cursor_wf (list_remove_abs (Event t) (sa_pending s))"
    using roles wf_pending pending
    by (auto simp: role_wf_def intro!: tail_cursor_wf_remove)
  have susp_tail:
    "tail_cursor_wf (list_remove_abs (Generic t) (sa_suspended s))"
  proof (cases "Generic t \<in> set (ring (sa_suspended s))")
    case True
    show ?thesis
      using roles wf_susp True
      by (auto simp: role_wf_def intro!: tail_cursor_wf_remove)
  next
    case False
    show ?thesis
      using roles list_remove_abs_nonmember[OF wf_susp False]
      by (simp add: role_wf_def)
  qed
  have ready_payload:
    "\<And>p u. p < 4 \<Longrightarrow>
       u \<in> generic_task_set
         (((sa_ready s)
           (?p0 := list_insert_end_abs (Generic t) ?k
             (sa_ready s ?p0))) p) \<Longrightarrow>
       sa_priority s u = p"
  proof -
    fix p :: nat and u
    assume p_bound: "p < 4"
    assume membership:
      "u \<in> generic_task_set
         (((sa_ready s)
           (?p0 := list_insert_end_abs (Generic t) ?k
             (sa_ready s ?p0))) p)"
    show "sa_priority s u = p"
    proof (cases "p = ?p0")
      case True
      have expanded:
        "u \<in> insert t (generic_task_set (sa_ready s ?p0))"
        using membership True
          generic_task_set_insert_end[OF wf_ready[OF pri_t]]
        by simp
      show ?thesis
        using expanded roles pri_t True
        by (auto simp: role_wf_def)
    next
      case False
      show ?thesis
        using membership False p_bound roles
        by (auto simp: role_wf_def)
    qed
  qed
  have ready_ring_primed:
    "\<And>p. p < 4 \<Longrightarrow>
       generic_ring (sa_ready (resume_one_pending_abs t s) p)"
  proof -
    fix p :: nat
    assume p4: "p < 4"
    have old: "generic_ring (sa_ready s p)"
      using roles p4 by (simp add: role_wf_def)
    show "generic_ring (sa_ready (resume_one_pending_abs t s) p)"
    proof (cases "p = ?p0")
      case True
      have "generic_ring (list_insert_end_abs (Generic t) ?k
         (sa_ready s ?p0))"
        by (rule generic_ring_insert_end[OF wf_ready[OF pri_t]])
           (use old True in simp)
      then show ?thesis using True by (simp add: eq)
    next
      case False
      then show ?thesis using old by (simp add: eq)
    qed
  qed
  have ready_payload_primed:
    "\<And>p u. p < 4 \<Longrightarrow>
       u \<in> generic_task_set
         (sa_ready (resume_one_pending_abs t s) p) \<Longrightarrow>
       sa_priority (resume_one_pending_abs t s) u = p"
  proof -
    fix p :: nat and u
    assume p4: "p < 4"
    assume mem:
      "u \<in> generic_task_set
         (sa_ready (resume_one_pending_abs t s) p)"
    have mem':
      "u \<in> generic_task_set
         (((sa_ready s)
           (?p0 := list_insert_end_abs (Generic t) ?k
             (sa_ready s ?p0))) p)"
      using mem by (simp add: eq)
    have "sa_priority s u = p"
      by (rule ready_payload[OF p4 mem'])
    then show "sa_priority (resume_one_pending_abs t s) u = p"
      by (simp add: eq)
  qed
  have delayed_a_primed:
    "generic_ring (sa_delayed_a (resume_one_pending_abs t s))"
  proof -
    have base: "generic_ring (sa_delayed_a s)"
      using roles by (simp add: role_wf_def)
    have "generic_ring (list_remove_abs (Generic t) (sa_delayed_a s))"
      by (rule generic_ring_remove[OF base])
    then show ?thesis by (simp add: eq)
  qed
  have delayed_b_primed:
    "generic_ring (sa_delayed_b (resume_one_pending_abs t s))"
  proof -
    have base: "generic_ring (sa_delayed_b s)"
      using roles by (simp add: role_wf_def)
    have "generic_ring (list_remove_abs (Generic t) (sa_delayed_b s))"
      by (rule generic_ring_remove[OF base])
    then show ?thesis by (simp add: eq)
  qed
  have pending_ring_primed:
    "event_ring (sa_pending (resume_one_pending_abs t s))"
  proof -
    have base: "event_ring (sa_pending s)"
      using roles by (simp add: role_wf_def)
    have "event_ring (list_remove_abs (Event t) (sa_pending s))"
      by (rule event_ring_remove[OF base])
    then show ?thesis by (simp add: eq)
  qed
  have susp_ring_primed:
    "generic_ring (sa_suspended (resume_one_pending_abs t s))"
  proof -
    have base: "generic_ring (sa_suspended s)"
      using roles by (simp add: role_wf_def)
    have "generic_ring (list_remove_abs (Generic t) (sa_suspended s))"
      by (rule generic_ring_remove[OF base])
    then show ?thesis by (simp add: eq)
  qed
  have da_cursor_primed:
    "cursor (sa_delayed_a (resume_one_pending_abs t s)) = None"
    using delayed_a_cursor by (simp add: eq)
  have db_cursor_primed:
    "cursor (sa_delayed_b (resume_one_pending_abs t s)) = None"
    using delayed_b_cursor by (simp add: eq)
  have pending_tail_primed:
    "tail_cursor_wf (sa_pending (resume_one_pending_abs t s))"
    using pending_tail by (simp add: eq)
  have susp_tail_primed:
    "tail_cursor_wf (sa_suspended (resume_one_pending_abs t s))"
    using susp_tail by (simp add: eq)
  have role':
    "role_wf (resume_one_pending_abs t s)"
    unfolding role_wf_def
    using ready_ring_primed ready_payload_primed delayed_a_primed
      delayed_b_primed pending_ring_primed susp_ring_primed
      da_cursor_primed db_cursor_primed pending_tail_primed
      susp_tail_primed
    by blast

  have distinct_da: "distinct (ring (sa_delayed_a s))"
    using wf_da by (simp add: xlist_wf_def)
  have distinct_db: "distinct (ring (sa_delayed_b s))"
    using wf_db by (simp add: xlist_wf_def)
  have distinct_susp: "distinct (ring (sa_suspended s))"
    using wf_susp by (simp add: xlist_wf_def)
  have distinct_pending: "distinct (ring (sa_pending s))"
    using wf_pending by (simp add: xlist_wf_def)
  note set_eqs =
    generic_task_set_remove[OF distinct_da]
    generic_task_set_remove[OF distinct_db]
    generic_task_set_remove[OF distinct_susp]
    event_task_set_remove[OF distinct_pending]
    generic_task_set_insert_end[OF wf_ready[OF pri_t]]

  have ready_sets:
    "ready_task_set (resume_one_pending_abs t s) =
       insert t (ready_task_set s)"
  proof -
    have per_p:
      "\<And>p. generic_task_set
         (sa_ready (resume_one_pending_abs t s) p) =
         (if p = ?p0
          then insert t (generic_task_set (sa_ready s p))
          else generic_task_set (sa_ready s p))"
      using generic_task_set_insert_end[OF wf_ready[OF pri_t]]
      by (simp add: eq)
    show ?thesis
      unfolding ready_task_set_def
      using pri_t
      by (auto simp: per_p split: if_splits)
  qed

  have members':
    "membership_wf (resume_one_pending_abs t s)"
  proof -
    have old:
      "ready_task_set s \<union>
         generic_task_set (sa_delayed_a s) \<union>
         generic_task_set (sa_delayed_b s) \<union>
         generic_task_set (sa_suspended s) = sa_live s"
      "ready_task_set s \<inter> generic_task_set (sa_delayed_a s) = {}"
      "ready_task_set s \<inter> generic_task_set (sa_delayed_b s) = {}"
      "ready_task_set s \<inter> generic_task_set (sa_suspended s) = {}"
      "generic_task_set (sa_delayed_a s) \<inter>
         generic_task_set (sa_delayed_b s) = {}"
      "generic_task_set (sa_delayed_a s) \<inter>
         generic_task_set (sa_suspended s) = {}"
      "generic_task_set (sa_delayed_b s) \<inter>
         generic_task_set (sa_suspended s) = {}"
      "event_task_set (sa_pending s) \<subseteq> sa_live s"
      "sa_event_waiting s \<subseteq> sa_live s"
      "event_task_set (sa_pending s) \<inter> sa_event_waiting s = {}"
      "event_task_set (sa_pending s) \<subseteq>
         generic_task_set (sa_delayed_a s) \<union>
         generic_task_set (sa_delayed_b s) \<union>
         generic_task_set (sa_suspended s)"
      "ready_task_set s \<inter> sa_event_waiting s = {}"
      using members by (auto simp: membership_wf_def Let_def)
    have live_p: "sa_live (resume_one_pending_abs t s) = sa_live s"
      by (simp add: eq)
    have ew_p:
      "sa_event_waiting (resume_one_pending_abs t s) =
         sa_event_waiting s - {t}"
      by (simp add: eq)
    have a_p:
      "generic_task_set (sa_delayed_a (resume_one_pending_abs t s)) =
         generic_task_set (sa_delayed_a s) - {t}"
      by (simp add: eq generic_task_set_remove[OF distinct_da])
    have b_p:
      "generic_task_set (sa_delayed_b (resume_one_pending_abs t s)) =
         generic_task_set (sa_delayed_b s) - {t}"
      by (simp add: eq generic_task_set_remove[OF distinct_db])
    have s_p:
      "generic_task_set (sa_suspended (resume_one_pending_abs t s)) =
         generic_task_set (sa_suspended s) - {t}"
      by (simp add: eq generic_task_set_remove[OF distinct_susp])
    have p_p:
      "event_task_set (sa_pending (resume_one_pending_abs t s)) =
         event_task_set (sa_pending s) - {t}"
      by (simp add: eq event_task_set_remove[OF distinct_pending])
    show ?thesis
      unfolding membership_wf_def Let_def
      unfolding ready_sets live_p ew_p a_p b_p s_p p_p
      using old live_t by auto
  qed

  have current_ring_eq:
    "current_delayed_ring (resume_one_pending_abs t s) =
       list_remove_abs (Generic t) (current_delayed_ring s)"
    by (simp add: current_delayed_ring_def eq)
  have overflow_ring_eq:
    "overflow_delayed_ring (resume_one_pending_abs t s) =
       list_remove_abs (Generic t) (overflow_delayed_ring s)"
    by (simp add: overflow_delayed_ring_def eq)
  have current_ring_distinct: "distinct (ring (current_delayed_ring s))"
    using distinct_da distinct_db
    by (simp add: current_delayed_ring_def)
  have overflow_ring_distinct:
    "distinct (ring (overflow_delayed_ring s))"
    using distinct_da distinct_db
    by (simp add: overflow_delayed_ring_def)

  have time':
    "time_wf (resume_one_pending_abs t s)"
  proof -
    have agree_a:
      "delayed_key_agrees (resume_one_pending_abs t s)
         (sa_delayed_a (resume_one_pending_abs t s))"
      using time
      by (auto simp: time_wf_def delayed_key_agrees_def eq
          item_key_remove generic_task_set_remove[OF distinct_da])
    have agree_b:
      "delayed_key_agrees (resume_one_pending_abs t s)
         (sa_delayed_b (resume_one_pending_abs t s))"
      using time
      by (auto simp: time_wf_def delayed_key_agrees_def eq
          item_key_remove generic_task_set_remove[OF distinct_db])
    have sorted_a:
      "sorted (map (item_key
         (sa_delayed_a (resume_one_pending_abs t s)))
         (ring (sa_delayed_a (resume_one_pending_abs t s))))"
      using time
      by (simp add: time_wf_def eq item_key_remove
          list_remove_abs_def sorted_map_remove1)
    have sorted_b:
      "sorted (map (item_key
         (sa_delayed_b (resume_one_pending_abs t s)))
         (ring (sa_delayed_b (resume_one_pending_abs t s))))"
      using time
      by (simp add: time_wf_def eq item_key_remove
          list_remove_abs_def sorted_map_remove1)
    have none:
      "\<forall>u \<in> ready_task_set (resume_one_pending_abs t s) \<union>
         generic_task_set
           (sa_suspended (resume_one_pending_abs t s)).
         sa_wake (resume_one_pending_abs t s) u = None"
      using time ready_sets
      by (auto simp: time_wf_def eq
          generic_task_set_remove[OF distinct_susp])
    have current_cond:
      "\<forall>u \<in> generic_task_set
         (current_delayed_ring (resume_one_pending_abs t s)).
         case sa_wake (resume_one_pending_abs t s) u of
           None \<Rightarrow> False
         | Some k \<Rightarrow> sa_tick (resume_one_pending_abs t s) < k"
      using time
      by (auto simp: time_wf_def current_delayed_ring_def eq
          generic_task_set_remove[OF distinct_da]
          generic_task_set_remove[OF distinct_db]
          split: if_splits option.splits)
    have overflow_cond:
      "\<forall>u \<in> generic_task_set
         (overflow_delayed_ring (resume_one_pending_abs t s)).
         case sa_wake (resume_one_pending_abs t s) u of
           None \<Rightarrow> False
         | Some k \<Rightarrow> k < sa_tick (resume_one_pending_abs t s)"
      using time
      by (auto simp: time_wf_def overflow_delayed_ring_def eq
          generic_task_set_remove[OF distinct_da]
          generic_task_set_remove[OF distinct_db]
          split: if_splits option.splits)
    show ?thesis
      unfolding time_wf_def
      using agree_a agree_b sorted_a sorted_b none current_cond
        overflow_cond by blast
  qed

  have cache':
    "ready_cache_wf (resume_one_pending_abs t s)"
  proof -
    have top_bound: "sa_top_ready s < 4"
      using cache by (simp add: ready_cache_wf_def)
    have inserted_nonempty:
      "ring (list_insert_end_abs (Generic t) ?k
         (sa_ready s ?p0)) \<noteq> []"
      using ring_set_insert_end[OF wf_ready[OF pri_t]]
      by (metis empty_set insert_not_empty)
    show ?thesis
      using cache top_bound pri_t inserted_nonempty
      unfolding ready_cache_wf_def eq
      by (auto simp: ready_cache_wf_def max_def)
  qed

  have current':
    "current_wf (resume_one_pending_abs t s)"
    using wf
    by (simp add: core_wf_def current_wf_def eq
        split: option.splits)

  show ?thesis
    unfolding core_wf_def
    using wf shape' role' members' time' cache' current'
    by (simp add: core_wf_def eq)
qed

end
