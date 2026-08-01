theory Scheduler_Abstract_Model
  imports
    "EAL6_FreeRTOS_V611_Model.XList_Model_Definitions"
    "HOL-Library.Word"
begin

text \<open>
  First pure scheduler-model draft, reconstructed from the frozen FreeRTOS
  V6.1.1 source and independent executable traces.  This theory deliberately
  contains no raw heap, TCB pointer, port implementation, or generated C
  program.  In particular, a task owner is not a list-node identity.
\<close>

datatype 'tid node_kind =
    Generic 'tid
  | Event 'tid

fun node_owner :: "'tid node_kind \<Rightarrow> 'tid" where
  "node_owner (Generic t) = t"
| "node_owner (Event t) = t"

lemma generic_event_are_distinct_nodes [simp]:
  "Generic t \<noteq> Event u"
  by simp

lemma same_task_has_two_nodes:
  "node_owner (Generic t) = node_owner (Event t) \<and>
   Generic t \<noteq> Event t"
  by simp

type_synonym 'tid node_ring = "('tid node_kind, 32 word) xlist_abs"

definition empty_node_ring :: "'tid node_ring" where
  "empty_node_ring =
     \<lparr>ring = [], cursor = None, item_key = (\<lambda>_. 0)\<rparr>"

definition rotate_after :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "rotate_after c xs =
     (case dropWhile (\<lambda>x. x \<noteq> c) xs of
        [] \<Rightarrow> xs
      | z # ys \<Rightarrow> ys @ takeWhile (\<lambda>x. x \<noteq> c) xs @ [c])"

definition ready_node_order :: "'tid node_ring \<Rightarrow> 'tid node_kind list" where
  "ready_node_order q =
     (case cursor q of
        None \<Rightarrow> ring q
      | Some c \<Rightarrow> rotate_after c (ring q))"

definition ready_task_order :: "'tid node_ring \<Rightarrow> 'tid list" where
  "ready_task_order q = map node_owner (ready_node_order q)"

definition advance_ready_ring :: "'tid node_ring \<Rightarrow> 'tid node_ring" where
  "advance_ready_ring q =
     (case ready_node_order q of
        [] \<Rightarrow> q
      | n # ns \<Rightarrow> q\<lparr>cursor := Some n\<rparr>)"

lemma advance_ready_ring_frames_ring [simp]:
  "ring (advance_ready_ring q) = ring q"
  unfolding advance_ready_ring_def
  by (cases "ready_node_order q") simp_all

lemma advance_ready_ring_frames_keys [simp]:
  "item_key (advance_ready_ring q) = item_key q"
  unfolding advance_ready_ring_def
  by (cases "ready_node_order q") simp_all

lemma advance_ready_ring_selects_head:
  assumes "ready_node_order q = n # ns"
  shows "cursor (advance_ready_ring q) = Some n"
  using assms unfolding advance_ready_ring_def by simp

definition ready_abc :: "nat node_ring" where
  "ready_abc =
     \<lparr>ring = [Generic 1, Generic 2, Generic 3],
       cursor = Some (Generic 3),
       item_key = (\<lambda>_. 0)\<rparr>"

value "ready_node_order ready_abc"
value "cursor (advance_ready_ring ready_abc)"

lemma ready_abc_order:
  "ready_node_order ready_abc =
     [Generic 1, Generic 2, Generic 3]"
  by (simp add: ready_abc_def ready_node_order_def rotate_after_def)

lemma ready_abc_first_advance:
  "cursor (advance_ready_ring ready_abc) = Some (Generic 1)"
  by (simp add: advance_ready_ring_def ready_abc_order)

record 'tid scheduler_abs =
  sa_live :: "'tid set"
  sa_priority :: "'tid \<Rightarrow> nat"
  sa_wake :: "'tid \<Rightarrow> 32 word option"
  sa_event_waiting :: "'tid set"
  sa_ready :: "nat \<Rightarrow> 'tid node_ring"
  sa_delayed_a :: "'tid node_ring"
  sa_delayed_b :: "'tid node_ring"
  sa_current_role_a :: bool
  sa_pending :: "'tid node_ring"
  sa_suspended :: "'tid node_ring"
  sa_tick :: "32 word"
  sa_missed_ticks :: nat
  sa_suspend_depth :: nat
  sa_missed_yield :: bool
  sa_top_ready :: nat
  sa_current :: "'tid option"
  sa_overflows :: nat
  sa_yield_count :: nat

definition current_delayed_ring ::
  "'tid scheduler_abs \<Rightarrow> 'tid node_ring"
where
  "current_delayed_ring s =
     (if sa_current_role_a s then sa_delayed_a s else sa_delayed_b s)"

definition overflow_delayed_ring ::
  "'tid scheduler_abs \<Rightarrow> 'tid node_ring"
where
  "overflow_delayed_ring s =
     (if sa_current_role_a s then sa_delayed_b s else sa_delayed_a s)"

definition put_current_delayed ::
  "'tid node_ring \<Rightarrow> 'tid scheduler_abs \<Rightarrow> 'tid scheduler_abs"
where
  "put_current_delayed q s =
     (if sa_current_role_a s
      then s\<lparr>sa_delayed_a := q\<rparr>
      else s\<lparr>sa_delayed_b := q\<rparr>)"

definition put_overflow_delayed ::
  "'tid node_ring \<Rightarrow> 'tid scheduler_abs \<Rightarrow> 'tid scheduler_abs"
where
  "put_overflow_delayed q s =
     (if sa_current_role_a s
      then s\<lparr>sa_delayed_b := q\<rparr>
      else s\<lparr>sa_delayed_a := q\<rparr>)"

definition swap_delayed_roles ::
  "'tid scheduler_abs \<Rightarrow> 'tid scheduler_abs"
where
  "swap_delayed_roles s =
     s\<lparr>sa_current_role_a := \<not> sa_current_role_a s,
       sa_overflows := Suc (sa_overflows s)\<rparr>"

lemma current_delayed_after_role_swap:
  "current_delayed_ring (swap_delayed_roles s) = overflow_delayed_ring s"
  unfolding current_delayed_ring_def overflow_delayed_ring_def
    swap_delayed_roles_def
  by simp

lemma overflow_delayed_after_role_swap:
  "overflow_delayed_ring (swap_delayed_roles s) = current_delayed_ring s"
  unfolding current_delayed_ring_def overflow_delayed_ring_def
    swap_delayed_roles_def
  by simp

lemma role_swap_frames_physical_rings [simp]:
  "sa_delayed_a (swap_delayed_roles s) = sa_delayed_a s \<and>
   sa_delayed_b (swap_delayed_roles s) = sa_delayed_b s"
  unfolding swap_delayed_roles_def by simp

definition generic_ring :: "'tid node_ring \<Rightarrow> bool" where
  "generic_ring q \<longleftrightarrow>
     (\<forall>n \<in> set (ring q). \<exists>t. n = Generic t)"

definition event_ring :: "'tid node_ring \<Rightarrow> bool" where
  "event_ring q \<longleftrightarrow>
     (\<forall>n \<in> set (ring q). \<exists>t. n = Event t)"

definition generic_task_set :: "'tid node_ring \<Rightarrow> 'tid set" where
  "generic_task_set q = {t. Generic t \<in> set (ring q)}"

definition event_task_set :: "'tid node_ring \<Rightarrow> 'tid set" where
  "event_task_set q = {t. Event t \<in> set (ring q)}"

definition ready_task_set :: "'tid scheduler_abs \<Rightarrow> 'tid set" where
  "ready_task_set s =
     (\<Union>p \<in> {0..<4}. generic_task_set (sa_ready s p))"

definition physical_delayed_task_set ::
  "'tid scheduler_abs \<Rightarrow> 'tid set"
where
  "physical_delayed_task_set s =
     generic_task_set (sa_delayed_a s) \<union>
     generic_task_set (sa_delayed_b s)"

definition tail_cursor_wf :: "'tid node_ring \<Rightarrow> bool" where
  "tail_cursor_wf q \<longleftrightarrow>
     (if ring q = []
      then cursor q = None
      else cursor q = Some (last (ring q)))"

definition ring_shape_wf :: "'tid scheduler_abs \<Rightarrow> bool" where
  "ring_shape_wf s \<longleftrightarrow>
     (\<forall>p<4. xlist_wf (sa_ready s p)) \<and>
     xlist_wf (sa_delayed_a s) \<and>
     xlist_wf (sa_delayed_b s) \<and>
     xlist_wf (sa_pending s) \<and>
     xlist_wf (sa_suspended s)"

definition role_wf :: "'tid scheduler_abs \<Rightarrow> bool" where
  "role_wf s \<longleftrightarrow>
     (\<forall>p<4.
        generic_ring (sa_ready s p) \<and>
        (\<forall>t \<in> generic_task_set (sa_ready s p).
           sa_priority s t = p)) \<and>
     generic_ring (sa_delayed_a s) \<and>
     generic_ring (sa_delayed_b s) \<and>
     event_ring (sa_pending s) \<and>
     generic_ring (sa_suspended s) \<and>
     cursor (sa_delayed_a s) = None \<and>
     cursor (sa_delayed_b s) = None \<and>
     tail_cursor_wf (sa_pending s) \<and>
     tail_cursor_wf (sa_suspended s)"

definition membership_wf :: "'tid scheduler_abs \<Rightarrow> bool" where
  "membership_wf s \<longleftrightarrow>
     (let R = ready_task_set s;
          A = generic_task_set (sa_delayed_a s);
          B = generic_task_set (sa_delayed_b s);
          S = generic_task_set (sa_suspended s);
          P = event_task_set (sa_pending s)
      in R \<union> A \<union> B \<union> S = sa_live s \<and>
         R \<inter> A = {} \<and> R \<inter> B = {} \<and> R \<inter> S = {} \<and>
         A \<inter> B = {} \<and> A \<inter> S = {} \<and> B \<inter> S = {} \<and>
         P \<subseteq> sa_live s \<and>
         sa_event_waiting s \<subseteq> sa_live s \<and>
         P \<inter> sa_event_waiting s = {} \<and>
         P \<subseteq> A \<union> B \<union> S \<and>
         R \<inter> sa_event_waiting s = {})"

definition delayed_key_agrees ::
  "'tid scheduler_abs \<Rightarrow> 'tid node_ring \<Rightarrow> bool"
where
  "delayed_key_agrees s q \<longleftrightarrow>
     (\<forall>t \<in> generic_task_set q.
        sa_wake s t = Some (item_key q (Generic t)))"

definition time_wf :: "'tid scheduler_abs \<Rightarrow> bool" where
  "time_wf s \<longleftrightarrow>
     delayed_key_agrees s (sa_delayed_a s) \<and>
     delayed_key_agrees s (sa_delayed_b s) \<and>
     sorted (map (item_key (sa_delayed_a s)) (ring (sa_delayed_a s))) \<and>
     sorted (map (item_key (sa_delayed_b s)) (ring (sa_delayed_b s))) \<and>
     (\<forall>t \<in> ready_task_set s \<union>
                  generic_task_set (sa_suspended s).
        sa_wake s t = None) \<and>
     (\<forall>t \<in> generic_task_set (current_delayed_ring s).
        case sa_wake s t of
          None \<Rightarrow> False
        | Some k \<Rightarrow> sa_tick s < k) \<and>
     (\<forall>t \<in> generic_task_set (overflow_delayed_ring s).
        case sa_wake s t of
          None \<Rightarrow> False
        | Some k \<Rightarrow> k < sa_tick s)"

definition ready_cache_wf :: "'tid scheduler_abs \<Rightarrow> bool" where
  "ready_cache_wf s \<longleftrightarrow>
     sa_top_ready s < 4 \<and>
     (\<forall>p<4. ring (sa_ready s p) \<noteq> [] \<longrightarrow>
        p \<le> sa_top_ready s) \<and>
     (\<exists>p<4. p \<le> sa_top_ready s \<and>
        ring (sa_ready s p) \<noteq> [])"

definition current_wf :: "'tid scheduler_abs \<Rightarrow> bool" where
  "current_wf s \<longleftrightarrow>
     (case sa_current s of
        None \<Rightarrow> True
      | Some t \<Rightarrow> t \<in> sa_live s)"

definition core_wf :: "'tid scheduler_abs \<Rightarrow> bool" where
  "core_wf s \<longleftrightarrow>
     finite (sa_live s) \<and>
     (\<forall>t \<in> sa_live s. sa_priority s t < 4) \<and>
     ring_shape_wf s \<and>
     role_wf s \<and>
     membership_wf s \<and>
     time_wf s \<and>
     ready_cache_wf s \<and>
     current_wf s"

definition settled_wf :: "'tid scheduler_abs \<Rightarrow> bool" where
  "settled_wf s \<longleftrightarrow>
     core_wf s \<and>
     sa_suspend_depth s = 0 \<and>
     sa_missed_ticks s = 0 \<and>
     ring (sa_pending s) = [] \<and>
     ring (sa_ready s (sa_top_ready s)) \<noteq> [] \<and>
     (case sa_current s of
        None \<Rightarrow> False
      | Some t \<Rightarrow>
          Generic t \<in> set (ring (sa_ready s (sa_priority s t))))"

lemma settled_wf_imp_core_wf:
  "settled_wf s \<Longrightarrow> core_wf s"
  unfolding settled_wf_def by simp

lemma core_wf_current_is_live:
  assumes "core_wf s" "sa_current s = Some t"
  shows "t \<in> sa_live s"
  using assms unfolding core_wf_def current_wf_def by simp

definition request_yield ::
  "'tid scheduler_abs \<Rightarrow> 'tid scheduler_abs"
where
  "request_yield s =
     s\<lparr>sa_yield_count := Suc (sa_yield_count s)\<rparr>"

fun add_ready_node ::
  "'tid node_kind \<Rightarrow> 'tid scheduler_abs \<Rightarrow>
   'tid scheduler_abs"
where
  "add_ready_node (Event t) s = s"
| "add_ready_node (Generic t) s =
     (let p = sa_priority s t;
          q = sa_ready s p;
          k = (case sa_wake s t of None \<Rightarrow> 0 | Some w \<Rightarrow> w)
      in s\<lparr>
           sa_ready := (sa_ready s)
             (p := list_insert_end_abs (Generic t) k q),
           sa_wake := (sa_wake s)(t := None),
           sa_event_waiting := sa_event_waiting s - {t},
           sa_top_ready := max (sa_top_ready s) p
         \<rparr>)"

lemma add_ready_node_frames_current [simp]:
  "sa_current (add_ready_node n s) = sa_current s"
  by (cases n) (simp_all add: Let_def)

definition block_task_at ::
  "32 word \<Rightarrow> 'tid \<Rightarrow> 'tid scheduler_abs \<Rightarrow>
   'tid scheduler_abs"
where
  "block_task_at wake t s =
     (let p = sa_priority s t;
          rq = sa_ready s p;
          rq' = list_remove_abs (Generic t) rq;
          s1 = s\<lparr>
                 sa_ready := (sa_ready s)(p := rq'),
                 sa_wake := (sa_wake s)(t := Some wake)
               \<rparr>;
          dq = (if wake < sa_tick s
                then overflow_delayed_ring s1
                else current_delayed_ring s1);
          dq' = list_insert_ordered_abs (Generic t) wake dq
      in if wake < sa_tick s
         then put_overflow_delayed dq' s1
         else put_current_delayed dq' s1)"

definition task_delay_abs ::
  "32 word \<Rightarrow> 'tid scheduler_abs \<Rightarrow> 'tid scheduler_abs"
where
  "task_delay_abs ticks s =
     (if ticks = 0
      then request_yield s
      else
        (case sa_current s of
           None \<Rightarrow> request_yield s
         | Some t \<Rightarrow>
             request_yield (block_task_at (sa_tick s + ticks) t s)))"

definition should_delay_until ::
  "32 word \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> bool"
where
  "should_delay_until now previous wake \<longleftrightarrow>
     (if now < previous
      then wake < previous \<and> now < wake
      else wake < previous \<or> now < wake)"

definition task_delay_until_abs ::
  "32 word \<Rightarrow> 32 word \<Rightarrow> 'tid scheduler_abs \<Rightarrow>
   32 word \<times> 'tid scheduler_abs"
where
  "task_delay_until_abs previous increment s =
     (let wake = previous + increment;
          s1 = (if should_delay_until (sa_tick s) previous wake
                then
                  (case sa_current s of
                     None \<Rightarrow> s
                   | Some t \<Rightarrow> block_task_at wake t s)
                else s)
      in (wake, request_yield s1))"

definition task_get_tick_abs ::
  "'tid scheduler_abs \<Rightarrow> 32 word \<times> 'tid scheduler_abs"
where
  "task_get_tick_abs s = (sa_tick s, s)"

definition due_nodes ::
  "32 word \<Rightarrow> 'tid node_ring \<Rightarrow> 'tid node_kind list"
where
  "due_nodes now q =
     takeWhile (\<lambda>n. item_key q n \<le> now) (ring q)"

definition remove_nodes ::
  "'tid node_kind list \<Rightarrow> 'tid node_ring \<Rightarrow> 'tid node_ring"
where
  "remove_nodes ns q = fold list_remove_abs ns q"

definition tick_unlocked_abs ::
  "'tid scheduler_abs \<Rightarrow> 'tid scheduler_abs"
where
  "tick_unlocked_abs s =
     (let next = sa_tick s + 1;
          s0 = s\<lparr>sa_tick := next\<rparr>;
          s1 = (if next = 0 then swap_delayed_roles s0 else s0);
          q = current_delayed_ring s1;
          due = due_nodes next q;
          q' = remove_nodes due q;
          s2 = put_current_delayed q' s1
      in fold add_ready_node due s2)"

definition task_increment_tick_abs ::
  "'tid scheduler_abs \<Rightarrow> 'tid scheduler_abs"
where
  "task_increment_tick_abs s =
     (if sa_suspend_depth s = 0
      then tick_unlocked_abs s
      else s\<lparr>sa_missed_ticks := Suc (sa_missed_ticks s)\<rparr>)"

fun find_ready_from ::
  "nat \<Rightarrow> (nat \<Rightarrow> 'tid node_ring) \<Rightarrow> nat"
where
  "find_ready_from 0 qs = 0"
| "find_ready_from (Suc p) qs =
     (if ring (qs (Suc p)) = []
      then find_ready_from p qs
      else Suc p)"

definition switch_at ::
  "nat \<Rightarrow> 'tid scheduler_abs \<Rightarrow> 'tid scheduler_abs"
where
  "switch_at p s =
     (let q = sa_ready s p
      in case ready_node_order q of
           [] \<Rightarrow> s
         | n # ns \<Rightarrow>
             s\<lparr>
               sa_ready := (sa_ready s)(p := q\<lparr>cursor := Some n\<rparr>),
               sa_top_ready := p,
               sa_current := Some (node_owner n)
             \<rparr>)"

definition task_switch_context_abs ::
  "'tid scheduler_abs \<Rightarrow> 'tid scheduler_abs"
where
  "task_switch_context_abs s =
     (if sa_suspend_depth s \<noteq> 0
      then s\<lparr>sa_missed_yield := True\<rparr>
      else switch_at (find_ready_from (sa_top_ready s) (sa_ready s)) s)"

lemma task_get_tick_abs_result [simp]:
  "fst (task_get_tick_abs s) = sa_tick s"
  unfolding task_get_tick_abs_def by simp

lemma task_get_tick_abs_frames_state [simp]:
  "snd (task_get_tick_abs s) = s"
  unfolding task_get_tick_abs_def by simp

lemma task_delay_zero:
  "task_delay_abs 0 s = request_yield s"
  unfolding task_delay_abs_def by simp

lemma task_delay_until_commits_nominal_wake:
  "fst (task_delay_until_abs previous increment s) =
   previous + increment"
  unfolding task_delay_until_abs_def by (simp add: Let_def)

lemma task_increment_tick_while_suspended:
  assumes "sa_suspend_depth s \<noteq> 0"
  shows "task_increment_tick_abs s =
         s\<lparr>sa_missed_ticks := Suc (sa_missed_ticks s)\<rparr>"
  using assms unfolding task_increment_tick_abs_def by simp

lemma task_switch_context_while_suspended:
  assumes "sa_suspend_depth s \<noteq> 0"
  shows "task_switch_context_abs s =
         s\<lparr>sa_missed_yield := True\<rparr>"
  using assms unfolding task_switch_context_abs_def by simp

value "should_delay_until (12 :: 32 word) 10 11"
value "should_delay_until (4294967293 :: 32 word) 4294967292 1"

definition example_scheduler :: "nat scheduler_abs" where
  "example_scheduler =
     \<lparr>
       sa_live = {1, 2, 3},
       sa_priority = (\<lambda>_. 2),
       sa_wake = (\<lambda>_. None),
       sa_event_waiting = {},
       sa_ready = (\<lambda>p. if p = 2 then ready_abc else empty_node_ring),
       sa_delayed_a = empty_node_ring,
       sa_delayed_b = empty_node_ring,
       sa_current_role_a = True,
       sa_pending = empty_node_ring,
       sa_suspended = empty_node_ring,
       sa_tick = 42,
       sa_missed_ticks = 0,
       sa_suspend_depth = 0,
       sa_missed_yield = False,
       sa_top_ready = 2,
       sa_current = Some 1,
       sa_overflows = 0,
       sa_yield_count = 0
     \<rparr>"

value "sa_current (task_switch_context_abs example_scheduler)"
value "sa_current
  (task_switch_context_abs (task_switch_context_abs example_scheduler))"
value "sa_tick
  (task_increment_tick_abs
    (example_scheduler\<lparr>sa_tick := 4294967295\<rparr>))"
value "sa_current_role_a
  (task_increment_tick_abs
    (example_scheduler\<lparr>sa_tick := 4294967295\<rparr>))"

text \<open>
  The five root functions above are pure endpoint models.  The two delay
  functions intentionally describe the quiescent API-boundary case: they
  collapse the internal suspend/resume pair to one yield request.  Pending
  ready draining, missed-tick replay, external event-list order, finite C
  counter bounds, and the raw representation relation remain later layers.
\<close>

end
