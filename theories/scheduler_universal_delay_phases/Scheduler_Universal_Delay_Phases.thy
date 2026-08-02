theory Scheduler_Universal_Delay_Phases
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Abstract_Model.Scheduler_Abstract_Model"
begin

text \<open>
  Proof-only phase model for a positive-delay transaction.  The model is
  independent of the generated-loop and raw ownership developments.  Its
  contexts and snapshots quantify over arbitrary finite live sets, bounded
  priority maps, root identities, ready-ring cursors, delayed-ring contents,
  ticks, and delays.  The phase constructors are logical cutpoints, not
  runtime FreeRTOS state.
\<close>

datatype delay_resume_path =
    DelayInternalYield
  | DelayOuterYieldRequired

datatype 'root delay_txn_phase =
    DelayReady
  | DelayUnlinked
  | DelayKeyed
  | DelaySelected 'root
  | DelayInserted
  | DelayResumed delay_resume_path
  | DelayYieldPending

record ('tid, 'root) delay_txn_context =
  dt_live :: "'tid set"
  dt_priority_levels :: nat
  dt_suspension_depth :: nat
  dt_priority :: "'tid \<Rightarrow> nat"
  dt_task :: 'tid
  dt_roots :: "'root set"
  dt_ready_root :: "nat \<Rightarrow> 'root"
  dt_current_root :: 'root
  dt_overflow_root :: 'root
  dt_tick :: "32 word"
  dt_delay :: "32 word"

record ('tid, 'root) delay_txn_snapshot =
  ds_ready :: "nat \<Rightarrow> 'tid node_ring"
  ds_current_delayed :: "'tid node_ring"
  ds_overflow_delayed :: "'tid node_ring"
  ds_members :: "'root \<Rightarrow> 'tid node_kind set"
  ds_container :: "'tid node_kind \<Rightarrow> 'root option"
  ds_next :: "'tid node_kind option \<Rightarrow> 'tid node_kind option"
  ds_previous :: "'tid node_kind option \<Rightarrow> 'tid node_kind option"
  ds_wake :: "'tid \<Rightarrow> 32 word option"
  ds_tick :: "32 word"
  ds_top_hint :: nat
  ds_current :: "'tid option"
  ds_scheduler_suspended :: nat
  ds_pending_ready :: "'tid node_ring"
  ds_missed_ticks :: nat
  ds_missed_yield :: bool
  ds_yield_count :: nat

definition delay_wake ::
  "('tid, 'root) delay_txn_context \<Rightarrow> 32 word"
where
  "delay_wake C = dt_tick C + dt_delay C"

definition delay_selected_root ::
  "('tid, 'root) delay_txn_context \<Rightarrow> 'root"
where
  "delay_selected_root C =
     (if delay_wake C < dt_tick C
      then dt_overflow_root C
      else dt_current_root C)"

definition delay_context_wf ::
  "('tid, 'root) delay_txn_context \<Rightarrow> bool"
where
  "delay_context_wf C \<longleftrightarrow>
     finite (dt_live C) \<and>
     0 < dt_priority_levels C \<and>
     0 < dt_suspension_depth C \<and>
     dt_task C \<in> dt_live C \<and>
     (\<forall>t\<in>dt_live C.
        dt_priority C t < dt_priority_levels C) \<and>
     finite (dt_roots C) \<and>
     inj_on (dt_ready_root C) {0..<dt_priority_levels C} \<and>
     (\<forall>p<dt_priority_levels C. dt_ready_root C p \<in> dt_roots C) \<and>
     dt_current_root C \<in> dt_roots C \<and>
     dt_overflow_root C \<in> dt_roots C \<and>
     dt_current_root C \<noteq> dt_overflow_root C \<and>
     dt_current_root C \<notin>
       dt_ready_root C ` {0..<dt_priority_levels C} \<and>
     dt_overflow_root C \<notin>
       dt_ready_root C ` {0..<dt_priority_levels C}"

definition delay_snapshot_shape ::
  "('tid, 'root) delay_txn_context \<Rightarrow>
   ('tid, 'root) delay_txn_snapshot \<Rightarrow> bool"
where
  "delay_snapshot_shape C S \<longleftrightarrow>
     (\<forall>p<dt_priority_levels C.
        xlist_wf (ds_ready S p) \<and>
        ds_members S (dt_ready_root C p) = set (ring (ds_ready S p))) \<and>
     xlist_wf (ds_current_delayed S) \<and>
     xlist_wf (ds_overflow_delayed S) \<and>
     xlist_wf (ds_pending_ready S) \<and>
     ds_members S (dt_current_root C) =
       set (ring (ds_current_delayed S)) \<and>
     ds_members S (dt_overflow_root C) =
       set (ring (ds_overflow_delayed S))"

definition delay_globally_unlinked ::
  "('tid, 'root) delay_txn_context \<Rightarrow>
   ('tid, 'root) delay_txn_snapshot \<Rightarrow>
   'tid node_kind \<Rightarrow> bool"
where
  "delay_globally_unlinked C S n \<longleftrightarrow>
     (\<forall>r\<in>dt_roots C. n \<notin> ds_members S r)"

definition delay_container_faithful ::
  "('tid, 'root) delay_txn_context \<Rightarrow>
   ('tid, 'root) delay_txn_snapshot \<Rightarrow> bool"
where
  "delay_container_faithful C S \<longleftrightarrow>
     (\<forall>n r. r \<in> dt_roots C \<longrightarrow>
        (n \<in> ds_members S r \<longleftrightarrow>
         ds_container S n = Some r)) \<and>
     (\<forall>n r. ds_container S n = Some r \<longrightarrow>
        r \<in> dt_roots C)"

definition delay_stable_ownership ::
  "('tid, 'root) delay_txn_context \<Rightarrow>
   ('tid, 'root) delay_txn_snapshot \<Rightarrow> bool"
where
  "delay_stable_ownership C S \<longleftrightarrow>
     delay_container_faithful C S \<and>
     (\<forall>t\<in>dt_live C.
        \<exists>!r. r \<in> dt_roots C \<and>
             Generic t \<in> ds_members S r)"

definition delay_transit_ownership ::
  "('tid, 'root) delay_txn_context \<Rightarrow>
   ('tid, 'root) delay_txn_snapshot \<Rightarrow> bool"
where
  "delay_transit_ownership C S \<longleftrightarrow>
     delay_container_faithful C S \<and>
     dt_task C \<in> dt_live C \<and>
     ds_container S (Generic (dt_task C)) = None \<and>
     delay_globally_unlinked C S (Generic (dt_task C)) \<and>
     (\<forall>t\<in>dt_live C - {dt_task C}.
        \<exists>!r. r \<in> dt_roots C \<and>
             Generic t \<in> ds_members S r)"

definition delay_nonempty_ready_priorities ::
  "nat \<Rightarrow> (nat \<Rightarrow> 'tid node_ring) \<Rightarrow> nat set"
where
  "delay_nonempty_ready_priorities levels ready =
     {p. p < levels \<and> ring (ready p) \<noteq> []}"

definition delay_max_nonempty_ready ::
  "nat \<Rightarrow> (nat \<Rightarrow> 'tid node_ring) \<Rightarrow> nat"
where
  "delay_max_nonempty_ready levels ready =
     Max (insert 0 (delay_nonempty_ready_priorities levels ready))"

definition delay_ready_upper_bound ::
  "nat \<Rightarrow> (nat \<Rightarrow> 'tid node_ring) \<Rightarrow> nat \<Rightarrow> bool"
where
  "delay_ready_upper_bound levels ready hint \<longleftrightarrow>
     hint < levels \<and>
     (\<forall>p<levels. ring (ready p) \<noteq> [] \<longrightarrow> p \<le> hint)"

definition delay_exact_top_ready ::
  "nat \<Rightarrow> (nat \<Rightarrow> 'tid node_ring) \<Rightarrow> nat \<Rightarrow> bool"
where
  "delay_exact_top_ready levels ready hint \<longleftrightarrow>
     delay_ready_upper_bound levels ready hint \<and>
     ring (ready hint) \<noteq> []"

definition delay_yield_top_hint ::
  "nat \<Rightarrow> (nat \<Rightarrow> 'tid node_ring) \<Rightarrow> nat \<Rightarrow> bool"
where
  "delay_yield_top_hint levels ready hint \<longleftrightarrow>
     delay_max_nonempty_ready levels ready \<le> hint \<and> hint < levels"

definition delay_phase_ownership_ok ::
  "('tid, 'root) delay_txn_context \<Rightarrow>
   'root delay_txn_phase \<Rightarrow>
   ('tid, 'root) delay_txn_snapshot \<Rightarrow> bool"
where
  "delay_phase_ownership_ok C phase S \<longleftrightarrow>
     (case phase of
        DelayReady \<Rightarrow>
          delay_stable_ownership C S \<and>
          ds_container S (Generic (dt_task C)) =
            Some (dt_ready_root C (dt_priority C (dt_task C)))
      | DelayUnlinked \<Rightarrow> delay_transit_ownership C S
      | DelayKeyed \<Rightarrow> delay_transit_ownership C S
      | DelaySelected r \<Rightarrow>
          delay_transit_ownership C S \<and> r = delay_selected_root C
      | DelayInserted \<Rightarrow>
          delay_stable_ownership C S \<and>
          ds_container S (Generic (dt_task C)) =
            Some (delay_selected_root C)
      | DelayResumed _ \<Rightarrow>
          delay_stable_ownership C S \<and>
          ds_container S (Generic (dt_task C)) =
            Some (delay_selected_root C)
      | DelayYieldPending \<Rightarrow>
          delay_stable_ownership C S \<and>
          ds_container S (Generic (dt_task C)) =
            Some (delay_selected_root C))"

definition delay_phase_top_ok ::
  "('tid, 'root) delay_txn_context \<Rightarrow>
   'root delay_txn_phase \<Rightarrow>
   ('tid, 'root) delay_txn_snapshot \<Rightarrow> bool"
where
  "delay_phase_top_ok C phase S \<longleftrightarrow>
     (case phase of
        DelayReady \<Rightarrow>
          delay_exact_top_ready (dt_priority_levels C)
            (ds_ready S) (ds_top_hint S)
      | DelayUnlinked \<Rightarrow>
          delay_yield_top_hint (dt_priority_levels C)
            (ds_ready S) (ds_top_hint S)
      | DelayKeyed \<Rightarrow>
          delay_yield_top_hint (dt_priority_levels C)
            (ds_ready S) (ds_top_hint S)
      | DelaySelected _ \<Rightarrow>
          delay_yield_top_hint (dt_priority_levels C)
            (ds_ready S) (ds_top_hint S)
      | DelayInserted \<Rightarrow>
          delay_yield_top_hint (dt_priority_levels C)
            (ds_ready S) (ds_top_hint S)
      | DelayResumed _ \<Rightarrow>
          delay_yield_top_hint (dt_priority_levels C)
            (ds_ready S) (ds_top_hint S)
      | DelayYieldPending \<Rightarrow>
          delay_yield_top_hint (dt_priority_levels C)
            (ds_ready S) (ds_top_hint S))"

definition delay_phase_key_ok ::
  "('tid, 'root) delay_txn_context \<Rightarrow>
   'root delay_txn_phase \<Rightarrow>
   ('tid, 'root) delay_txn_snapshot \<Rightarrow> bool"
where
  "delay_phase_key_ok C phase S \<longleftrightarrow>
     (case phase of
        DelayReady \<Rightarrow> True
      | DelayUnlinked \<Rightarrow> True
      | DelayKeyed \<Rightarrow>
          ds_wake S (dt_task C) = Some (delay_wake C)
      | DelaySelected _ \<Rightarrow>
          ds_wake S (dt_task C) = Some (delay_wake C)
      | DelayInserted \<Rightarrow>
          ds_wake S (dt_task C) = Some (delay_wake C)
      | DelayResumed _ \<Rightarrow>
          ds_wake S (dt_task C) = Some (delay_wake C)
      | DelayYieldPending \<Rightarrow>
          ds_wake S (dt_task C) = Some (delay_wake C))"

definition delay_phase_current_ok ::
  "('tid, 'root) delay_txn_context \<Rightarrow>
   'root delay_txn_phase \<Rightarrow>
   ('tid, 'root) delay_txn_snapshot \<Rightarrow> bool"
where
  "delay_phase_current_ok C phase S \<longleftrightarrow>
     ds_current S = Some (dt_task C)"

definition delay_phase_machine_ok ::
  "('tid, 'root) delay_txn_context \<Rightarrow>
   'root delay_txn_phase \<Rightarrow>
   ('tid, 'root) delay_txn_snapshot \<Rightarrow> bool"
where
  "delay_phase_machine_ok C phase S \<longleftrightarrow>
     ds_tick S = dt_tick C \<and>
     (case phase of
        DelayReady \<Rightarrow>
          ds_scheduler_suspended S = dt_suspension_depth C
      | DelayUnlinked \<Rightarrow>
          ds_scheduler_suspended S = dt_suspension_depth C
      | DelayKeyed \<Rightarrow>
          ds_scheduler_suspended S = dt_suspension_depth C
      | DelaySelected _ \<Rightarrow>
          ds_scheduler_suspended S = dt_suspension_depth C
      | DelayInserted \<Rightarrow>
          ds_scheduler_suspended S = dt_suspension_depth C
      | DelayResumed _ \<Rightarrow>
          ds_scheduler_suspended S = dt_suspension_depth C - 1
      | DelayYieldPending \<Rightarrow>
          ds_scheduler_suspended S = dt_suspension_depth C - 1)"

definition delay_phase_ok ::
  "('tid, 'root) delay_txn_context \<Rightarrow>
   'root delay_txn_phase \<Rightarrow>
   ('tid, 'root) delay_txn_snapshot \<Rightarrow> bool"
where
  "delay_phase_ok C phase S \<longleftrightarrow>
     delay_context_wf C \<and>
     delay_snapshot_shape C S \<and>
     delay_phase_ownership_ok C phase S \<and>
     delay_phase_top_ok C phase S \<and>
     delay_phase_key_ok C phase S \<and>
     delay_phase_current_ok C phase S \<and>
     delay_phase_machine_ok C phase S"

inductive delay_phase_step ::
  "('tid, 'root) delay_txn_context \<Rightarrow>
   'root delay_txn_phase \<Rightarrow> 'root delay_txn_phase \<Rightarrow> bool"
for C where
  Ready_Unlinked:
    "delay_phase_step C DelayReady DelayUnlinked"
| Unlinked_Keyed:
    "delay_phase_step C DelayUnlinked DelayKeyed"
| Keyed_Selected:
    "r = delay_selected_root C \<Longrightarrow>
     delay_phase_step C DelayKeyed (DelaySelected r)"
| Selected_Inserted:
    "delay_phase_step C (DelaySelected r) DelayInserted"
| Inserted_Resumed:
    "delay_phase_step C DelayInserted (DelayResumed path)"
| Resumed_YieldPending:
    "delay_phase_step C (DelayResumed path) DelayYieldPending"

definition delay_public_eq ::
  "('tid, 'root) delay_txn_snapshot \<Rightarrow>
   ('tid, 'root) delay_txn_snapshot \<Rightarrow> bool"
where
  "delay_public_eq S T \<longleftrightarrow>
     ds_ready S = ds_ready T \<and>
     ds_current_delayed S = ds_current_delayed T \<and>
     ds_overflow_delayed S = ds_overflow_delayed T \<and>
     ds_members S = ds_members T \<and>
     ds_container S = ds_container T \<and>
     ds_next S = ds_next T \<and>
     ds_previous S = ds_previous T \<and>
     ds_wake S = ds_wake T \<and>
     ds_tick S = ds_tick T \<and>
     ds_top_hint S = ds_top_hint T \<and>
     ds_current S = ds_current T \<and>
     ds_scheduler_suspended S = ds_scheduler_suspended T \<and>
     ds_pending_ready S = ds_pending_ready T \<and>
     ds_missed_ticks S = ds_missed_ticks T \<and>
     ds_missed_yield S = ds_missed_yield T \<and>
     ds_yield_count S = ds_yield_count T"

definition delay_existing_ring_slot ::
  "'id \<Rightarrow> ('id, 'key) xlist_abs \<Rightarrow>
   'id option \<Rightarrow> 'id option \<Rightarrow> bool"
where
  "delay_existing_ring_slot n xs c q \<longleftrightarrow>
     (\<exists>before after.
        ring xs = before @ n # after \<and>
        c = (case rev before of [] \<Rightarrow> None | x # _ \<Rightarrow> Some x) \<and>
        q = (case after of [] \<Rightarrow> None | x # _ \<Rightarrow> Some x))"

definition delay_ordered_scan_slot ::
  "'id \<Rightarrow> 'key::linorder \<Rightarrow> ('id, 'key) xlist_abs \<Rightarrow>
   'id option \<Rightarrow> 'id option \<Rightarrow> bool"
where
  "delay_ordered_scan_slot n k xs c q \<longleftrightarrow>
     n \<notin> set (ring xs) \<and>
     (\<exists>before after.
        ring xs = before @ after \<and>
        (\<forall>x\<in>set before. item_key xs x \<le> k) \<and>
        (case after of [] \<Rightarrow> True | x # _ \<Rightarrow> k < item_key xs x) \<and>
        c = (case rev before of [] \<Rightarrow> None | x # _ \<Rightarrow> Some x) \<and>
        q = (case after of [] \<Rightarrow> None | x # _ \<Rightarrow> Some x))"

definition delay_selected_snapshot_ring ::
  "('tid, 'root) delay_txn_context \<Rightarrow> 'root \<Rightarrow>
   ('tid, 'root) delay_txn_snapshot \<Rightarrow> 'tid node_ring"
where
  "delay_selected_snapshot_ring C selected S =
     (if selected = dt_current_root C
      then ds_current_delayed S
      else ds_overflow_delayed S)"

definition delay_ready_unlinked_delta ::
  "('tid, 'root) delay_txn_context \<Rightarrow>
   'tid node_kind option \<Rightarrow> 'tid node_kind option \<Rightarrow>
   ('tid, 'root) delay_txn_snapshot \<Rightarrow>
   ('tid, 'root) delay_txn_snapshot \<Rightarrow> bool"
where
  "delay_ready_unlinked_delta C c q S T \<longleftrightarrow>
     (let t = dt_task C;
          p = dt_priority C t;
          n = Some (Generic t);
          source = dt_ready_root C p
      in c \<noteq> n \<and> q \<noteq> n \<and>
         delay_existing_ring_slot (Generic t) (ds_ready S p) c q \<and>
         ds_previous S n = c \<and> ds_next S n = q \<and>
         ds_next S c = n \<and> ds_previous S q = n \<and>
         ds_ready T =
           (ds_ready S)(p := list_remove_abs (Generic t) (ds_ready S p)) \<and>
         ds_current_delayed T = ds_current_delayed S \<and>
         ds_overflow_delayed T = ds_overflow_delayed S \<and>
         ds_members T =
           (ds_members S)(source := ds_members S source - {Generic t}) \<and>
         ds_container T = (ds_container S)(Generic t := None) \<and>
         ds_next T = (ds_next S)(c := q) \<and>
         ds_previous T = (ds_previous S)(q := c) \<and>
         ds_wake T = ds_wake S \<and>
         ds_tick T = ds_tick S \<and>
         ds_top_hint T = ds_top_hint S \<and>
         ds_current T = ds_current S \<and>
         ds_scheduler_suspended T = ds_scheduler_suspended S \<and>
         ds_pending_ready T = ds_pending_ready S \<and>
         ds_missed_ticks T = ds_missed_ticks S \<and>
         ds_missed_yield T = ds_missed_yield S \<and>
         ds_yield_count T = ds_yield_count S)"

definition delay_unlinked_keyed_delta ::
  "('tid, 'root) delay_txn_context \<Rightarrow>
   ('tid, 'root) delay_txn_snapshot \<Rightarrow>
   ('tid, 'root) delay_txn_snapshot \<Rightarrow> bool"
where
  "delay_unlinked_keyed_delta C S T \<longleftrightarrow>
     ds_ready T = ds_ready S \<and>
     ds_current_delayed T = ds_current_delayed S \<and>
     ds_overflow_delayed T = ds_overflow_delayed S \<and>
     ds_members T = ds_members S \<and>
     ds_container T = ds_container S \<and>
     ds_next T = ds_next S \<and>
     ds_previous T = ds_previous S \<and>
     ds_wake T = (ds_wake S)(dt_task C := Some (delay_wake C)) \<and>
     ds_tick T = ds_tick S \<and>
     ds_top_hint T = ds_top_hint S \<and>
     ds_current T = ds_current S \<and>
     ds_scheduler_suspended T = ds_scheduler_suspended S \<and>
     ds_pending_ready T = ds_pending_ready S \<and>
     ds_missed_ticks T = ds_missed_ticks S \<and>
     ds_missed_yield T = ds_missed_yield S \<and>
     ds_yield_count T = ds_yield_count S"

definition delay_keyed_selected_delta ::
  "('tid, 'root) delay_txn_snapshot \<Rightarrow>
   ('tid, 'root) delay_txn_snapshot \<Rightarrow> bool"
where
  "delay_keyed_selected_delta S T \<longleftrightarrow> delay_public_eq S T"

definition delay_selected_inserted_delta ::
  "('tid, 'root) delay_txn_context \<Rightarrow> 'root \<Rightarrow>
   'tid node_kind option \<Rightarrow> 'tid node_kind option \<Rightarrow>
   ('tid, 'root) delay_txn_snapshot \<Rightarrow>
   ('tid, 'root) delay_txn_snapshot \<Rightarrow> bool"
where
  "delay_selected_inserted_delta C selected c q S T \<longleftrightarrow>
     (let t = dt_task C;
          n = Some (Generic t);
          wake = delay_wake C
      in selected = delay_selected_root C \<and>
         c \<noteq> n \<and> q \<noteq> n \<and>
         delay_ordered_scan_slot (Generic t) wake
           (delay_selected_snapshot_ring C selected S) c q \<and>
         ds_next S c = q \<and> ds_previous S q = c \<and>
         ds_ready T = ds_ready S \<and>
         ds_current_delayed T =
           (if selected = dt_current_root C
            then list_insert_ordered_abs (Generic t) wake
                   (ds_current_delayed S)
            else ds_current_delayed S) \<and>
         ds_overflow_delayed T =
           (if selected = dt_overflow_root C
            then list_insert_ordered_abs (Generic t) wake
                   (ds_overflow_delayed S)
            else ds_overflow_delayed S) \<and>
         ds_members T =
           (ds_members S)(selected := insert (Generic t) (ds_members S selected)) \<and>
         ds_container T = (ds_container S)(Generic t := Some selected) \<and>
         ds_next T = (ds_next S)(n := q, c := n) \<and>
         ds_previous T = (ds_previous S)(q := n, n := c) \<and>
         ds_wake T = ds_wake S \<and>
         ds_tick T = ds_tick S \<and>
         ds_top_hint T = ds_top_hint S \<and>
         ds_current T = ds_current S \<and>
         ds_scheduler_suspended T = ds_scheduler_suspended S \<and>
         ds_pending_ready T = ds_pending_ready S \<and>
         ds_missed_ticks T = ds_missed_ticks S \<and>
         ds_missed_yield T = ds_missed_yield S \<and>
         ds_yield_count T = ds_yield_count S)"

definition delay_sequential_resume_boundary ::
  "('tid, 'root) delay_txn_context \<Rightarrow>
   ('tid, 'root) delay_txn_snapshot \<Rightarrow> bool"
where
  "delay_sequential_resume_boundary C S \<longleftrightarrow>
     ds_tick S = dt_tick C \<and>
     dt_suspension_depth C = Suc 0 \<and>
     ds_scheduler_suspended S = dt_suspension_depth C \<and>
     ring (ds_pending_ready S) = [] \<and>
     ds_missed_ticks S = 0"

definition delay_quiescent_resume_boundary ::
  "('tid, 'root) delay_txn_context \<Rightarrow>
   ('tid, 'root) delay_txn_snapshot \<Rightarrow> bool"
where
  "delay_quiescent_resume_boundary C S \<longleftrightarrow>
     delay_sequential_resume_boundary C S \<and>
     \<not> ds_missed_yield S"

definition delay_inserted_resumed_delta ::
  "('tid, 'root) delay_txn_context \<Rightarrow> delay_resume_path \<Rightarrow>
   ('tid, 'root) delay_txn_snapshot \<Rightarrow>
   ('tid, 'root) delay_txn_snapshot \<Rightarrow> bool"
where
  "delay_inserted_resumed_delta C path S T \<longleftrightarrow>
     delay_sequential_resume_boundary C S \<and>
     path = (if ds_missed_yield S
             then DelayInternalYield
             else DelayOuterYieldRequired) \<and>
     ds_ready T = ds_ready S \<and>
     ds_current_delayed T = ds_current_delayed S \<and>
     ds_overflow_delayed T = ds_overflow_delayed S \<and>
     ds_members T = ds_members S \<and>
     ds_container T = ds_container S \<and>
     ds_next T = ds_next S \<and>
     ds_previous T = ds_previous S \<and>
     ds_wake T = ds_wake S \<and>
     ds_tick T = ds_tick S \<and>
     ds_top_hint T = ds_top_hint S \<and>
     ds_current T = ds_current S \<and>
     ds_scheduler_suspended T = ds_scheduler_suspended S - 1 \<and>
     ds_pending_ready T = ds_pending_ready S \<and>
     ds_missed_ticks T = ds_missed_ticks S \<and>
     ds_missed_yield T = False \<and>
     ds_yield_count T =
       (case path of
          DelayInternalYield \<Rightarrow> Suc (ds_yield_count S)
        | DelayOuterYieldRequired \<Rightarrow> ds_yield_count S)"

definition delay_resumed_yield_pending_delta ::
  "delay_resume_path \<Rightarrow>
   ('tid, 'root) delay_txn_snapshot \<Rightarrow>
   ('tid, 'root) delay_txn_snapshot \<Rightarrow> bool"
where
  "delay_resumed_yield_pending_delta path S T \<longleftrightarrow>
     ds_ready T = ds_ready S \<and>
     ds_current_delayed T = ds_current_delayed S \<and>
     ds_overflow_delayed T = ds_overflow_delayed S \<and>
     ds_members T = ds_members S \<and>
     ds_container T = ds_container S \<and>
     ds_next T = ds_next S \<and>
     ds_previous T = ds_previous S \<and>
     ds_wake T = ds_wake S \<and>
     ds_tick T = ds_tick S \<and>
     ds_top_hint T = ds_top_hint S \<and>
     ds_current T = ds_current S \<and>
     ds_scheduler_suspended T = ds_scheduler_suspended S \<and>
     ds_pending_ready T = ds_pending_ready S \<and>
     ds_missed_ticks T = ds_missed_ticks S \<and>
     ds_missed_yield T = ds_missed_yield S \<and>
     ds_yield_count T =
       (case path of
          DelayInternalYield \<Rightarrow> ds_yield_count S
        | DelayOuterYieldRequired \<Rightarrow> Suc (ds_yield_count S))"

definition delay_resume_and_conditional_yield ::
  "('tid, 'root) delay_txn_context \<Rightarrow>
   ('tid, 'root) delay_txn_snapshot \<Rightarrow>
   ('tid, 'root) delay_txn_snapshot \<Rightarrow> bool"
where
  "delay_resume_and_conditional_yield C S T \<longleftrightarrow>
     (\<exists>path R.
        delay_inserted_resumed_delta C path S R \<and>
        delay_resumed_yield_pending_delta path R T)"

text \<open>
  @{const dt_suspension_depth} is the positive depth immediately after
  vTaskSuspendAll; there is deliberately no pre-suspend cutpoint in this
  core-only transaction theory.  All core cutpoints keep both the captured
  tick and that depth.  Resume is exposed only through
  @{const delay_sequential_resume_boundary}: source-level API entry requires
  one suspension level, an empty pending-ready ring, and zero missed ticks.
  These are named API assumptions, not properties inferred from a concrete
  witness.  The missed-yield bit remains symbolic and selects the
  internal-yield versus outer-yield-required source branch.  The stronger
  quiescent boundary fixes that bit false and consequently selects the outer
  branch.

  The slot predicates connect c/q to list-level source geometry: removal uses
  the actual predecessor/successor decomposition of the source ready ring,
  and insertion uses the exact stable ordered-scan split (all passed keys are
  at most the new wake key, while the first unpassed key is greater).  A
  raw-pointer-to-slot refinement theorem remains a separate implementation
  bridge; this proof-only phase model does not claim it.
\<close>

definition delay_remove_ready ::
  "'tid \<Rightarrow> nat \<Rightarrow>
   (nat \<Rightarrow> 'tid node_ring) \<Rightarrow>
   nat \<Rightarrow> 'tid node_ring"
where
  "delay_remove_ready t p ready =
     ready(p := list_remove_abs (Generic t) (ready p))"

lemma delay_context_wfD:
  assumes "delay_context_wf C"
  shows
    "finite (dt_live C) \<and>
     0 < dt_priority_levels C \<and>
     0 < dt_suspension_depth C \<and>
     dt_task C \<in> dt_live C \<and>
     (\<forall>t\<in>dt_live C.
        dt_priority C t < dt_priority_levels C) \<and>
     finite (dt_roots C)"
  using assms by (simp add: delay_context_wf_def)

lemma delay_phase_snapshot_shapeD:
  assumes phase: "delay_phase_ok C phase S"
  shows
    "(\<forall>p<dt_priority_levels C. xlist_wf (ds_ready S p)) \<and>
     xlist_wf (ds_current_delayed S) \<and>
     xlist_wf (ds_overflow_delayed S) \<and>
     xlist_wf (ds_pending_ready S)"
  using phase
  by (auto simp: delay_phase_ok_def delay_snapshot_shape_def)

lemma delay_stable_ownership_uniqueD:
  assumes stable: "delay_stable_ownership C S"
      and live: "t \<in> dt_live C"
  shows
    "\<exists>!r. r \<in> dt_roots C \<and>
         Generic t \<in> ds_members S r"
  using stable live by (simp add: delay_stable_ownership_def)

lemma delay_transit_only_current_unowned:
  assumes transit: "delay_transit_ownership C S"
  shows
    "ds_container S (Generic (dt_task C)) = None \<and>
     delay_globally_unlinked C S (Generic (dt_task C)) \<and>
     (\<forall>t\<in>dt_live C - {dt_task C}.
        \<exists>!r. r \<in> dt_roots C \<and>
             Generic t \<in> ds_members S r)"
  using transit by (simp add: delay_transit_ownership_def)

lemma delay_phase_selected_rootD:
  assumes selected: "delay_phase_ok C (DelaySelected r) S"
  shows "r = delay_selected_root C"
  using selected
  by (simp add: delay_phase_ok_def delay_phase_ownership_ok_def)

lemma delay_keyed_phase_wakeD:
  assumes keyed: "delay_phase_ok C DelayKeyed S"
  shows "ds_wake S (dt_task C) = Some (delay_wake C)"
  using keyed by (simp add: delay_phase_ok_def delay_phase_key_ok_def)

lemma delay_yield_pending_ownershipD:
  assumes pending: "delay_phase_ok C DelayYieldPending S"
  shows
    "delay_stable_ownership C S \<and>
     ds_container S (Generic (dt_task C)) =
       Some (delay_selected_root C)"
  using pending
  by (simp add: delay_phase_ok_def delay_phase_ownership_ok_def)

lemma delay_yield_pending_top_hintD:
  assumes pending: "delay_phase_ok C DelayYieldPending S"
  shows
    "delay_max_nonempty_ready (dt_priority_levels C) (ds_ready S)
       \<le> ds_top_hint S \<and>
     ds_top_hint S < dt_priority_levels C"
  using pending
  by (simp add: delay_phase_ok_def delay_phase_top_ok_def
      delay_yield_top_hint_def)

theorem delay_unlinked_phase_cannot_publicly_stutter:
  assumes ready: "delay_phase_ok C DelayReady S"
      and unlinked: "delay_phase_ok C DelayUnlinked T"
  shows "\<not> delay_public_eq S T"
proof
  assume public: "delay_public_eq S T"
  have before:
    "ds_container S (Generic (dt_task C)) =
       Some (dt_ready_root C (dt_priority C (dt_task C)))"
    using ready
    by (simp add: delay_phase_ok_def delay_phase_ownership_ok_def)
  have after: "ds_container T (Generic (dt_task C)) = None"
    using unlinked
    by (simp add: delay_phase_ok_def delay_phase_ownership_ok_def
        delay_transit_ownership_def)
  have same: "ds_container S = ds_container T"
    using public by (simp add: delay_public_eq_def)
  show False using before after same by simp
qed

lemma delay_remove_cursor_conditional:
  "cursor (list_remove_abs x q) =
     (if cursor q = Some x
      then predecessor x (ring q)
      else cursor q)"
  by (simp add: list_remove_abs_def)

definition delay_singleton_cursor_ring ::
  "'id \<Rightarrow> ('id \<Rightarrow> 'key) \<Rightarrow> ('id, 'key) xlist_abs"
where
  "delay_singleton_cursor_ring x keys =
     \<lparr>ring = [x], cursor = Some x, item_key = keys\<rparr>"

lemma singleton_cursor_unchanged_counterexample:
  "cursor
      (list_remove_abs x (delay_singleton_cursor_ring x keys)) \<noteq>
   cursor (delay_singleton_cursor_ring x keys)"
  by (simp add: delay_singleton_cursor_ring_def list_remove_abs_def)

lemma singleton_highest_removal_not_exact_counterexample:
  assumes hint_lt: "hint < levels"
      and singleton: "ring (ready hint) = [Generic t]"
  shows
    "\<not> delay_exact_top_ready levels
       (delay_remove_ready t hint ready) hint"
  using hint_lt singleton
  by (simp add: delay_exact_top_ready_def delay_ready_upper_bound_def
      delay_remove_ready_def list_remove_abs_def)

definition delay_single_equal_wake_ring ::
  "'tid node_kind \<Rightarrow> 32 word \<Rightarrow> 'tid node_ring"
where
  "delay_single_equal_wake_ring old wake =
     \<lparr>ring = [old], cursor = None, item_key = (\<lambda>_. wake)\<rparr>"

lemma two_equal_wake_stable_after_equals:
  assumes distinct: "new \<noteq> old"
  shows
    "ring
       (list_insert_ordered_abs new wake
         (delay_single_equal_wake_ring old wake)) =
     [old, new]"
  using distinct
  by (simp add: delay_single_equal_wake_ring_def
      list_insert_ordered_abs_def Let_def)

lemma two_equal_wake_before_equals_counterexample:
  assumes distinct: "new \<noteq> old"
  shows
    "ring
       (list_insert_ordered_abs new wake
         (delay_single_equal_wake_ring old wake)) \<noteq>
     [new, old]"
  using distinct two_equal_wake_stable_after_equals[OF distinct]
  by auto

lemma delay_remove_ready_preserves_upper_bound:
  assumes upper: "delay_ready_upper_bound levels ready hint"
  shows
    "delay_ready_upper_bound levels (delay_remove_ready t p ready) hint"
proof -
  from upper have hint_lt: "hint < levels"
    and old_bound:
      "\<forall>q<levels. ring (ready q) \<noteq> [] \<longrightarrow> q \<le> hint"
    by (simp_all add: delay_ready_upper_bound_def)
  have new_bound:
    "\<forall>q<levels.
       ring (delay_remove_ready t p ready q) \<noteq> [] \<longrightarrow>
       q \<le> hint"
  proof (intro allI impI)
    fix q
    assume q: "q < levels"
    assume nonempty:
      "ring (delay_remove_ready t p ready q) \<noteq> []"
    have old_nonempty: "ring (ready q) \<noteq> []"
      using nonempty
      by (cases "q = p"; cases "ring (ready q)")
         (simp_all add: delay_remove_ready_def list_remove_abs_def)
    show "q \<le> hint"
      using old_bound q old_nonempty by blast
  qed
  show ?thesis
    using hint_lt new_bound by (simp add: delay_ready_upper_bound_def)
qed

lemma delay_upper_bound_imp_yield_hint:
  assumes upper: "delay_ready_upper_bound levels ready hint"
  shows "delay_yield_top_hint levels ready hint"
proof -
  let ?A = "insert 0 (delay_nonempty_ready_priorities levels ready)"
  have finite_A: "finite ?A"
    by (simp add: delay_nonempty_ready_priorities_def)
  have nonempty_A: "?A \<noteq> {}"
    by simp
  have every: "\<forall>p\<in>?A. p \<le> hint"
    using upper
    by (auto simp: delay_ready_upper_bound_def
        delay_nonempty_ready_priorities_def)
  have max_in: "Max ?A \<in> ?A"
    by (rule Max_in[OF finite_A nonempty_A])
  have max_le: "Max ?A \<le> hint"
    using every max_in by blast
  from upper have hint_lt: "hint < levels"
    by (simp add: delay_ready_upper_bound_def)
  show ?thesis
    using max_le hint_lt
    by (simp add: delay_yield_top_hint_def
        delay_max_nonempty_ready_def)
qed

corollary delay_remove_ready_preserves_yield_hint:
  assumes upper: "delay_ready_upper_bound levels ready hint"
  shows
    "delay_yield_top_hint levels (delay_remove_ready t p ready) hint"
  by (rule delay_upper_bound_imp_yield_hint,
      rule delay_remove_ready_preserves_upper_bound[OF upper])

lemma delay_selected_root_wrap:
  assumes wrap: "delay_wake C < dt_tick C"
  shows "delay_selected_root C = dt_overflow_root C"
  using wrap by (simp add: delay_selected_root_def)

lemma delay_selected_root_nonwrap:
  assumes nonwrap: "\<not> delay_wake C < dt_tick C"
  shows "delay_selected_root C = dt_current_root C"
  using nonwrap by (simp add: delay_selected_root_def)

lemma delay_selected_phase_wrapD:
  assumes selected: "delay_phase_ok C (DelaySelected r) S"
      and wrap: "delay_wake C < dt_tick C"
  shows "r = dt_overflow_root C"
  using delay_phase_selected_rootD[OF selected]
    delay_selected_root_wrap[OF wrap]
  by simp

lemma delay_selected_phase_nonwrapD:
  assumes selected: "delay_phase_ok C (DelaySelected r) S"
      and nonwrap: "\<not> delay_wake C < dt_tick C"
  shows "r = dt_current_root C"
  using delay_phase_selected_rootD[OF selected]
    delay_selected_root_nonwrap[OF nonwrap]
  by simp

theorem delay_max_wake_selects_current_root:
  assumes max_wake: "delay_wake C = (- 1 :: 32 word)"
  shows "delay_selected_root C = dt_current_root C"
proof -
  have tick_le: "dt_tick C \<le> (- 1 :: 32 word)"
    by simp
  have nonwrap: "\<not> delay_wake C < dt_tick C"
    using max_wake tick_le by auto
  show ?thesis
    by (rule delay_selected_root_nonwrap[OF nonwrap])
qed

text \<open>
  The following destructor lemmas are the executable-field ledger for the
  seven proof cutpoints.  The neighbour parameters may coincide: neither
  removal nor insertion assumes @{term "c \<noteq> q"}.  Only coincidence with the
  in-transit Generic item is excluded, which is precisely what preserves the
  removed item's own stale link fields during the unlink cutpoint.
\<close>

lemma delay_phase_currentD:
  assumes phase: "delay_phase_ok C phase S"
  shows "ds_current S = Some (dt_task C)"
  using phase
  by (simp add: delay_phase_ok_def delay_phase_current_ok_def)

lemma delay_phase_tick_and_suspensionD:
  assumes phase: "delay_phase_ok C phase S"
  shows
    "ds_tick S = dt_tick C \<and>
     (case phase of
        DelayReady \<Rightarrow>
          ds_scheduler_suspended S = dt_suspension_depth C
      | DelayUnlinked \<Rightarrow>
          ds_scheduler_suspended S = dt_suspension_depth C
      | DelayKeyed \<Rightarrow>
          ds_scheduler_suspended S = dt_suspension_depth C
      | DelaySelected _ \<Rightarrow>
          ds_scheduler_suspended S = dt_suspension_depth C
      | DelayInserted \<Rightarrow>
          ds_scheduler_suspended S = dt_suspension_depth C
      | DelayResumed _ \<Rightarrow>
          ds_scheduler_suspended S = dt_suspension_depth C - 1
      | DelayYieldPending \<Rightarrow>
          ds_scheduler_suspended S = dt_suspension_depth C - 1)"
  using phase
  by (simp add: delay_phase_ok_def delay_phase_machine_ok_def)

lemma delay_ready_and_unlinked_key_unconstrained:
  "delay_phase_key_ok C DelayReady S \<and>
   delay_phase_key_ok C DelayUnlinked T"
  by (simp add: delay_phase_key_ok_def)

lemma delay_ready_unlinked_precomputed_wake_and_frames:
  assumes delta: "delay_ready_unlinked_delta C c q S T"
  shows
    "delay_wake C = dt_tick C + dt_delay C \<and>
     ds_current_delayed T = ds_current_delayed S \<and>
     ds_overflow_delayed T = ds_overflow_delayed S \<and>
     ds_wake T = ds_wake S \<and>
     ds_tick T = ds_tick S \<and>
     ds_top_hint T = ds_top_hint S \<and>
     ds_current T = ds_current S \<and>
     ds_scheduler_suspended T = ds_scheduler_suspended S \<and>
     ds_pending_ready T = ds_pending_ready S \<and>
     ds_missed_ticks T = ds_missed_ticks S \<and>
     ds_missed_yield T = ds_missed_yield S \<and>
     ds_yield_count T = ds_yield_count S"
  using delta
  by (auto simp: delay_wake_def delay_ready_unlinked_delta_def Let_def)

lemma delay_ready_unlinked_removed_links_stale:
  assumes delta: "delay_ready_unlinked_delta C c q S T"
  shows
    "ds_next T (Some (Generic (dt_task C))) =
       ds_next S (Some (Generic (dt_task C))) \<and>
     ds_previous T (Some (Generic (dt_task C))) =
       ds_previous S (Some (Generic (dt_task C)))"
  using delta
  by (auto simp: delay_ready_unlinked_delta_def Let_def)

lemma delay_ready_unlinked_exact_deltaD:
  assumes delta: "delay_ready_unlinked_delta C c q S T"
  defines "t \<equiv> dt_task C"
      and "p \<equiv> dt_priority C (dt_task C)"
      and "source \<equiv> dt_ready_root C (dt_priority C (dt_task C))"
  shows
    "delay_existing_ring_slot (Generic t) (ds_ready S p) c q \<and>
     ds_previous S (Some (Generic t)) = c \<and>
     ds_next S (Some (Generic t)) = q \<and>
     ds_next S c = Some (Generic t) \<and>
     ds_previous S q = Some (Generic t) \<and>
     ds_ready T =
       (ds_ready S)(p := list_remove_abs (Generic t) (ds_ready S p)) \<and>
     ds_members T =
       (ds_members S)(source := ds_members S source - {Generic t}) \<and>
     ds_container T = (ds_container S)(Generic t := None) \<and>
     ds_next T = (ds_next S)(c := q) \<and>
     ds_previous T = (ds_previous S)(q := c)"
  using delta
  by (auto simp: delay_ready_unlinked_delta_def Let_def
      t_def p_def source_def)

lemma delay_unlinked_keyed_exact_deltaD:
  assumes delta: "delay_unlinked_keyed_delta C S T"
  shows
    "ds_wake T =
       (ds_wake S)(dt_task C := Some (dt_tick C + dt_delay C)) \<and>
     ds_ready T = ds_ready S \<and>
     ds_current_delayed T = ds_current_delayed S \<and>
     ds_overflow_delayed T = ds_overflow_delayed S \<and>
     ds_members T = ds_members S \<and>
     ds_container T = ds_container S \<and>
     ds_next T = ds_next S \<and>
     ds_previous T = ds_previous S \<and>
     ds_tick T = ds_tick S \<and>
     ds_top_hint T = ds_top_hint S \<and>
     ds_current T = ds_current S \<and>
     ds_scheduler_suspended T = ds_scheduler_suspended S \<and>
     ds_pending_ready T = ds_pending_ready S \<and>
     ds_missed_ticks T = ds_missed_ticks S \<and>
     ds_missed_yield T = ds_missed_yield S \<and>
     ds_yield_count T = ds_yield_count S"
  using delta
  by (simp add: delay_unlinked_keyed_delta_def delay_wake_def)

lemma delay_keyed_selected_public_stutterD:
  assumes delta: "delay_keyed_selected_delta S T"
  shows "delay_public_eq S T"
  using delta by (simp add: delay_keyed_selected_delta_def)

lemma delay_selected_inserted_exact_deltaD:
  assumes delta: "delay_selected_inserted_delta C selected c q S T"
  defines "t \<equiv> dt_task C"
      and "n \<equiv> Some (Generic (dt_task C))"
      and "wake \<equiv> delay_wake C"
  shows
    "selected = delay_selected_root C \<and>
     delay_ordered_scan_slot (Generic t) wake
       (delay_selected_snapshot_ring C selected S) c q \<and>
     ds_next S c = q \<and> ds_previous S q = c \<and>
     ds_ready T = ds_ready S \<and>
     ds_current_delayed T =
       (if selected = dt_current_root C
        then list_insert_ordered_abs (Generic t) wake
               (ds_current_delayed S)
        else ds_current_delayed S) \<and>
     ds_overflow_delayed T =
       (if selected = dt_overflow_root C
        then list_insert_ordered_abs (Generic t) wake
               (ds_overflow_delayed S)
        else ds_overflow_delayed S) \<and>
     ds_members T =
       (ds_members S)(selected := insert (Generic t) (ds_members S selected)) \<and>
     ds_container T = (ds_container S)(Generic t := Some selected) \<and>
     ds_next T = (ds_next S)(n := q, c := n) \<and>
     ds_previous T = (ds_previous S)(q := n, n := c) \<and>
     ds_wake T = ds_wake S \<and>
     ds_tick T = ds_tick S \<and>
     ds_top_hint T = ds_top_hint S \<and>
     ds_current T = ds_current S \<and>
     ds_scheduler_suspended T = ds_scheduler_suspended S \<and>
     ds_pending_ready T = ds_pending_ready S \<and>
     ds_missed_ticks T = ds_missed_ticks S \<and>
     ds_missed_yield T = ds_missed_yield S \<and>
     ds_yield_count T = ds_yield_count S"
  using delta
  by (auto simp only: delay_selected_inserted_delta_def Let_def
      t_def n_def wake_def)

lemma delay_quiescent_resume_requires_outer_yield:
  assumes quiet: "delay_quiescent_resume_boundary C S"
      and resume: "delay_inserted_resumed_delta C path S T"
  shows "path = DelayOuterYieldRequired"
  using quiet resume
  by (simp add: delay_quiescent_resume_boundary_def
      delay_sequential_resume_boundary_def
      delay_inserted_resumed_delta_def)

lemma delay_internal_resume_performs_yield:
  assumes resume:
    "delay_inserted_resumed_delta C DelayInternalYield S T"
  shows
    "ds_yield_count T = Suc (ds_yield_count S) \<and>
     ds_scheduler_suspended T = ds_scheduler_suspended S - 1 \<and>
     ds_tick T = ds_tick S"
  using resume by (simp add: delay_inserted_resumed_delta_def)

lemma delay_outer_resume_defers_yield:
  assumes resume:
    "delay_inserted_resumed_delta C DelayOuterYieldRequired S T"
  shows
    "ds_yield_count T = ds_yield_count S \<and>
     ds_scheduler_suspended T = ds_scheduler_suspended S - 1 \<and>
     ds_tick T = ds_tick S"
  using resume by (simp add: delay_inserted_resumed_delta_def)

lemma delay_internal_path_skips_outer_yield:
  assumes outer:
    "delay_resumed_yield_pending_delta DelayInternalYield S T"
  shows "ds_yield_count T = ds_yield_count S"
  using outer by (simp add: delay_resumed_yield_pending_delta_def)

lemma delay_outer_path_performs_outer_yield:
  assumes outer:
    "delay_resumed_yield_pending_delta DelayOuterYieldRequired S T"
  shows "ds_yield_count T = Suc (ds_yield_count S)"
  using outer by (simp add: delay_resumed_yield_pending_delta_def)

theorem delay_resume_paths_converge_to_one_yield:
  assumes transaction: "delay_resume_and_conditional_yield C S T"
  shows
    "ds_yield_count T = Suc (ds_yield_count S) \<and>
     ds_tick T = ds_tick S \<and>
     ds_current T = ds_current S \<and>
     ds_top_hint T = ds_top_hint S \<and>
     ds_scheduler_suspended T = ds_scheduler_suspended S - 1"
proof -
  obtain path R where
    resume: "delay_inserted_resumed_delta C path S R" and
    outer: "delay_resumed_yield_pending_delta path R T"
    using transaction
    by (auto simp: delay_resume_and_conditional_yield_def)
  show ?thesis
    using resume outer
    by (cases path)
       (auto simp: delay_inserted_resumed_delta_def
          delay_resumed_yield_pending_delta_def)
qed

end
