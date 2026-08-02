theory Scheduler_One_Due_Task_Phases_Base
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Task_Observation_Rel.Scheduler_Task_Observation_Rel"
    "EAL6_FreeRTOS_V611_Scheduler_Event_Root_Family_Rel.Scheduler_Event_Root_Family_Rel"
    "EAL6_FreeRTOS_V611_Scheduler_Delay_Suspended_Core.Scheduler_Delay_Suspended_Core"
    "EAL6_FreeRTOS_V611_Scheduler_Unlocked_Tick_Scaffold.Scheduler_Unlocked_Tick_Scaffold"
begin

text \<open>
  Universal one-due-task source-order scaffold for the unlocked tick loop.

  No task, priority, root, key, tick, list length, cursor, endpoint, or Event
  branch is fixed.  The entry task is an arbitrary live task whose Generic
  item is due in the current delayed root.  Its Event item is either owned by
  one arbitrary external Event root or is globally unlinked/NULL.  The six
  cutpoints follow the FreeRTOS V6.1.1 source order exactly:

    DueOwned -> GenericUnlinked -> EventChecked -> EventUnlinked
             -> TopRaised -> GenericReady.

  The phase snapshots below are proof objects.  They retain a total physical
  payload map for Generic items and the total K_E map for Event items, so an
  unlinked node never loses its payload merely because it is absent from every
  represented ring.
\<close>

datatype 'root one_due_event_branch =
    DueEventLinked 'root
  | DueEventNull

datatype one_due_phase =
    DueOwned
  | GenericUnlinked
  | EventChecked
  | EventUnlinked
  | TopRaised
  | GenericReady

record ('tid, 'root) one_due_context =
  odc_live :: "'tid set"
  odc_task :: 'tid
  odc_generic_roots :: "'root set"
  odc_event_roots :: "'root set"
  odc_delayed_root :: 'root
  odc_ready_root :: "nat \<Rightarrow> 'root"
  odc_pending_root :: 'root
  odc_priority :: "'tid \<Rightarrow> nat"
  odc_tick :: "32 word"
  odc_entry_top :: nat
  odc_K_E :: "'tid \<Rightarrow> 32 word"

record ('tid, 'root) one_due_snapshot =
  ods_generic_family :: "'root \<Rightarrow> 'tid node_ring"
  ods_event_family :: "'root \<Rightarrow> 'tid node_ring"
  ods_generic_payload :: "'tid \<Rightarrow> 32 word"
  ods_event_payload :: "'tid \<Rightarrow> 32 word"
  ods_top :: nat
  ods_captured_generic_key :: "32 word option"
  ods_checked_event :: "'root one_due_event_branch option"

definition one_due_target_root ::
  "('tid, 'root) one_due_context \<Rightarrow> 'root"
where
  "one_due_target_root C = odc_ready_root C (odc_priority C (odc_task C))"

definition one_due_context_wf ::
  "('tid, 'root) one_due_context \<Rightarrow> bool"
where
  "one_due_context_wf C \<longleftrightarrow>
     finite (odc_live C) \<and>
     odc_task C \<in> odc_live C \<and>
     finite (odc_generic_roots C) \<and>
     finite (odc_event_roots C) \<and>
     odc_delayed_root C \<in> odc_generic_roots C \<and>
     one_due_target_root C \<in> odc_generic_roots C \<and>
     odc_delayed_root C \<noteq> one_due_target_root C \<and>
     odc_pending_root C \<in> odc_event_roots C"

definition one_due_family_shape ::
  "('tid, 'root) one_due_context \<Rightarrow>
   ('tid, 'root) one_due_snapshot \<Rightarrow> bool"
where
  "one_due_family_shape C S \<longleftrightarrow>
     (\<forall>r\<in>odc_generic_roots C.
        xlist_wf (ods_generic_family S r) \<and>
        generic_ring (ods_generic_family S r) \<and>
        set (ring (ods_generic_family S r)) \<subseteq>
          Generic ` odc_live C) \<and>
     (\<forall>r\<in>odc_event_roots C.
        xlist_wf (ods_event_family S r) \<and>
        event_ring (ods_event_family S r) \<and>
        set (ring (ods_event_family S r)) \<subseteq>
          Event ` odc_live C) \<and>
     (\<forall>r\<in>odc_generic_roots C. \<forall>s\<in>odc_generic_roots C.
        r \<noteq> s \<longrightarrow>
        set (ring (ods_generic_family S r)) \<inter>
          set (ring (ods_generic_family S s)) = {}) \<and>
     (\<forall>r\<in>odc_event_roots C. \<forall>s\<in>odc_event_roots C.
        r \<noteq> s \<longrightarrow>
        set (ring (ods_event_family S r)) \<inter>
          set (ring (ods_event_family S s)) = {}) \<and>
     (\<forall>r\<in>odc_generic_roots C. \<forall>t\<in>odc_live C.
        Generic t \<in> set (ring (ods_generic_family S r)) \<longrightarrow>
        item_key (ods_generic_family S r) (Generic t) =
          ods_generic_payload S t) \<and>
     (\<forall>r\<in>odc_event_roots C. \<forall>t\<in>odc_live C.
        Event t \<in> set (ring (ods_event_family S r)) \<longrightarrow>
        item_key (ods_event_family S r) (Event t) =
          ods_event_payload S t) \<and>
     (\<forall>t\<in>odc_live C. ods_event_payload S t = odc_K_E C t)"

definition one_due_external_roots ::
  "('tid, 'root) one_due_context \<Rightarrow> 'root set"
where
  "one_due_external_roots C =
     odc_event_roots C - {odc_pending_root C}"

fun one_due_event_branch_at ::
  "('tid, 'root) one_due_context \<Rightarrow>
   ('tid, 'root) one_due_snapshot \<Rightarrow>
   'root one_due_event_branch \<Rightarrow> bool"
where
  "one_due_event_branch_at C S (DueEventLinked owner) \<longleftrightarrow>
     owner \<in> one_due_external_roots C \<and>
     Event (odc_task C) \<in> set (ring (ods_event_family S owner))"
| "one_due_event_branch_at C S DueEventNull \<longleftrightarrow>
     (\<forall>r\<in>odc_event_roots C.
        Event (odc_task C) \<notin> set (ring (ods_event_family S r)))"

lemma one_due_event_branch_exhaustive_if_pending_empty:
  assumes pending_empty:
    "ring (ods_event_family S (odc_pending_root C)) = []"
  shows "\<exists>branch. one_due_event_branch_at C S branch"
proof (cases
    "\<exists>owner\<in>odc_event_roots C.
       Event (odc_task C) \<in>
         set (ring (ods_event_family S owner))")
  case True
  then obtain owner where
      owner_root: "owner \<in> odc_event_roots C"
    and owner_member:
      "Event (odc_task C) \<in>
        set (ring (ods_event_family S owner))"
    by blast
  have owner_not_pending: "owner \<noteq> odc_pending_root C"
    using owner_member pending_empty by auto
  have external: "owner \<in> one_due_external_roots C"
    using owner_root owner_not_pending
    by (auto simp: one_due_external_roots_def)
  show ?thesis
    using external owner_member
    by (intro exI[of _ "DueEventLinked owner"]) simp
next
  case False
  then have absent:
    "\<forall>r\<in>odc_event_roots C.
       Event (odc_task C) \<notin>
         set (ring (ods_event_family S r))"
    by blast
  show ?thesis
    using absent by (intro exI[of _ DueEventNull]) simp
qed

definition one_due_entry_rel ::
  "('tid, 'root) one_due_context \<Rightarrow>
   'root one_due_event_branch \<Rightarrow>
   ('tid, 'root) one_due_snapshot \<Rightarrow> bool"
where
  "one_due_entry_rel C branch S \<longleftrightarrow>
     one_due_context_wf C \<and>
     one_due_family_shape C S \<and>
     (\<exists>rest.
        ring (ods_generic_family S (odc_delayed_root C)) =
          Generic (odc_task C) # rest) \<and>
     Generic (odc_task C) \<in>
       set (ring (ods_generic_family S (odc_delayed_root C))) \<and>
     item_key (ods_generic_family S (odc_delayed_root C))
       (Generic (odc_task C)) = ods_generic_payload S (odc_task C) \<and>
     ods_generic_payload S (odc_task C) \<le> odc_tick C \<and>
     one_due_event_branch_at C S branch \<and>
     ods_top S = odc_entry_top C \<and>
     ods_captured_generic_key S = None \<and>
     ods_checked_event S = None"

definition one_due_generic_unlink_state ::
  "('tid, 'root) one_due_context \<Rightarrow>
   ('tid, 'root) one_due_snapshot \<Rightarrow>
   ('tid, 'root) one_due_snapshot"
where
  "one_due_generic_unlink_state C S =
     S\<lparr>
       ods_generic_family :=
         (ods_generic_family S)
           (odc_delayed_root C :=
             list_remove_abs (Generic (odc_task C))
               (ods_generic_family S (odc_delayed_root C))),
       ods_captured_generic_key :=
         Some (ods_generic_payload S (odc_task C))
     \<rparr>"

definition one_due_event_check_state ::
  "'root one_due_event_branch \<Rightarrow>
   ('tid, 'root) one_due_snapshot \<Rightarrow>
   ('tid, 'root) one_due_snapshot"
where
  "one_due_event_check_state branch S =
     S\<lparr>ods_checked_event := Some branch\<rparr>"

definition one_due_event_unlink_state ::
  "('tid, 'root) one_due_context \<Rightarrow>
   'root one_due_event_branch \<Rightarrow>
   ('tid, 'root) one_due_snapshot \<Rightarrow>
   ('tid, 'root) one_due_snapshot"
where
  "one_due_event_unlink_state C branch S =
     (case branch of
        DueEventLinked owner \<Rightarrow>
          S\<lparr>ods_event_family :=
            (ods_event_family S)
              (owner := list_remove_abs (Event (odc_task C))
                (ods_event_family S owner))\<rparr>
      | DueEventNull \<Rightarrow> S)"

definition one_due_raise_top_state ::
  "('tid, 'root) one_due_context \<Rightarrow>
   ('tid, 'root) one_due_snapshot \<Rightarrow>
   ('tid, 'root) one_due_snapshot"
where
  "one_due_raise_top_state C S =
     S\<lparr>ods_top := max (ods_top S) (odc_priority C (odc_task C))\<rparr>"

definition one_due_ready_state ::
  "('tid, 'root) one_due_context \<Rightarrow>
   ('tid, 'root) one_due_snapshot \<Rightarrow>
   ('tid, 'root) one_due_snapshot"
where
  "one_due_ready_state C S =
     (let target = one_due_target_root C;
          t = odc_task C;
          k = ods_generic_payload S t
      in S\<lparr>ods_generic_family :=
           (ods_generic_family S)
             (target := list_insert_end_abs (Generic t) k
               (ods_generic_family S target))\<rparr>)"

fun one_due_snapshot_at ::
  "('tid, 'root) one_due_context \<Rightarrow>
   'root one_due_event_branch \<Rightarrow> one_due_phase \<Rightarrow>
   ('tid, 'root) one_due_snapshot \<Rightarrow>
   ('tid, 'root) one_due_snapshot"
where
  "one_due_snapshot_at C branch DueOwned S = S"
| "one_due_snapshot_at C branch GenericUnlinked S =
     one_due_generic_unlink_state C S"
| "one_due_snapshot_at C branch EventChecked S =
     one_due_event_check_state branch
       (one_due_generic_unlink_state C S)"
| "one_due_snapshot_at C branch EventUnlinked S =
     one_due_event_unlink_state C branch
       (one_due_event_check_state branch
         (one_due_generic_unlink_state C S))"
| "one_due_snapshot_at C branch TopRaised S =
     one_due_raise_top_state C
       (one_due_event_unlink_state C branch
         (one_due_event_check_state branch
           (one_due_generic_unlink_state C S)))"
| "one_due_snapshot_at C branch GenericReady S =
     one_due_ready_state C
       (one_due_raise_top_state C
         (one_due_event_unlink_state C branch
           (one_due_event_check_state branch
             (one_due_generic_unlink_state C S))))"

definition one_due_phase_rel ::
  "('tid, 'root) one_due_context \<Rightarrow>
   'root one_due_event_branch \<Rightarrow>
   ('tid, 'root) one_due_snapshot \<Rightarrow> one_due_phase \<Rightarrow>
   ('tid, 'root) one_due_snapshot \<Rightarrow> bool"
where
  "one_due_phase_rel C branch entry phase current \<longleftrightarrow>
     one_due_entry_rel C branch entry \<and>
     current = one_due_snapshot_at C branch phase entry"

inductive one_due_phase_step :: "one_due_phase \<Rightarrow> one_due_phase \<Rightarrow> bool"
where
  DueOwned_GenericUnlinked:
    "one_due_phase_step DueOwned GenericUnlinked"
| GenericUnlinked_EventChecked:
    "one_due_phase_step GenericUnlinked EventChecked"
| EventChecked_EventUnlinked:
    "one_due_phase_step EventChecked EventUnlinked"
| EventUnlinked_TopRaised:
    "one_due_phase_step EventUnlinked TopRaised"
| TopRaised_GenericReady:
    "one_due_phase_step TopRaised GenericReady"

text \<open>Basic context and phase destructors.\<close>

lemma one_due_context_task_liveD:
  "one_due_context_wf C \<Longrightarrow> odc_task C \<in> odc_live C"
  by (simp add: one_due_context_wf_def)

lemma one_due_context_rootsD:
  assumes wf: "one_due_context_wf C"
  shows
    "odc_delayed_root C \<in> odc_generic_roots C \<and>
     one_due_target_root C \<in> odc_generic_roots C \<and>
     odc_delayed_root C \<noteq> one_due_target_root C \<and>
     odc_pending_root C \<in> odc_event_roots C"
  using wf by (simp add: one_due_context_wf_def)

lemma one_due_phase_rel_entryD:
  "one_due_phase_rel C branch entry phase current \<Longrightarrow>
   one_due_entry_rel C branch entry"
  by (simp add: one_due_phase_rel_def)

lemma one_due_phase_rel_currentD:
  "one_due_phase_rel C branch entry phase current \<Longrightarrow>
   current = one_due_snapshot_at C branch phase entry"
  by (simp add: one_due_phase_rel_def)

lemma one_due_phase_rel_deterministic:
  assumes left: "one_due_phase_rel C branch entry phase left"
    and right: "one_due_phase_rel C branch entry phase right"
  shows "left = right"
  using left right by (simp add: one_due_phase_rel_def)

lemma one_due_phase_chain:
  assumes entry: "one_due_entry_rel C branch S"
  shows
    "one_due_phase_rel C branch S DueOwned S \<and>
     one_due_phase_rel C branch S GenericUnlinked
       (one_due_generic_unlink_state C S) \<and>
     one_due_phase_rel C branch S EventChecked
       (one_due_event_check_state branch
         (one_due_generic_unlink_state C S)) \<and>
     one_due_phase_rel C branch S EventUnlinked
       (one_due_event_unlink_state C branch
         (one_due_event_check_state branch
           (one_due_generic_unlink_state C S))) \<and>
     one_due_phase_rel C branch S TopRaised
       (one_due_raise_top_state C
         (one_due_event_unlink_state C branch
           (one_due_event_check_state branch
             (one_due_generic_unlink_state C S)))) \<and>
     one_due_phase_rel C branch S GenericReady
       (one_due_ready_state C
         (one_due_raise_top_state C
           (one_due_event_unlink_state C branch
             (one_due_event_check_state branch
               (one_due_generic_unlink_state C S)))))"
  using entry by (simp add: one_due_phase_rel_def)

lemma one_due_generic_unlink_capture:
  "ods_captured_generic_key (one_due_generic_unlink_state C S) =
   Some (ods_generic_payload S (odc_task C))"
  by (simp add: one_due_generic_unlink_state_def)

lemma one_due_generic_unlink_non_target:
  assumes other: "r \<noteq> odc_delayed_root C"
  shows
    "ods_generic_family (one_due_generic_unlink_state C S) r =
     ods_generic_family S r"
  using other by (simp add: one_due_generic_unlink_state_def)

lemma one_due_event_unlink_non_target:
  assumes branch: "b = DueEventLinked owner"
    and other: "r \<noteq> owner"
  shows
    "ods_event_family (one_due_event_unlink_state C b S) r =
     ods_event_family S r"
  using branch other by (simp add: one_due_event_unlink_state_def)

lemma one_due_event_unlink_null_frame:
  "one_due_event_unlink_state C DueEventNull S = S"
  by (simp add: one_due_event_unlink_state_def)

lemma one_due_ready_non_target:
  assumes other: "r \<noteq> one_due_target_root C"
  shows
    "ods_generic_family (one_due_ready_state C S) r =
     ods_generic_family S r"
  using other by (simp add: one_due_ready_state_def Let_def)

lemma one_due_event_family_after_unlink_exact:
  "ods_event_family
      (one_due_snapshot_at C branch EventUnlinked S) r =
    (case branch of
       DueEventLinked owner \<Rightarrow>
         if r = owner then
           list_remove_abs (Event (odc_task C))
             (ods_event_family S owner)
         else ods_event_family S r
     | DueEventNull \<Rightarrow> ods_event_family S r)"
  by (cases branch)
     (simp_all add: one_due_generic_unlink_state_def
        one_due_event_check_state_def one_due_event_unlink_state_def)

lemma one_due_event_family_at_ready_exact:
  "ods_event_family
      (one_due_snapshot_at C branch GenericReady S) r =
    (case branch of
       DueEventLinked owner \<Rightarrow>
         if r = owner then
           list_remove_abs (Event (odc_task C))
             (ods_event_family S owner)
         else ods_event_family S r
     | DueEventNull \<Rightarrow> ods_event_family S r)"
  by (cases branch)
     (simp_all add: one_due_generic_unlink_state_def
        one_due_event_check_state_def one_due_event_unlink_state_def
        one_due_raise_top_state_def one_due_ready_state_def Let_def)

lemma one_due_generic_family_at_ready_exact:
  assumes entry: "one_due_entry_rel C branch S"
  shows
    "ods_generic_family
       (one_due_snapshot_at C branch GenericReady S) r =
     (if r = one_due_target_root C then
        list_insert_end_abs (Generic (odc_task C))
          (ods_generic_payload S (odc_task C))
          (ods_generic_family S r)
      else if r = odc_delayed_root C then
        list_remove_abs (Generic (odc_task C))
          (ods_generic_family S r)
      else ods_generic_family S r)"
proof -
  have different:
    "odc_delayed_root C \<noteq> one_due_target_root C"
    using entry
    by (auto simp: one_due_entry_rel_def one_due_context_wf_def)
  show ?thesis
    using different
    by (cases branch; cases "r = one_due_target_root C";
        cases "r = odc_delayed_root C")
       (simp_all add: one_due_generic_unlink_state_def
          one_due_event_check_state_def one_due_event_unlink_state_def
          one_due_raise_top_state_def one_due_ready_state_def Let_def)
qed

lemma one_due_payload_maps_frame:
  assumes current:
    "current = one_due_snapshot_at C branch phase entry"
  shows
    "ods_generic_payload current = ods_generic_payload entry \<and>
     ods_event_payload current = ods_event_payload entry"
  using current
  by (cases phase; cases branch)
     (simp_all add: one_due_generic_unlink_state_def
        one_due_event_check_state_def one_due_event_unlink_state_def
        one_due_raise_top_state_def one_due_ready_state_def Let_def)

text \<open>The total Event payload map is identical at every cutpoint,
  including after the linked Event node has left every ring.\<close>

lemma one_due_phase_total_K_E:
  assumes rel: "one_due_phase_rel C branch entry phase current"
    and live: "t \<in> odc_live C"
  shows "ods_event_payload current t = odc_K_E C t"
proof -
  have entry_rel: "one_due_entry_rel C branch entry"
    by (rule one_due_phase_rel_entryD[OF rel])
  then have shape: "one_due_family_shape C entry"
    by (simp add: one_due_entry_rel_def)
  then have key: "ods_event_payload entry t = odc_K_E C t"
    using live by (auto simp: one_due_family_shape_def)
  have current:
    "current = one_due_snapshot_at C branch phase entry"
    by (rule one_due_phase_rel_currentD[OF rel])
  show ?thesis
    using key current
    by (cases phase; cases branch)
       (simp_all add: one_due_generic_unlink_state_def
          one_due_event_check_state_def one_due_event_unlink_state_def
          one_due_raise_top_state_def one_due_ready_state_def Let_def)
qed

lemma one_due_phase_captured_keyD:
  assumes rel: "one_due_phase_rel C branch entry phase current"
    and after_due: "phase \<noteq> DueOwned"
  shows
    "ods_captured_generic_key current =
       Some (ods_generic_payload entry (odc_task C))"
proof -
  have current:
    "current = one_due_snapshot_at C branch phase entry"
    by (rule one_due_phase_rel_currentD[OF rel])
  show ?thesis
    using current after_due
    by (cases phase; cases branch)
       (simp_all add: one_due_generic_unlink_state_def
          one_due_event_check_state_def one_due_event_unlink_state_def
          one_due_raise_top_state_def one_due_ready_state_def Let_def)
qed

lemma one_due_phase_captured_due_keyD:
  assumes rel: "one_due_phase_rel C branch entry phase current"
    and after_due: "phase \<noteq> DueOwned"
  shows
    "ods_captured_generic_key current =
       Some (item_key (ods_generic_family entry (odc_delayed_root C))
         (Generic (odc_task C))) \<and>
     ods_generic_payload entry (odc_task C) \<le> odc_tick C"
proof -
  have entry_rel: "one_due_entry_rel C branch entry"
    by (rule one_due_phase_rel_entryD[OF rel])
  have captured:
    "ods_captured_generic_key current =
       Some (ods_generic_payload entry (odc_task C))"
    by (rule one_due_phase_captured_keyD[OF rel after_due])
  show ?thesis
    using entry_rel captured by (simp add: one_due_entry_rel_def)
qed

text \<open>Removal really leaves the target node absent; this uses the
  distinctness carried by xlist_wf rather than silently assuming no duplicate
  task identities.\<close>

lemma one_due_generic_unlink_absent:
  assumes entry: "one_due_entry_rel C branch S"
  shows
    "Generic (odc_task C) \<notin>
       set (ring (ods_generic_family
         (one_due_generic_unlink_state C S) (odc_delayed_root C)))"
proof -
  have root: "odc_delayed_root C \<in> odc_generic_roots C"
    using entry by (auto simp: one_due_entry_rel_def one_due_context_wf_def)
  have wf: "xlist_wf (ods_generic_family S (odc_delayed_root C))"
    using entry root
    by (auto simp: one_due_entry_rel_def one_due_family_shape_def)
  have distinct:
    "distinct (ring (ods_generic_family S (odc_delayed_root C)))"
    using wf by (simp add: xlist_wf_def)
  have member:
    "Generic (odc_task C) \<in>
       set (ring (ods_generic_family S (odc_delayed_root C)))"
    using entry by (simp add: one_due_entry_rel_def)
  have absent:
    "Generic (odc_task C) \<notin>
       set (remove1 (Generic (odc_task C))
         (ring (ods_generic_family S (odc_delayed_root C))))"
    by (rule raw_distinct_member_notin_remove1[OF distinct member])
  show ?thesis
    using absent
    by (simp add: one_due_generic_unlink_state_def list_remove_abs_def)
qed

lemma one_due_event_unlink_absent:
  assumes entry: "one_due_entry_rel C branch S"
  shows
    "\<forall>r\<in>odc_event_roots C.
       Event (odc_task C) \<notin>
         set (ring (ods_event_family
           (one_due_event_unlink_state C branch
             (one_due_event_check_state branch
               (one_due_generic_unlink_state C S))) r))"
proof (cases branch)
  case (DueEventLinked owner)
  from entry DueEventLinked have owner_ext:
      "owner \<in> one_due_external_roots C"
    and owner_member:
      "Event (odc_task C) \<in>
        set (ring (ods_event_family S owner))"
    by (simp_all add: one_due_entry_rel_def)
  have owner_root: "owner \<in> odc_event_roots C"
    using owner_ext by (auto simp: one_due_external_roots_def)
  have shape: "one_due_family_shape C S"
    using entry by (simp add: one_due_entry_rel_def)
  have owner_wf: "xlist_wf (ods_event_family S owner)"
    using shape owner_root by (auto simp: one_due_family_shape_def)
  have owner_distinct: "distinct (ring (ods_event_family S owner))"
    using owner_wf by (simp add: xlist_wf_def)
  have owner_absent:
    "Event (odc_task C) \<notin>
       set (remove1 (Event (odc_task C))
         (ring (ods_event_family S owner)))"
    by (rule raw_distinct_member_notin_remove1[
      OF owner_distinct owner_member])
  show ?thesis
  proof (intro ballI)
    fix r
    assume root: "r \<in> odc_event_roots C"
    show
      "Event (odc_task C) \<notin>
       set (ring (ods_event_family
         (one_due_event_unlink_state C branch
           (one_due_event_check_state branch
             (one_due_generic_unlink_state C S))) r))"
    proof (cases "r = owner")
      case True
      show ?thesis
        using True DueEventLinked owner_absent
        by (simp add: one_due_generic_unlink_state_def
            one_due_event_check_state_def one_due_event_unlink_state_def
            list_remove_abs_def)
    next
      case False
      have disjoint:
        "set (ring (ods_event_family S owner)) \<inter>
         set (ring (ods_event_family S r)) = {}"
        using shape owner_root root False
        by (auto simp: one_due_family_shape_def)
      have not_member:
        "Event (odc_task C) \<notin>
          set (ring (ods_event_family S r))"
        using disjoint owner_member by blast
      show ?thesis
        using False DueEventLinked not_member
        by (simp add: one_due_generic_unlink_state_def
            one_due_event_check_state_def one_due_event_unlink_state_def)
    qed
  qed
next
  case DueEventNull
  have absent:
    "\<forall>r\<in>odc_event_roots C.
       Event (odc_task C) \<notin> set (ring (ods_event_family S r))"
    using entry DueEventNull by (simp add: one_due_entry_rel_def)
  show ?thesis
    using absent DueEventNull
    by (simp add: one_due_generic_unlink_state_def
        one_due_event_check_state_def one_due_event_unlink_state_def)
qed

lemma one_due_event_checked_branchD:
  assumes rel: "one_due_phase_rel C branch entry EventChecked current"
  shows "ods_checked_event current = Some branch"
  using one_due_phase_rel_currentD[OF rel]
  by (simp add: one_due_generic_unlink_state_def
      one_due_event_check_state_def)

lemma one_due_event_unlinked_branchD:
  assumes rel: "one_due_phase_rel C branch entry EventUnlinked current"
  shows
    "ods_checked_event current = Some branch \<and>
     (\<forall>r\<in>odc_event_roots C.
       Event (odc_task C) \<notin>
         set (ring (ods_event_family current r)))"
proof -
  have entry_rel: "one_due_entry_rel C branch entry"
    by (rule one_due_phase_rel_entryD[OF rel])
  have current:
    "current = one_due_snapshot_at C branch EventUnlinked entry"
    by (rule one_due_phase_rel_currentD[OF rel])
  have absent:
    "\<forall>r\<in>odc_event_roots C.
       Event (odc_task C) \<notin>
         set (ring (ods_event_family
           (one_due_event_unlink_state C branch
             (one_due_event_check_state branch
               (one_due_generic_unlink_state C entry))) r))"
    by (rule one_due_event_unlink_absent[OF entry_rel])
  show ?thesis
    using current absent
    by (cases branch)
       (simp_all add: one_due_generic_unlink_state_def
          one_due_event_check_state_def one_due_event_unlink_state_def)
qed

lemma one_due_top_raisedD:
  assumes rel: "one_due_phase_rel C branch entry TopRaised current"
  shows
    "ods_top current =
       max (odc_entry_top C) (odc_priority C (odc_task C))"
proof -
  have entry_rel: "one_due_entry_rel C branch entry"
    by (rule one_due_phase_rel_entryD[OF rel])
  have top: "ods_top entry = odc_entry_top C"
    using entry_rel by (simp add: one_due_entry_rel_def)
  have current:
    "current = one_due_snapshot_at C branch TopRaised entry"
    by (rule one_due_phase_rel_currentD[OF rel])
  show ?thesis
    using current top
    by (cases branch)
       (simp_all add: one_due_generic_unlink_state_def
          one_due_event_check_state_def one_due_event_unlink_state_def
          one_due_raise_top_state_def)
qed

text \<open>The ready insertion is into the root derived from the arbitrary
  priority map, uses exactly the captured Generic key, and frames every other
  Generic root.\<close>

lemma one_due_entry_target_absent:
  assumes entry: "one_due_entry_rel C branch S"
  shows
    "Generic (odc_task C) \<notin>
       set (ring (ods_generic_family S (one_due_target_root C)))"
proof -
  have roots:
    "odc_delayed_root C \<in> odc_generic_roots C \<and>
     one_due_target_root C \<in> odc_generic_roots C \<and>
     odc_delayed_root C \<noteq> one_due_target_root C"
    using entry
    by (auto simp: one_due_entry_rel_def one_due_context_wf_def)
  have member:
    "Generic (odc_task C) \<in>
       set (ring (ods_generic_family S (odc_delayed_root C)))"
    using entry by (simp add: one_due_entry_rel_def)
  have disjoint:
    "set (ring (ods_generic_family S (odc_delayed_root C))) \<inter>
     set (ring (ods_generic_family S (one_due_target_root C))) = {}"
    using entry roots
    by (auto simp: one_due_entry_rel_def one_due_family_shape_def)
  show ?thesis using member disjoint by blast
qed

lemma one_due_ready_inserted_member_and_key:
  assumes entry: "one_due_entry_rel C branch S"
  shows
    "Generic (odc_task C) \<in>
       set (ring (ods_generic_family
         (one_due_snapshot_at C branch GenericReady S)
         (one_due_target_root C))) \<and>
     item_key (ods_generic_family
       (one_due_snapshot_at C branch GenericReady S)
       (one_due_target_root C))
       (Generic (odc_task C)) = ods_generic_payload S (odc_task C) \<and>
     ods_captured_generic_key
       (one_due_snapshot_at C branch GenericReady S) =
       Some (ods_generic_payload S (odc_task C))"
proof -
  let ?target = "one_due_target_root C"
  let ?node = "Generic (odc_task C)"
  let ?q = "ods_generic_family S ?target"
  let ?before =
    "one_due_raise_top_state C
      (one_due_event_unlink_state C branch
        (one_due_event_check_state branch
          (one_due_generic_unlink_state C S)))"
  have target_root: "?target \<in> odc_generic_roots C"
    using entry
    by (auto simp: one_due_entry_rel_def one_due_context_wf_def)
  have target_ne_delayed:
    "?target \<noteq> odc_delayed_root C"
    using entry
    by (auto simp: one_due_entry_rel_def one_due_context_wf_def)
  have wf: "xlist_wf ?q"
    using entry target_root
    by (auto simp: one_due_entry_rel_def one_due_family_shape_def)
  have absent: "?node \<notin> set (ring ?q)"
    by (rule one_due_entry_target_absent[OF entry])
  have inserted_wf:
    "xlist_wf
       (list_insert_end_abs ?node (ods_generic_payload S (odc_task C)) ?q)"
    by (rule list_insert_end_preserves_wf[OF wf absent])
  have inserted_cursor:
    "cursor
       (list_insert_end_abs ?node (ods_generic_payload S (odc_task C)) ?q) =
     Some ?node"
    by (simp add: list_insert_end_abs_def)
  have inserted_member:
    "?node \<in>
       set (ring
         (list_insert_end_abs ?node
           (ods_generic_payload S (odc_task C)) ?q))"
    using inserted_wf inserted_cursor by (simp add: xlist_wf_def)
  have inserted_key:
    "item_key
       (list_insert_end_abs ?node
         (ods_generic_payload S (odc_task C)) ?q) ?node =
     ods_generic_payload S (odc_task C)"
    by (simp add: list_insert_end_abs_def)
  have target_before:
    "ods_generic_family ?before ?target = ?q"
    using target_ne_delayed
    by (cases branch)
       (simp_all add: one_due_raise_top_state_def
          one_due_event_unlink_state_def one_due_event_check_state_def
          one_due_generic_unlink_state_def one_due_context_wf_def
          one_due_entry_rel_def)
  have payload_before:
    "ods_generic_payload ?before (odc_task C) =
     ods_generic_payload S (odc_task C)"
    by (cases branch)
       (simp_all add: one_due_raise_top_state_def
          one_due_event_unlink_state_def one_due_event_check_state_def
          one_due_generic_unlink_state_def)
  have captured_before:
    "ods_captured_generic_key ?before =
     Some (ods_generic_payload S (odc_task C))"
    by (cases branch)
       (simp_all add: one_due_raise_top_state_def
          one_due_event_unlink_state_def one_due_event_check_state_def
          one_due_generic_unlink_state_def)
  show ?thesis
    using inserted_member inserted_key target_before payload_before
      captured_before
    by (simp add: one_due_ready_state_def Let_def)
qed

lemma one_due_generic_readyD:
  assumes rel: "one_due_phase_rel C branch entry GenericReady current"
  shows
    "Generic (odc_task C) \<in>
       set (ring (ods_generic_family current (one_due_target_root C))) \<and>
     item_key (ods_generic_family current (one_due_target_root C))
       (Generic (odc_task C)) =
       ods_generic_payload entry (odc_task C) \<and>
     ods_captured_generic_key current =
       Some (ods_generic_payload entry (odc_task C)) \<and>
     ods_top current =
       max (odc_entry_top C) (odc_priority C (odc_task C)) \<and>
     (\<forall>r\<in>odc_event_roots C.
       Event (odc_task C) \<notin>
         set (ring (ods_event_family current r)))"
proof -
  have entry_rel: "one_due_entry_rel C branch entry"
    by (rule one_due_phase_rel_entryD[OF rel])
  let ?before =
    "one_due_raise_top_state C
      (one_due_event_unlink_state C branch
        (one_due_event_check_state branch
          (one_due_generic_unlink_state C entry)))"
  have inserted:
    "Generic (odc_task C) \<in>
       set (ring (ods_generic_family
         (one_due_snapshot_at C branch GenericReady entry)
         (one_due_target_root C))) \<and>
     item_key (ods_generic_family
       (one_due_snapshot_at C branch GenericReady entry)
       (one_due_target_root C))
       (Generic (odc_task C)) =
       ods_generic_payload entry (odc_task C) \<and>
     ods_captured_generic_key
       (one_due_snapshot_at C branch GenericReady entry) =
       Some (ods_generic_payload entry (odc_task C))"
    by (rule one_due_ready_inserted_member_and_key[OF entry_rel])
  have event_absent:
    "\<forall>r\<in>odc_event_roots C.
       Event (odc_task C) \<notin>
         set (ring (ods_event_family ?before r))"
    using one_due_event_unlink_absent[OF entry_rel]
    by (simp add: one_due_raise_top_state_def)
  have top:
    "ods_top ?before =
       max (odc_entry_top C) (odc_priority C (odc_task C))"
    using entry_rel
    by (cases branch)
       (simp_all add: one_due_entry_rel_def one_due_generic_unlink_state_def
          one_due_event_check_state_def one_due_event_unlink_state_def
          one_due_raise_top_state_def)
  have current:
    "current = one_due_snapshot_at C branch GenericReady entry"
    using one_due_phase_rel_currentD[OF rel] by simp
  show ?thesis
    using inserted event_absent top current
    by (simp add: one_due_ready_state_def Let_def)
qed

end
