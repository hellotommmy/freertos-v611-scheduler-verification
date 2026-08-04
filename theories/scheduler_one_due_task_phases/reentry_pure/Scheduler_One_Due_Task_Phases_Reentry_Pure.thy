theory Scheduler_One_Due_Task_Phases_Reentry_Pure
  imports
    "EAL6_FreeRTOS_V611_Scheduler_One_Due_Task_Phases_Delayed_Head.Scheduler_One_Due_Task_Phases_Delayed_Head"
begin

text \<open>
  Pure re-entry witnesses for the next due task.  After one completed
  tick-body iteration the context advances to the decoded head of the
  shrunk delayed ring with the raised top, and the snapshot is the
  completed five-phase state with the capture and check registers
  cleared.  The lemmas below give the component facts of the pure entry
  relation at those witnesses; root-membership side conditions that the
  pure layer cannot re-establish stay explicit premises for the gate
  layer.
\<close>

definition one_due_reentry_context ::
  "('tid, 'root) one_due_context \<Rightarrow> 'tid \<Rightarrow>
   ('tid, 'root) one_due_context"
where
  "one_due_reentry_context C u =
     C\<lparr>odc_task := u,
       odc_entry_top :=
         max (odc_entry_top C) (odc_priority C (odc_task C))\<rparr>"

definition one_due_reentry_snapshot ::
  "('tid, 'root) one_due_context \<Rightarrow>
   'root one_due_event_branch \<Rightarrow>
   ('tid, 'root) one_due_snapshot \<Rightarrow>
   ('tid, 'root) one_due_snapshot"
where
  "one_due_reentry_snapshot C branch S =
     (one_due_ready_state C
       (one_due_raise_top_state C
         (one_due_event_unlink_state C branch
           (one_due_event_check_state branch
             (one_due_generic_unlink_state C S)))))
     \<lparr>ods_captured_generic_key := None,
      ods_checked_event := None\<rparr>"

lemma one_due_reentry_context_components:
  "odc_live (one_due_reentry_context C u) = odc_live C"
  "odc_task (one_due_reentry_context C u) = u"
  "odc_generic_roots (one_due_reentry_context C u) =
     odc_generic_roots C"
  "odc_event_roots (one_due_reentry_context C u) =
     odc_event_roots C"
  "odc_delayed_root (one_due_reentry_context C u) =
     odc_delayed_root C"
  "odc_ready_root (one_due_reentry_context C u) = odc_ready_root C"
  "odc_pending_root (one_due_reentry_context C u) =
     odc_pending_root C"
  "odc_priority (one_due_reentry_context C u) = odc_priority C"
  "odc_tick (one_due_reentry_context C u) = odc_tick C"
  "odc_entry_top (one_due_reentry_context C u) =
     max (odc_entry_top C) (odc_priority C (odc_task C))"
  "odc_K_E (one_due_reentry_context C u) = odc_K_E C"
  by (simp_all add: one_due_reentry_context_def)

lemma one_due_reentry_snapshot_registers:
  "ods_captured_generic_key
     (one_due_reentry_snapshot C branch S) = None"
  "ods_checked_event (one_due_reentry_snapshot C branch S) = None"
  by (simp_all add: one_due_reentry_snapshot_def)

lemma one_due_reentry_snapshot_top:
  "ods_top (one_due_reentry_snapshot C branch S) =
     max (ods_top S) (odc_priority C (odc_task C))"
  by (cases branch)
     (simp_all add: one_due_reentry_snapshot_def
       one_due_ready_state_def one_due_raise_top_state_def
       one_due_event_unlink_state_def one_due_event_check_state_def
       one_due_generic_unlink_state_def Let_def)

lemma one_due_reentry_snapshot_payloads:
  "ods_generic_payload (one_due_reentry_snapshot C branch S) =
     ods_generic_payload S"
  "ods_event_payload (one_due_reentry_snapshot C branch S) =
     ods_event_payload S"
  by (cases branch;
      simp add: one_due_reentry_snapshot_def
        one_due_ready_state_def one_due_raise_top_state_def
        one_due_event_unlink_state_def one_due_event_check_state_def
        one_due_generic_unlink_state_def Let_def)+

lemma one_due_reentry_snapshot_generic_at:
  "ods_generic_family (one_due_reentry_snapshot C branch S) r =
     (let target = one_due_target_root C;
          removed =
            (ods_generic_family S)
              (odc_delayed_root C :=
                list_remove_abs (Generic (odc_task C))
                  (ods_generic_family S (odc_delayed_root C)))
      in if r = target
         then list_insert_end_abs (Generic (odc_task C))
                (ods_generic_payload S (odc_task C))
                (removed target)
         else removed r)"
  by (cases branch)
     (simp_all add: one_due_reentry_snapshot_def
       one_due_ready_state_def one_due_raise_top_state_def
       one_due_event_unlink_state_def one_due_event_check_state_def
       one_due_generic_unlink_state_def Let_def fun_upd_def)

lemma one_due_reentry_snapshot_event_at:
  "ods_event_family (one_due_reentry_snapshot C branch S) r =
     (case branch of
        DueEventLinked owner \<Rightarrow>
          if r = owner
          then list_remove_abs (Event (odc_task C))
                 (ods_event_family S owner)
          else ods_event_family S r
      | DueEventNull \<Rightarrow> ods_event_family S r)"
  by (cases branch)
     (simp_all add: one_due_reentry_snapshot_def
       one_due_ready_state_def one_due_raise_top_state_def
       one_due_event_unlink_state_def one_due_event_check_state_def
       one_due_generic_unlink_state_def Let_def fun_upd_def)

end
