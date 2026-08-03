theory Scheduler_Resume_Generated_Drained_Relabel
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Drained_Family.Scheduler_Resume_Generated_Drained_Family"
begin

text \<open>
  The drained raw Generic family relabels, root by root, to the abstract
  ready-inserted snapshot family: at the awakened task's ready queue the raw
  ring gains its Generic item exactly where the abstract ring gains
  \<open>Generic t\<close> with its context key, and every other root keeps the removal
  relabel unchanged.  This is the decoder-level link the drained gate
  relation needs between the concrete heap and the pure snapshot.
\<close>

lemma resume_pending_drained_abs_family_eq:
  "rps_generic_family
     (resume_pending_ready_insert_state C t
       (resume_pending_raise_top_state C t
         (resume_pending_generic_unlink_state C t
           (resume_pending_event_unlink_state C t S)))) =
   (rps_generic_family
     (resume_pending_generic_unlink_state C t
       (resume_pending_event_unlink_state C t S)))
     (rpc_ready_root C (rpc_priority C t) :=
       list_insert_end_abs (Generic t) (rpc_K_G C t)
         (rps_generic_family
           (resume_pending_generic_unlink_state C t
             (resume_pending_event_unlink_state C t S))
           (rpc_ready_root C (rpc_priority C t))))"
  by (simp add: resume_pending_ready_insert_state_def
      resume_pending_raise_top_state_def Let_def)

theorem resume_pending_drained_generic_relabel:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
    and root: "g \<in> rpc_generic_roots C"
  shows
    "xlist_relabel (sd_node_decode D)
       (resume_pending_drained_generic_fam C D t c generic_raw g)
       (rps_generic_family
         (resume_pending_ready_insert_state C t
           (resume_pending_raise_top_state C t
             (resume_pending_generic_unlink_state C t
               (resume_pending_event_unlink_state C t S)))) g)"
proof -
  let ?hR = "resume_pending_generic_remove_heap D t c"
  let ?target = "rpc_ready_root C (rpc_priority C t)"
  let ?fam = "resume_pending_generic_raw_after C D t generic_raw"
  let ?p = "resume_pending_generic_raw_ptr D t"
  let ?abs = "rps_generic_family
    (resume_pending_generic_unlink_state C t
      (resume_pending_event_unlink_state C t S))"
  have t_live: "t \<in> rpc_live C"
    by (rule resume_pending_gate_head_liveD[OF rel tasks])
  note post = resume_pending_generic_remove_family_post[OF rel tasks]
  have relabel_after:
    "xlist_relabel (sd_node_decode D) (?fam g) (?abs g)"
    using post root by blast
  show ?thesis
  proof (cases "g = ?target")
    case False
    have raw_same:
      "resume_pending_drained_generic_fam C D t c generic_raw g = ?fam g"
      using False
      by (simp add: resume_pending_drained_generic_fam_def
          scheduler_family_insert_end_raw_def)
    have abs_same:
      "rps_generic_family
         (resume_pending_ready_insert_state C t
           (resume_pending_raise_top_state C t
             (resume_pending_generic_unlink_state C t
               (resume_pending_event_unlink_state C t S)))) g = ?abs g"
      using False
      by (simp add: resume_pending_drained_abs_family_eq)
    show ?thesis
      using relabel_after raw_same abs_same by simp
  next
    case True
    have heap_base:
      "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
         (resume_pending_top_raised_state D t c)) = ?hR"
      using resume_pending_top_raised_semantics[OF rel tasks] by blast
    have pre:
      "scheduler_family_pre_rel ?hR (rpc_generic_roots C) ?fam
         (rpc_live C) D"
      using resume_pending_top_raised_generic_family[OF rel tasks]
        heap_base by simp
    have target_root: "?target \<in> rpc_generic_roots C"
      by (rule resume_pending_ready_target_in_roots[OF rel tasks])
    have raw_rel: "raw_xlist_rel ?hR ?target (?fam ?target)"
      using pre target_root
      by (auto simp: scheduler_family_pre_rel_def raw_family_rel_def)
    have raw_wf: "xlist_wf (?fam ?target)"
      using raw_rel
      by (simp add: raw_xlist_rel_def raw_xlist_view_def)
    have abs_wf_all:
      "\<forall>lp\<in>rpc_generic_roots C.
         xlist_wf (scheduler_family_remove_abs
           (rps_generic_family
             (resume_pending_event_unlink_state C t S))
           (rpc_generic_owner C t) (Generic t) lp)"
      using post
      by (simp add: scheduler_node_kind_family_remove_post_def Let_def)
    have abs_eq:
      "scheduler_family_remove_abs
         (rps_generic_family (resume_pending_event_unlink_state C t S))
         (rpc_generic_owner C t) (Generic t) = ?abs"
      by (simp add: scheduler_family_remove_abs_def
          resume_pending_generic_unlink_state_def
          resume_pending_event_unlink_state_def)
    have abs_wf: "xlist_wf (?abs ?target)"
      using abs_wf_all target_root abs_eq by simp
    have not_owner: "rpc_generic_owner C t \<noteq> ?target"
      by (rule resume_pending_ready_target_not_owner[OF rel tasks])
    have entry_unique:
      "\<forall>g\<in>rpc_generic_roots C.
         Generic t \<in> set (ring (rps_generic_family S g)) \<longleftrightarrow>
           g = rpc_generic_owner C t"
      using resume_pending_gate_pure_entryD[OF rel] tasks
      by (simp add: resume_pending_entry_rel_def)
    have abs_target_entry:
      "?abs ?target = rps_generic_family S ?target"
      using not_owner
      by (simp add: resume_pending_generic_unlink_state_def
          resume_pending_event_unlink_state_def)
    have abs_fresh: "Generic t \<notin> set (ring (?abs ?target))"
      using entry_unique target_root not_owner abs_target_entry by simp
    have live_abs: "t \<in> sa_live a"
      using rel t_live
      unfolding resume_pending_gate_entry_rel_def Let_def by blast
    have decode:
      "sd_node_decode D ?p = Some (Generic t)"
      using scheduler_node_decode_Generic_iff[
        OF resume_pending_gate_decoderD[OF rel],
        where p="?p" and t=t] live_abs
      by (simp add: resume_pending_generic_raw_ptr_def)
    have new_key: "raw_key_at ?hR ?p = rpc_K_G C t"
      using post t_live by blast
    note preserved = xlist_relabel_insert_end_preserved[
      OF relabel_after[unfolded True] raw_wf abs_wf abs_fresh decode
        new_key]
    have raw_target:
      "resume_pending_drained_generic_fam C D t c generic_raw ?target =
       list_insert_end_abs ?p (raw_key_at ?hR ?p) (?fam ?target)"
      by (simp add: resume_pending_drained_generic_fam_def
          scheduler_family_insert_end_raw_def)
    have abs_target:
      "rps_generic_family
         (resume_pending_ready_insert_state C t
           (resume_pending_raise_top_state C t
             (resume_pending_generic_unlink_state C t
               (resume_pending_event_unlink_state C t S)))) ?target =
       list_insert_end_abs (Generic t) (rpc_K_G C t) (?abs ?target)"
      by (simp add: resume_pending_drained_abs_family_eq)
    show ?thesis
      using preserved raw_target abs_target True by simp
  qed
qed

end
