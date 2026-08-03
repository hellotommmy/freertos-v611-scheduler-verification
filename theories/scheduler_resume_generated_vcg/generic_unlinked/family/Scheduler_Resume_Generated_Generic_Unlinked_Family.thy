theory Scheduler_Resume_Generated_Generic_Unlinked_Family
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Generic_Unlinked_Source.Scheduler_Resume_Generated_Generic_Unlinked_Source"
begin

lemma resume_pending_generic_remove_family_post:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "scheduler_node_kind_family_remove_post D
       (resume_pending_event_remove_heap D t c)
       (resume_pending_generic_remove_heap D t c)
       (rpc_generic_roots C) generic_raw
       (rps_generic_family (resume_pending_event_unlink_state C t S))
       (rpc_live C) (rpc_generic_owner C t)
       (resume_pending_generic_raw_ptr D t) (Generic t) \<and>
     (\<forall>g\<in>rpc_generic_roots C.
       set (ring (resume_pending_generic_raw_after C D t generic_raw g))
         \<subseteq> resume_pending_generic_raw_set (rpc_live C) D) \<and>
     (\<forall>g\<in>rpc_generic_roots C.
       xlist_relabel (sd_node_decode D)
         (resume_pending_generic_raw_after C D t generic_raw g)
         (rps_generic_family
           (resume_pending_generic_unlink_state C t
             (resume_pending_event_unlink_state C t S)) g)) \<and>
     (\<forall>u\<in>rpc_live C.
       raw_key_at (resume_pending_generic_remove_heap D t c)
         (resume_pending_generic_raw_ptr D u) = rpc_K_G C u)"
proof -
  let ?hE = "resume_pending_event_remove_heap D t c"
  let ?owner = "rpc_generic_owner C t"
  let ?p = "resume_pending_generic_raw_ptr D t"
  have pre:
    "scheduler_family_pre_rel ?hE (rpc_generic_roots C)
       generic_raw (rpc_live C) D"
    by (rule resume_pending_event_remove_generic_family_frame[OF rel tasks])
  have laws: "universal_decoder_laws (rpc_live C) D"
    by (rule resume_pending_gate_decoder_lawsD[OF rel])
  have owner_entry:
    "scheduler_delay_owner_entry_rel ?hE (rpc_generic_roots C)
       generic_raw ?owner ?p"
    by (rule resume_pending_event_remove_generic_owner_frame[OF rel tasks])
  have owner: "?owner \<in> rpc_generic_roots C"
    using owner_entry by (simp add: scheduler_delay_owner_entry_rel_def)
  have live: "t \<in> rpc_live C"
    by (rule resume_pending_gate_head_liveD[OF rel tasks])
  have member: "?p \<in> set (ring (generic_raw ?owner))"
    by (rule scheduler_delay_owner_entry_member[OF owner_entry])
  have generic_only:
    "\<And>g. g \<in> rpc_generic_roots C \<Longrightarrow>
      set (ring (generic_raw g)) \<subseteq>
        scheduler_family_generic_raw_set (rpc_live C) D"
  proof -
    fix g
    assume root: "g \<in> rpc_generic_roots C"
    have subset:
      "set (ring (generic_raw g)) \<subseteq>
        resume_pending_generic_raw_set (rpc_live C) D"
      using rel root
      unfolding resume_pending_gate_entry_rel_def Let_def
      by blast
    show
      "set (ring (generic_raw g)) \<subseteq>
        scheduler_family_generic_raw_set (rpc_live C) D"
      using subset
      by (simp add: resume_pending_generic_raw_set_def
          scheduler_family_generic_raw_set_def
          resume_pending_generic_raw_ptr_def
          scheduler_family_generic_raw_ptr_def)
  qed
  have relabels:
    "\<And>g. g \<in> rpc_generic_roots C \<Longrightarrow>
      xlist_relabel (sd_node_decode D) (generic_raw g)
        (rps_generic_family (resume_pending_event_unlink_state C t S) g)"
  proof -
    fix g
    assume root: "g \<in> rpc_generic_roots C"
    have old:
      "xlist_relabel (sd_node_decode D) (generic_raw g)
        (rps_generic_family S g)"
      using rel root
      unfolding resume_pending_gate_entry_rel_def Let_def
      by blast
    show
      "xlist_relabel (sd_node_decode D) (generic_raw g)
        (rps_generic_family (resume_pending_event_unlink_state C t S) g)"
      using old by (simp add: resume_pending_event_unlink_state_def)
  qed
  have abs_wf:
    "\<And>g. g \<in> rpc_generic_roots C \<Longrightarrow>
      xlist_wf (rps_generic_family
        (resume_pending_event_unlink_state C t S) g)"
  proof -
    fix g
    assume root: "g \<in> rpc_generic_roots C"
    have shape: "resume_pending_family_shape C S"
      using resume_pending_gate_pure_entryD[OF rel]
      by (simp add: resume_pending_entry_rel_def)
    show
      "xlist_wf (rps_generic_family
        (resume_pending_event_unlink_state C t S) g)"
      using shape root
      by (simp add: resume_pending_family_shape_def
          resume_pending_event_unlink_state_def)
  qed
  have keys:
    "\<And>u. u \<in> rpc_live C \<Longrightarrow>
      raw_key_at ?hE (scheduler_family_generic_raw_ptr D u) = rpc_K_G C u"
    using resume_pending_event_remove_generic_keys_frame[OF rel tasks]
    by (simp add: scheduler_family_generic_raw_ptr_def
        resume_pending_generic_raw_ptr_def)
  have member_source:
    "scheduler_family_generic_raw_ptr D t \<in>
       set (ring (generic_raw ?owner))"
    using member
    by (simp add: scheduler_family_generic_raw_ptr_def
        resume_pending_generic_raw_ptr_def)
  have instantiated:
    "scheduler_node_kind_family_remove_post D ?hE
       (raw_remove_concrete_heap ?hE
         (scheduler_family_generic_raw_ptr D t))
       (rpc_generic_roots C) generic_raw
       (rps_generic_family (resume_pending_event_unlink_state C t S))
       (rpc_live C) ?owner (scheduler_family_generic_raw_ptr D t)
       (Generic t) \<and>
     (\<forall>g\<in>rpc_generic_roots C.
       set (ring (scheduler_family_remove_raw generic_raw ?owner
         (scheduler_family_generic_raw_ptr D t) g)) \<subseteq>
         scheduler_family_generic_raw_set (rpc_live C) D) \<and>
     (\<forall>g\<in>rpc_generic_roots C.
       xlist_relabel (sd_node_decode D)
         (scheduler_family_remove_raw generic_raw ?owner
           (scheduler_family_generic_raw_ptr D t) g)
         (scheduler_family_remove_abs
           (rps_generic_family (resume_pending_event_unlink_state C t S))
           ?owner (Generic t) g)) \<and>
     (\<forall>u\<in>rpc_live C.
       raw_key_at
         (raw_remove_concrete_heap ?hE
           (scheduler_family_generic_raw_ptr D t))
         (scheduler_family_generic_raw_ptr D u) = rpc_K_G C u)"
    by (rule scheduler_generic_task_family_remove_interface[
      OF pre laws owner live member_source generic_only relabels abs_wf keys])
  show ?thesis
    using instantiated
    by (simp add: resume_pending_generic_remove_heap_def
        resume_pending_generic_raw_after_def
        resume_pending_generic_abs_after
        scheduler_family_generic_raw_ptr_def
        resume_pending_generic_raw_ptr_def
        scheduler_family_generic_raw_set_def
        resume_pending_generic_raw_set_def)
qed

end
