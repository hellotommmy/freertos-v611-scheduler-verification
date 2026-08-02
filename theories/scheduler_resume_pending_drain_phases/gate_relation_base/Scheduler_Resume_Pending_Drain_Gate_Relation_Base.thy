theory Scheduler_Resume_Pending_Drain_Gate_Relation_Base
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Pending_Drain_Phases.Scheduler_Resume_Pending_Drain_Phases"
begin

text \<open>
  Concrete entry bridge.  It relates the pure prefix invariant to the existing
  TaskObservation, Generic raw-family and arbitrary Event-family relations.
  The Generic owner function is entry data: each pending task is proved to
  occupy exactly that one blocked root.  The ready target remains derived from
  its observed priority.  No post-state is assumed.
\<close>

definition resume_pending_generic_raw_ptr ::
  "'tid scheduler_decode \<Rightarrow> 'tid \<Rightarrow> raw_node_id"
where
  "resume_pending_generic_raw_ptr D t =
     abi_generic_list_item_ptr (sd_tcb_ptr D t)"

definition resume_pending_generic_raw_set ::
  "'tid set \<Rightarrow> 'tid scheduler_decode \<Rightarrow> raw_node_id set"
where
  "resume_pending_generic_raw_set live D =
     resume_pending_generic_raw_ptr D ` live"

definition resume_pending_owner_list_ptr ::
  "scheduler_roots \<Rightarrow>
   ('tid, xLIST_C ptr) resume_pending_context \<Rightarrow> 'tid \<Rightarrow>
   Scheduler_V611_Parse.xLIST_C ptr"
where
  "resume_pending_owner_list_ptr R C t =
     (if rpc_generic_owner C t = abi_list_ptr (sr_delayed_a R)
      then sr_delayed_a R
      else if rpc_generic_owner C t = abi_list_ptr (sr_delayed_b R)
      then sr_delayed_b R
      else sr_suspended R)"

definition resume_pending_gate_entry_rel ::
  "'tid scheduler_decode \<Rightarrow> scheduler_roots \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> 'tid scheduler_abs \<Rightarrow>
   ('tid, xLIST_C ptr) resume_pending_context \<Rightarrow>
   ('tid, xLIST_C ptr) resume_pending_snapshot \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   bool"
where
  "resume_pending_gate_entry_rel
      D R c a C S generic_raw event_raw \<longleftrightarrow>
     (let h = hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)
      in resume_pending_entry_rel C S \<and>
         core_wf a \<and>
         TaskObservationRel D h a \<and>
         scheduler_lists_rel D R c a \<and>
         scheduler_role_rel R c a \<and>
         scheduler_scalar_rel c a \<and>
         scheduler_current_rel D c a \<and>
         sa_suspend_depth a = 0 \<and>
         universal_decoder_laws (rpc_live C) D \<and>
         rpc_live C = sa_live a \<and>
         (\<forall>t\<in>rpc_live C. rpc_priority C t = sa_priority a t) \<and>
         rps_event_family S (rpc_pending_root C) = sa_pending a \<and>
         rpc_pending_root C = abi_list_ptr (sr_pending R) \<and>
         (\<forall>p<4.
            abi_list_ptr (sr_ready R p) \<in> rpc_generic_roots C) \<and>
         abi_list_ptr (sr_delayed_a R) \<in> rpc_generic_roots C \<and>
         abi_list_ptr (sr_delayed_b R) \<in> rpc_generic_roots C \<and>
         abi_list_ptr (sr_suspended R) \<in> rpc_generic_roots C \<and>
         (\<forall>t\<in>rpc_live C.
            rpc_ready_root C (rpc_priority C t) =
              abi_list_ptr (sr_ready R (rpc_priority C t))) \<and>
         (\<forall>t\<in>set (rpc_tasks C).
            rpc_generic_owner C t \<in>
              {abi_list_ptr (sr_delayed_a R),
               abi_list_ptr (sr_delayed_b R),
               abi_list_ptr (sr_suspended R)}) \<and>
         (\<forall>p<4.
            rps_generic_family S (abi_list_ptr (sr_ready R p)) =
              sa_ready a p) \<and>
         rps_generic_family S (abi_list_ptr (sr_delayed_a R)) =
           sa_delayed_a a \<and>
         rps_generic_family S (abi_list_ptr (sr_delayed_b R)) =
           sa_delayed_b a \<and>
         rps_generic_family S (abi_list_ptr (sr_suspended R)) =
           sa_suspended a \<and>
         rpc_entry_top C =
           unat (Scheduler_V611_Parse.globals.uxTopReadyPriority_' c) \<and>
         (\<exists>current\<in>rpc_live C.
            sa_current a = Some current \<and>
            rpc_current_priority C = rpc_priority C current) \<and>
         scheduler_family_pre_rel h (rpc_generic_roots C)
           generic_raw (rpc_live C) D \<and>
         (\<forall>g\<in>rpc_generic_roots C.
            set (ring (generic_raw g)) \<subseteq>
              resume_pending_generic_raw_set (rpc_live C) D) \<and>
         (\<forall>g\<in>rpc_generic_roots C.
            xlist_relabel (sd_node_decode D) (generic_raw g)
              (rps_generic_family S g)) \<and>
         (\<forall>t\<in>set (rpc_tasks C).
            scheduler_delay_owner_entry_rel h (rpc_generic_roots C)
              generic_raw (rpc_generic_owner C t)
              (resume_pending_generic_raw_ptr D t) \<and>
            raw_family_insert_geometry (rpc_generic_roots C) generic_raw
              (resume_pending_generic_raw_ptr D t)) \<and>
         (\<forall>t\<in>rpc_live C.
            raw_key_at h (resume_pending_generic_raw_ptr D t) =
              rpc_K_G C t) \<and>
         scheduler_event_root_family_rel D h (rpc_event_roots C)
           (rpc_pending_root C) event_raw (rps_event_family S)
           (rpc_live C) (rpc_K_E C) \<and>
         rpc_generic_roots C \<inter> rpc_event_roots C = {} \<and>
         (\<forall>g\<in>rpc_generic_roots C. \<forall>e\<in>rpc_event_roots C.
            raw_xlist_storage g (generic_raw g) \<inter>
              raw_xlist_storage e (event_raw e) = {}))"

lemma resume_pending_gate_pure_entryD:
  "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw
   \<Longrightarrow> resume_pending_entry_rel C S"
  by (simp add: resume_pending_gate_entry_rel_def Let_def)

lemma resume_pending_gate_generic_familyD:
  assumes rel:
    "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
  shows
    "scheduler_family_pre_rel
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (rpc_generic_roots C) generic_raw (rpc_live C) D"
  using rel
  unfolding resume_pending_gate_entry_rel_def Let_def
  by blast

lemma resume_pending_gate_event_familyD:
  assumes rel:
    "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
  shows
    "scheduler_event_root_family_rel D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (rpc_event_roots C) (rpc_pending_root C) event_raw
       (rps_event_family S) (rpc_live C) (rpc_K_E C)"
  using rel
  unfolding resume_pending_gate_entry_rel_def Let_def
  by blast

end
