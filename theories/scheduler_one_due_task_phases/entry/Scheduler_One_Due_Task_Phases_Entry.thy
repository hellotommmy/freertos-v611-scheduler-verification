theory Scheduler_One_Due_Task_Phases_Entry
  imports
    "EAL6_FreeRTOS_V611_Scheduler_One_Due_Task_Phases_Base.Scheduler_One_Due_Task_Phases_Base"
begin

text \<open>
  Gate-H entry bridge.  The abstract phase snapshot is tied simultaneously to
  the generated globals, TaskObservation, a Generic raw-root family, and the
  universal Event-root family.  The delayed root is the actual current
  delayed-list pointer and the ready target is derived from the arbitrary
  task priority; neither is supplied as a convenient post-state choice.
\<close>

definition one_due_generic_raw_ptr ::
  "'tid scheduler_decode \<Rightarrow> 'tid \<Rightarrow> raw_node_id"
where
  "one_due_generic_raw_ptr D t =
     abi_generic_list_item_ptr (sd_tcb_ptr D t)"

definition one_due_generic_raw_set ::
  "'tid set \<Rightarrow> 'tid scheduler_decode \<Rightarrow> raw_node_id set"
where
  "one_due_generic_raw_set live D =
     one_due_generic_raw_ptr D ` live"

definition one_due_gateH_entry_rel ::
  "'tid scheduler_decode \<Rightarrow> scheduler_roots \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> 'tid scheduler_abs \<Rightarrow>
   ('tid, xLIST_C ptr) one_due_context \<Rightarrow>
   xLIST_C ptr one_due_event_branch \<Rightarrow>
   ('tid, xLIST_C ptr) one_due_snapshot \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   bool"
where
  "one_due_gateH_entry_rel
      D R c a C branch S generic_raw event_raw \<longleftrightarrow>
     (let h = hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)
      in one_due_entry_rel C branch S \<and>
         TaskObservationRel D h a \<and>
         universal_decoder_laws (odc_live C) D \<and>
         odc_live C = sa_live a \<and>
         (\<forall>t\<in>odc_live C.
            odc_priority C t = sa_priority a t) \<and>
         odc_tick C = Scheduler_V611_Parse.globals.xTickCount_' c \<and>
         odc_entry_top C =
           unat (Scheduler_V611_Parse.globals.uxTopReadyPriority_' c) \<and>
         odc_delayed_root C =
           abi_list_ptr
             (Scheduler_V611_Parse.globals.pxDelayedTaskList_' c) \<and>
         odc_pending_root C = abi_list_ptr (sr_pending R) \<and>
         (\<forall>t\<in>odc_live C.
            odc_ready_root C (odc_priority C t) =
              abi_list_ptr (sr_ready R (odc_priority C t))) \<and>
         scheduler_family_pre_rel h (odc_generic_roots C)
           generic_raw (odc_live C) D \<and>
         (\<forall>r\<in>odc_generic_roots C.
            set (ring (generic_raw r)) \<subseteq>
              one_due_generic_raw_set (odc_live C) D) \<and>
         (\<forall>r\<in>odc_generic_roots C.
            xlist_relabel (sd_node_decode D) (generic_raw r)
              (ods_generic_family S r)) \<and>
         scheduler_delay_owner_entry_rel h (odc_generic_roots C)
           generic_raw (odc_delayed_root C)
           (one_due_generic_raw_ptr D (odc_task C)) \<and>
         raw_family_insert_geometry (odc_generic_roots C) generic_raw
           (one_due_generic_raw_ptr D (odc_task C)) \<and>
         scheduler_event_root_family_rel D h (odc_event_roots C)
           (odc_pending_root C) event_raw (ods_event_family S)
           (odc_live C) (odc_K_E C) \<and>
         (\<forall>t\<in>odc_live C.
            raw_key_at h (one_due_generic_raw_ptr D t) =
              ods_generic_payload S t) \<and>
         odc_generic_roots C \<inter> odc_event_roots C = {} \<and>
         (\<forall>g\<in>odc_generic_roots C. \<forall>e\<in>odc_event_roots C.
            raw_xlist_storage g (generic_raw g) \<inter>
              raw_xlist_storage e (event_raw e) = {}))"

lemma one_due_gateH_pure_entryD:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
  shows "one_due_entry_rel C branch S"
  using rel by (simp add: one_due_gateH_entry_rel_def Let_def)

lemma one_due_gateH_task_liveD:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
  shows "odc_task C \<in> odc_live C"
  using one_due_gateH_pure_entryD[OF rel]
  by (auto simp: one_due_entry_rel_def one_due_context_wf_def)

lemma one_due_gateH_generic_preD:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
  shows
    "scheduler_family_pre_rel
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (odc_generic_roots C) generic_raw (odc_live C) D"
  using rel
  unfolding one_due_gateH_entry_rel_def Let_def
  by blast

lemma one_due_gateH_event_relD:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
  shows
    "scheduler_event_root_family_rel D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (odc_event_roots C) (odc_pending_root C) event_raw
       (ods_event_family S) (odc_live C) (odc_K_E C)"
  using rel
  unfolding one_due_gateH_entry_rel_def Let_def
  by blast

lemma one_due_gateH_decoder_relD:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
  shows "scheduler_decode_rel D a"
proof -
  have pre: "scheduler_family_pre_rel
      (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
      (odc_generic_roots C) generic_raw (odc_live C) D"
    by (rule one_due_gateH_generic_preD[OF rel])
  have geometry: "universal_tcb_geometry (odc_live C) D"
    using pre by (simp add: scheduler_family_pre_rel_def)
  have laws: "universal_decoder_laws (odc_live C) D"
    using rel
    unfolding one_due_gateH_entry_rel_def Let_def
    by blast
  have live_eq: "sa_live a = odc_live C"
    using rel
    unfolding one_due_gateH_entry_rel_def Let_def
    by blast
  have universal: "universal_scheduler_geometry (odc_live C) D"
    using geometry laws by (simp add: universal_scheduler_geometry_def)
  show ?thesis
    by (rule universal_geometry_scheduler_decode_rel[OF universal live_eq])
qed

lemma one_due_gateH_decoder_lawsD:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
  shows "universal_decoder_laws (odc_live C) D"
  using rel
  unfolding one_due_gateH_entry_rel_def Let_def
  by blast

lemma one_due_gateH_generic_event_ptr_distinct:
  assumes rel:
      "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and generic_live: "u \<in> odc_live C"
    and event_live: "t \<in> odc_live C"
  shows
    "one_due_generic_raw_ptr D u \<noteq> event_item_raw_ptr D t"
proof
  assume equal:
    "one_due_generic_raw_ptr D u = event_item_raw_ptr D t"
  have laws: "universal_decoder_laws (odc_live C) D"
    by (rule one_due_gateH_decoder_lawsD[OF rel])
  have generic_decode:
    "sd_node_decode D (one_due_generic_raw_ptr D u) = Some (Generic u)"
    using universal_node_decode_Generic_iff[
      OF laws, where p="one_due_generic_raw_ptr D u" and t=u]
      generic_live
    by (simp add: one_due_generic_raw_ptr_def)
  have event_decode:
    "sd_node_decode D (event_item_raw_ptr D t) = Some (Event t)"
    using universal_node_decode_Event_iff[
      OF laws, where p="event_item_raw_ptr D t" and t=t]
      event_live
    by (simp add: event_item_raw_ptr_def)
  show False using generic_decode event_decode equal by simp
qed

lemma one_due_gateH_event_notin_generic_rootD:
  assumes rel:
      "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and event_live: "t \<in> odc_live C"
    and root: "g \<in> odc_generic_roots C"
  shows
    "event_item_raw_ptr D t \<notin> set (ring (generic_raw g))"
proof
  assume member:
    "event_item_raw_ptr D t \<in> set (ring (generic_raw g))"
  have subset:
    "set (ring (generic_raw g)) \<subseteq>
       one_due_generic_raw_set (odc_live C) D"
    using rel root
    unfolding one_due_gateH_entry_rel_def Let_def
    by blast
  then obtain u where generic_live: "u \<in> odc_live C"
      and equal:
        "event_item_raw_ptr D t = one_due_generic_raw_ptr D u"
    using member
    by (auto simp: one_due_generic_raw_set_def)
  have distinct:
    "one_due_generic_raw_ptr D u \<noteq> event_item_raw_ptr D t"
    by (rule one_due_gateH_generic_event_ptr_distinct[
      OF rel generic_live event_live])
  show False using equal distinct by simp
qed

lemma one_due_gateH_exact_rootsD:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
  shows
    "odc_delayed_root C =
       abi_list_ptr (Scheduler_V611_Parse.globals.pxDelayedTaskList_' c) \<and>
     one_due_target_root C =
       abi_list_ptr (sr_ready R (odc_priority C (odc_task C))) \<and>
     odc_delayed_root C \<noteq> one_due_target_root C \<and>
     odc_pending_root C = abi_list_ptr (sr_pending R)"
proof -
  have live: "odc_task C \<in> odc_live C"
    by (rule one_due_gateH_task_liveD[OF rel])
  have roots:
    "odc_delayed_root C \<noteq> one_due_target_root C"
    using one_due_gateH_pure_entryD[OF rel]
    by (auto simp: one_due_entry_rel_def one_due_context_wf_def)
  have delayed:
    "odc_delayed_root C =
       abi_list_ptr (Scheduler_V611_Parse.globals.pxDelayedTaskList_' c)"
    using rel
    unfolding one_due_gateH_entry_rel_def Let_def
    by blast
  have ready:
    "one_due_target_root C =
       abi_list_ptr (sr_ready R (odc_priority C (odc_task C)))"
    using rel live
    unfolding one_due_gateH_entry_rel_def one_due_target_root_def Let_def
    by blast
  have pending:
    "odc_pending_root C = abi_list_ptr (sr_pending R)"
    using rel
    unfolding one_due_gateH_entry_rel_def Let_def
    by blast
  show ?thesis
    using delayed ready roots pending by blast
qed

lemma one_due_gateH_priorityD:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
  shows
    "unat (Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
         (sd_tcb_ptr D (odc_task C)))) =
       odc_priority C (odc_task C)"
proof -
  have live: "odc_task C \<in> odc_live C"
    by (rule one_due_gateH_task_liveD[OF rel])
  have obs:
    "TaskObservationRel D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) a"
    using rel
    unfolding one_due_gateH_entry_rel_def Let_def
    by blast
  have abstract_priority:
    "odc_priority C (odc_task C) = sa_priority a (odc_task C)"
    using rel live
    unfolding one_due_gateH_entry_rel_def Let_def
    by blast
  have live_a: "odc_task C \<in> sa_live a"
    using rel live
    unfolding one_due_gateH_entry_rel_def Let_def
    by blast
  have observed:
    "unat (Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
         (sd_tcb_ptr D (odc_task C)))) =
       sa_priority a (odc_task C)"
    using TaskObservationRel_liveD[OF obs live_a] by simp
  show ?thesis
    using observed abstract_priority by simp
qed

lemma one_due_gateH_due_headD:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
  shows
    "scheduler_list_head_item
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (Scheduler_V611_Parse.globals.pxDelayedTaskList_' c) =
     scheduler_generic_item_ptr (sd_tcb_ptr D (odc_task C))"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  let ?root = "odc_delayed_root C"
  have root: "?root \<in> odc_generic_roots C"
    using one_due_gateH_pure_entryD[OF rel]
    by (auto simp: one_due_entry_rel_def one_due_context_wf_def)
  have raw: "raw_xlist_rel ?h ?root (generic_raw ?root)"
    using one_due_gateH_generic_preD[OF rel] root
    by (auto simp: scheduler_family_pre_rel_def raw_family_rel_def)
  have relabel:
    "xlist_relabel (sd_node_decode D) (generic_raw ?root)
       (ods_generic_family S ?root)"
    using rel root
    unfolding one_due_gateH_entry_rel_def Let_def
    by blast
  have lists:
    "sched_xlist_rel (sd_node_decode D) ?h ?root
       (ods_generic_family S ?root)"
    using raw relabel by (auto simp: sched_xlist_rel_def)
  obtain rest where head:
    "ring (ods_generic_family S ?root) =
       Generic (odc_task C) # rest"
    using one_due_gateH_pure_entryD[OF rel]
    by (auto simp: one_due_entry_rel_def)
  have root_eq:
    "?root = abi_list_ptr
       (Scheduler_V611_Parse.globals.pxDelayedTaskList_' c)"
    using one_due_gateH_exact_rootsD[OF rel] by simp
  have lists_source:
    "sched_xlist_rel (sd_node_decode D) ?h
       (abi_list_ptr
         (Scheduler_V611_Parse.globals.pxDelayedTaskList_' c))
       (ods_generic_family S ?root)"
    using lists root_eq by simp
  show ?thesis
    by (rule sched_xlist_rel_generic_head_ptr[
      OF lists_source one_due_gateH_decoder_relD[OF rel] head])
qed

lemma one_due_gateH_generic_owner_and_keyD:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
  shows
    "raw_family_members (odc_generic_roots C) generic_raw
       (one_due_generic_raw_ptr D (odc_task C)) =
         {odc_delayed_root C} \<and>
     raw_key_at (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (one_due_generic_raw_ptr D (odc_task C)) =
         ods_generic_payload S (odc_task C) \<and>
     ods_generic_payload S (odc_task C) \<le> odc_tick C"
proof -
  have live: "odc_task C \<in> odc_live C"
    by (rule one_due_gateH_task_liveD[OF rel])
  have owner:
    "scheduler_delay_owner_entry_rel
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (odc_generic_roots C) generic_raw (odc_delayed_root C)
       (one_due_generic_raw_ptr D (odc_task C))"
    using rel
    unfolding one_due_gateH_entry_rel_def Let_def
    by blast
  have members:
    "raw_family_members (odc_generic_roots C) generic_raw
       (one_due_generic_raw_ptr D (odc_task C)) =
       {odc_delayed_root C}"
    using owner
    unfolding scheduler_delay_owner_entry_rel_def
    by blast
  have key:
    "raw_key_at (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (one_due_generic_raw_ptr D (odc_task C)) =
       ods_generic_payload S (odc_task C)"
    using rel live
    unfolding one_due_gateH_entry_rel_def Let_def
    by blast
  have due:
    "ods_generic_payload S (odc_task C) \<le> odc_tick C"
    using one_due_gateH_pure_entryD[OF rel]
    unfolding one_due_entry_rel_def
    by blast
  show ?thesis using members key due by blast
qed

lemma one_due_gateH_total_K_E_entryD:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and live: "t \<in> odc_live C"
  shows
    "raw_key_at (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (event_item_raw_ptr D t) = odc_K_E C t"
  using scheduler_event_root_family_physical_keyD[
    OF one_due_gateH_event_relD[OF rel] live] .

lemma one_due_gateH_event_branchD:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
  shows
    "case branch of
       DueEventLinked owner \<Rightarrow>
         owner \<in> one_due_external_roots C \<and>
         event_item_raw_ptr D (odc_task C) \<in>
           set (ring (event_raw owner)) \<and>
         pvContainer_C
           (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
             (event_item_raw_ptr D (odc_task C))) =
           PTR_COERCE(xLIST_C \<rightarrow> unit) owner
     | DueEventNull \<Rightarrow>
         raw_family_members (odc_event_roots C) event_raw
           (event_item_raw_ptr D (odc_task C)) = {} \<and>
         pvContainer_C
           (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
             (event_item_raw_ptr D (odc_task C))) = NULL"
proof (cases branch)
  case (DueEventLinked owner)
  have live: "odc_task C \<in> odc_live C"
    by (rule one_due_gateH_task_liveD[OF rel])
  have pure: "one_due_entry_rel C branch S"
    by (rule one_due_gateH_pure_entryD[OF rel])
  from pure DueEventLinked have ext:
      "owner \<in> one_due_external_roots C"
    and abstract:
      "Event (odc_task C) \<in>
        set (ring (ods_event_family S owner))"
    by (simp_all add: one_due_entry_rel_def)
  have root: "owner \<in> odc_event_roots C"
    using ext by (auto simp: one_due_external_roots_def)
  have raw:
    "event_item_raw_ptr D (odc_task C) \<in>
       set (ring (event_raw owner))"
    using scheduler_event_root_family_member_iff[
      OF one_due_gateH_event_relD[OF rel] live root]
      abstract by simp
  have container:
    "pvContainer_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
         (event_item_raw_ptr D (odc_task C))) =
       PTR_COERCE(xLIST_C \<rightarrow> unit) owner"
    using scheduler_event_root_family_container_iff[
      OF one_due_gateH_event_relD[OF rel] live root]
      raw by simp
  show ?thesis using DueEventLinked ext raw container by simp
next
  case DueEventNull
  have live: "odc_task C \<in> odc_live C"
    by (rule one_due_gateH_task_liveD[OF rel])
  have pure: "one_due_entry_rel C branch S"
    by (rule one_due_gateH_pure_entryD[OF rel])
  have abstract_absent:
    "\<forall>r\<in>odc_event_roots C.
       Event (odc_task C) \<notin>
         set (ring (ods_event_family S r))"
    using pure DueEventNull by (simp add: one_due_entry_rel_def)
  have raw_absent:
    "raw_family_members (odc_event_roots C) event_raw
       (event_item_raw_ptr D (odc_task C)) = {}"
  proof (rule equals0I)
    fix r
    assume member:
      "r \<in> raw_family_members (odc_event_roots C) event_raw
        (event_item_raw_ptr D (odc_task C))"
    then have root: "r \<in> odc_event_roots C"
      and raw:
        "event_item_raw_ptr D (odc_task C) \<in>
          set (ring (event_raw r))"
      by (auto simp: raw_family_members_def)
    have abstract:
      "Event (odc_task C) \<in> set (ring (ods_event_family S r))"
      using scheduler_event_root_family_member_iff[
        OF one_due_gateH_event_relD[OF rel] live root]
        raw by simp
    show False using abstract_absent root abstract by blast
  qed
  have container:
    "pvContainer_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
         (event_item_raw_ptr D (odc_task C))) = NULL"
    using scheduler_event_root_family_null_iff[
      OF one_due_gateH_event_relD[OF rel] live]
      raw_absent by simp
  show ?thesis using DueEventNull raw_absent container by simp
qed

end
