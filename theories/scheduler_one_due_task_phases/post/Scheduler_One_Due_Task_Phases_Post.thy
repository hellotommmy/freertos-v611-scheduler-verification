theory Scheduler_One_Due_Task_Phases_Post
  imports
    "EAL6_FreeRTOS_V611_Scheduler_One_Due_Task_Phases_Entry.Scheduler_One_Due_Task_Phases_Entry"
begin

text \<open>
  Concrete cutpoint functions.  They name the exact heap/family expressions
  that the generated list leaves must produce.  No theorem below assumes a
  fabricated post relation.
\<close>

definition one_due_generic_remove_heap ::
  "'tid scheduler_decode \<Rightarrow>
   ('tid, xLIST_C ptr) one_due_context \<Rightarrow>
   heap_mem \<Rightarrow> heap_mem"
where
  "one_due_generic_remove_heap D C h =
     raw_remove_concrete_heap h
       (one_due_generic_raw_ptr D (odc_task C))"

definition one_due_generic_raw_after_remove ::
  "'tid scheduler_decode \<Rightarrow>
   ('tid, xLIST_C ptr) one_due_context \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs)"
where
  "one_due_generic_raw_after_remove D C fam =
     fam(odc_delayed_root C :=
       list_remove_abs (one_due_generic_raw_ptr D (odc_task C))
         (fam (odc_delayed_root C)))"

definition one_due_event_remove_heap ::
  "'tid scheduler_decode \<Rightarrow>
   ('tid, xLIST_C ptr) one_due_context \<Rightarrow>
   xLIST_C ptr one_due_event_branch \<Rightarrow>
   heap_mem \<Rightarrow> heap_mem"
where
  "one_due_event_remove_heap D C branch h =
     (case branch of
        DueEventLinked owner \<Rightarrow>
          raw_remove_concrete_heap h
            (event_item_raw_ptr D (odc_task C))
      | DueEventNull \<Rightarrow> h)"

definition one_due_event_raw_after_remove ::
  "'tid scheduler_decode \<Rightarrow>
   ('tid, xLIST_C ptr) one_due_context \<Rightarrow>
   xLIST_C ptr one_due_event_branch \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs)"
where
  "one_due_event_raw_after_remove D C branch fam =
     (case branch of
        DueEventLinked owner \<Rightarrow>
          fam(owner :=
            list_remove_abs (event_item_raw_ptr D (odc_task C))
              (fam owner))
      | DueEventNull \<Rightarrow> fam)"

definition one_due_ready_insert_heap ::
  "'tid scheduler_decode \<Rightarrow>
   ('tid, xLIST_C ptr) one_due_context \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   heap_mem \<Rightarrow> heap_mem"
where
  "one_due_ready_insert_heap D C fam h =
     raw_insert_concrete_heap h (one_due_target_root C)
       (fam (one_due_target_root C))
       (one_due_generic_raw_ptr D (odc_task C))"

definition one_due_after_generic_obligations ::
  "'tid scheduler_decode \<Rightarrow>
   ('tid, xLIST_C ptr) one_due_context \<Rightarrow>
   xLIST_C ptr one_due_event_branch \<Rightarrow>
   heap_mem \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   bool"
where
  "one_due_after_generic_obligations
      D C branch h generic_raw event_raw \<longleftrightarrow>
     (let hg = one_due_generic_remove_heap D C h;
          source = odc_delayed_root C;
          target = one_due_target_root C;
          p = one_due_generic_raw_ptr D (odc_task C)
      in raw_xlist_rel hg source
           (list_remove_abs p (generic_raw source)) \<and>
         (\<forall>g\<in>odc_generic_roots C. g \<noteq> source \<longrightarrow>
            raw_xlist_rel hg g (generic_raw g)) \<and>
         raw_xlist_rel hg target (generic_raw target) \<and>
         raw_fresh_for_insert target (ring (generic_raw target)) p \<and>
         (\<forall>e\<in>odc_event_roots C.
            raw_xlist_rel hg e (event_raw e)) \<and>
         (\<forall>t\<in>odc_live C.
            raw_key_at hg (event_item_raw_ptr D t) = odc_K_E C t) \<and>
         (case branch of
            DueEventLinked owner \<Rightarrow>
              raw_xlist_rel hg owner (event_raw owner) \<and>
              event_item_raw_ptr D (odc_task C) \<in>
                set (ring (event_raw owner))
           | DueEventNull \<Rightarrow>
               pvContainer_C
                 (h_val hg (event_item_raw_ptr D (odc_task C))) = NULL))"

lemma one_due_raw_remove_concrete_heap_refines:
  assumes rel: "raw_xlist_rel h lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "raw_xlist_rel (raw_remove_concrete_heap h p) lp
       (list_remove_abs p xs)"
proof -
  have count:
    "List_V611_Raw_Skip_Translation.xLIST_C.uxNumberOfItems_C
       (h_val (raw_remove_concrete_heap h p) lp) =
     List_V611_Raw_Skip_Translation.xLIST_C.uxNumberOfItems_C
       (h_val h lp) - 1"
    by (rule raw_remove_concrete_heap_count_effect[OF rel member])
  have index:
    "List_V611_Raw_Skip_Translation.xLIST_C.pxIndex_C
       (h_val (raw_remove_concrete_heap h p) lp) =
       (if List_V611_Raw_Skip_Translation.xLIST_C.pxIndex_C
             (h_val h lp) = p
        then raw_prev_at h lp p
        else List_V611_Raw_Skip_Translation.xLIST_C.pxIndex_C
             (h_val h lp))"
    by (rule raw_remove_concrete_heap_index_effect[OF rel member])
  have topology:
    "raw_ring_links (raw_remove_concrete_heap h p) lp
       (remove1 p (ring xs))"
    by (rule raw_remove_concrete_heap_topology_effect[OF rel member])
  have payload:
    "\<forall>q\<in>set (remove1 p (ring xs)).
       raw_key_at (raw_remove_concrete_heap h p) q = raw_key_at h q \<and>
       List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvContainer_C
         (h_val (raw_remove_concrete_heap h p) q) =
       List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvContainer_C
         (h_val h q)"
    by (rule raw_remove_concrete_heap_payload_effect[OF rel member])
  have effect:
    "raw_remove_effect h (raw_remove_concrete_heap h p) lp xs p"
    using count index topology payload
    by (simp add: raw_remove_effect_def)
  show ?thesis
    by (rule raw_remove_effect_refines[OF rel member effect])
qed

lemma one_due_gateH_generic_source_after_removeD:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
  shows
    "raw_xlist_rel
       (one_due_generic_remove_heap D C
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))
       (odc_delayed_root C)
       (list_remove_abs (one_due_generic_raw_ptr D (odc_task C))
         (generic_raw (odc_delayed_root C)))"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  let ?source = "odc_delayed_root C"
  let ?p = "one_due_generic_raw_ptr D (odc_task C)"
  have source: "?source \<in> odc_generic_roots C"
    using one_due_gateH_pure_entryD[OF rel]
    by (auto simp: one_due_entry_rel_def one_due_context_wf_def)
  have source_rel: "raw_xlist_rel ?h ?source (generic_raw ?source)"
    using one_due_gateH_generic_preD[OF rel] source
    by (auto simp: scheduler_family_pre_rel_def raw_family_rel_def)
  have owner:
    "scheduler_delay_owner_entry_rel ?h (odc_generic_roots C)
       generic_raw ?source ?p"
    using rel
    unfolding one_due_gateH_entry_rel_def Let_def
    by blast
  have member: "?p \<in> set (ring (generic_raw ?source))"
    by (rule scheduler_delay_owner_entry_member[OF owner])
  have refined:
    "raw_xlist_rel (raw_remove_concrete_heap ?h ?p) ?source
       (list_remove_abs ?p (generic_raw ?source))"
    by (rule one_due_raw_remove_concrete_heap_refines[
      OF source_rel member])
  show ?thesis
    using refined by (simp add: one_due_generic_remove_heap_def)
qed

lemma one_due_gateH_generic_non_source_after_removeD:
  assumes rel:
      "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and root: "g \<in> odc_generic_roots C"
    and other: "g \<noteq> odc_delayed_root C"
  shows
    "raw_xlist_rel
       (one_due_generic_remove_heap D C
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))
       g (generic_raw g)"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  let ?source = "odc_delayed_root C"
  let ?p = "one_due_generic_raw_ptr D (odc_task C)"
  have pre:
    "scheduler_family_pre_rel ?h (odc_generic_roots C)
       generic_raw (odc_live C) D"
    by (rule one_due_gateH_generic_preD[OF rel])
  have source: "?source \<in> odc_generic_roots C"
    using one_due_gateH_pure_entryD[OF rel]
    by (auto simp: one_due_entry_rel_def one_due_context_wf_def)
  have owner:
    "scheduler_delay_owner_entry_rel ?h (odc_generic_roots C)
       generic_raw ?source ?p"
    using rel
    unfolding one_due_gateH_entry_rel_def Let_def
    by blast
  have member: "?p \<in> set (ring (generic_raw ?source))"
    by (rule scheduler_delay_owner_entry_member[OF owner])
  have root_rel: "raw_xlist_rel ?h g (generic_raw g)"
    using pre root
    by (auto simp: scheduler_family_pre_rel_def raw_family_rel_def)
  have framed:
    "raw_xlist_rel (raw_remove_concrete_heap ?h ?p) g (generic_raw g)"
  proof (rule delay_raw_xlist_rel_storage_frame[OF root_rel])
    fix address
    assume address: "address \<in> raw_xlist_storage g (generic_raw g)"
    show "raw_remove_concrete_heap ?h ?p address = ?h address"
      by (rule raw_remove_family_non_target_byte_frame[
        OF pre source root other[symmetric] member address])
  qed
  show ?thesis
    using framed by (simp add: one_due_generic_remove_heap_def)
qed

lemma one_due_gateH_generic_target_after_removeD:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
  shows
    "raw_xlist_rel
       (one_due_generic_remove_heap D C
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))
       (one_due_target_root C) (generic_raw (one_due_target_root C))"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  let ?source = "odc_delayed_root C"
  let ?target = "one_due_target_root C"
  let ?p = "one_due_generic_raw_ptr D (odc_task C)"
  have pre:
    "scheduler_family_pre_rel ?h (odc_generic_roots C)
       generic_raw (odc_live C) D"
    by (rule one_due_gateH_generic_preD[OF rel])
  have source: "?source \<in> odc_generic_roots C"
      and target: "?target \<in> odc_generic_roots C"
      and distinct: "?source \<noteq> ?target"
    using one_due_gateH_pure_entryD[OF rel]
    by (auto simp: one_due_entry_rel_def one_due_context_wf_def)
  have owner:
    "scheduler_delay_owner_entry_rel ?h (odc_generic_roots C)
       generic_raw ?source ?p"
    using rel
    unfolding one_due_gateH_entry_rel_def Let_def
    by blast
  have member: "?p \<in> set (ring (generic_raw ?source))"
    by (rule scheduler_delay_owner_entry_member[OF owner])
  have target_rel: "raw_xlist_rel ?h ?target (generic_raw ?target)"
    using pre target
    by (auto simp: scheduler_family_pre_rel_def raw_family_rel_def)
  show ?thesis
    unfolding one_due_generic_remove_heap_def
  proof (rule delay_raw_xlist_rel_storage_frame[OF target_rel])
    fix address
    assume address:
      "address \<in> raw_xlist_storage ?target (generic_raw ?target)"
    show "raw_remove_concrete_heap ?h ?p address = ?h address"
      by (rule raw_remove_family_non_target_byte_frame[
        OF pre source target distinct member address])
  qed
qed

lemma one_due_gateH_generic_target_freshD:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
  shows
    "raw_fresh_for_insert (one_due_target_root C)
       (ring (generic_raw (one_due_target_root C)))
       (one_due_generic_raw_ptr D (odc_task C))"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  have roots:
    "odc_delayed_root C \<in> odc_generic_roots C \<and>
     one_due_target_root C \<in> odc_generic_roots C \<and>
     odc_delayed_root C \<noteq> one_due_target_root C"
    using one_due_gateH_pure_entryD[OF rel]
    by (auto simp: one_due_entry_rel_def one_due_context_wf_def)
  have target: "one_due_target_root C \<in> odc_generic_roots C"
    using roots by blast
  have distinct:
    "odc_delayed_root C \<noteq> one_due_target_root C"
    using roots by blast
  have owner:
    "scheduler_delay_owner_entry_rel ?h (odc_generic_roots C)
       generic_raw (odc_delayed_root C)
       (one_due_generic_raw_ptr D (odc_task C))"
    using rel
    unfolding one_due_gateH_entry_rel_def Let_def
    by blast
  have geometry:
    "raw_family_insert_geometry (odc_generic_roots C) generic_raw
       (one_due_generic_raw_ptr D (odc_task C))"
    using rel
    unfolding one_due_gateH_entry_rel_def Let_def
    by blast
  show ?thesis
    by (rule scheduler_delay_entry_fresh_for_derived_target[
      OF owner geometry target distinct])
qed

lemma one_due_gateH_generic_remove_event_item_frameD:
  assumes rel:
      "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and live: "t \<in> odc_live C"
  shows
    "h_val
       (one_due_generic_remove_heap D C
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))
       (event_item_raw_ptr D t) =
     h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (event_item_raw_ptr D t)"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  let ?source = "odc_delayed_root C"
  let ?p = "one_due_generic_raw_ptr D (odc_task C)"
  let ?event = "event_item_raw_ptr D t"
  have pre:
    "scheduler_family_pre_rel ?h (odc_generic_roots C)
       generic_raw (odc_live C) D"
    by (rule one_due_gateH_generic_preD[OF rel])
  have source: "?source \<in> odc_generic_roots C"
    using one_due_gateH_pure_entryD[OF rel]
    by (auto simp: one_due_entry_rel_def one_due_context_wf_def)
  have owner:
    "scheduler_delay_owner_entry_rel ?h (odc_generic_roots C)
       generic_raw ?source ?p"
    using rel
    unfolding one_due_gateH_entry_rel_def Let_def
    by blast
  have member: "?p \<in> set (ring (generic_raw ?source))"
    by (rule scheduler_delay_owner_entry_member[OF owner])
  have managed:
    "?event \<in> universal_managed_nodes (odc_live C) D"
    using live
    by (auto simp: universal_managed_nodes_def event_item_raw_ptr_def)
  have nonmember: "?event \<notin> set (ring (generic_raw ?source))"
    by (rule one_due_gateH_event_notin_generic_rootD[OF rel live source])
  have byte_frame:
    "\<forall>address\<in>raw_item_region ?event.
       raw_remove_concrete_heap ?h ?p address = ?h address"
    using raw_remove_family_sibling_item_priority_byte_frame[
      OF pre source member managed nonmember live]
    by blast
  show ?thesis
    unfolding one_due_generic_remove_heap_def
    apply (rule delay_h_val_region_cong)
    apply (rule byte_frame[rule_format])
    by (simp add: raw_item_region_def)
qed

lemma one_due_gateH_total_K_E_after_genericD:
  assumes rel:
      "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and live: "t \<in> odc_live C"
  shows
    "raw_key_at
       (one_due_generic_remove_heap D C
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))
       (event_item_raw_ptr D t) = odc_K_E C t"
  using one_due_gateH_generic_remove_event_item_frameD[OF rel live]
    one_due_gateH_total_K_E_entryD[OF rel live]
  by (simp add: raw_key_at_def)

lemma one_due_gateH_event_root_after_genericD:
  assumes rel:
      "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and event_root: "e \<in> odc_event_roots C"
  shows
    "raw_xlist_rel
       (one_due_generic_remove_heap D C
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))
       e (event_raw e)"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  let ?source = "odc_delayed_root C"
  let ?p = "one_due_generic_raw_ptr D (odc_task C)"
  have pre:
    "scheduler_family_pre_rel ?h (odc_generic_roots C)
       generic_raw (odc_live C) D"
    by (rule one_due_gateH_generic_preD[OF rel])
  have source: "?source \<in> odc_generic_roots C"
    using one_due_gateH_pure_entryD[OF rel]
    by (auto simp: one_due_entry_rel_def one_due_context_wf_def)
  have source_rel: "raw_xlist_rel ?h ?source (generic_raw ?source)"
    using pre source
    by (auto simp: scheduler_family_pre_rel_def raw_family_rel_def)
  have owner:
    "scheduler_delay_owner_entry_rel ?h (odc_generic_roots C)
       generic_raw ?source ?p"
    using rel
    unfolding one_due_gateH_entry_rel_def Let_def
    by blast
  have member: "?p \<in> set (ring (generic_raw ?source))"
    by (rule scheduler_delay_owner_entry_member[OF owner])
  have old_event: "raw_xlist_rel ?h e (event_raw e)"
    by (rule scheduler_event_root_family_raw_rootD[
      OF one_due_gateH_event_relD[OF rel] event_root])
  have storage_disjoint:
    "raw_xlist_storage ?source (generic_raw ?source) \<inter>
       raw_xlist_storage e (event_raw e) = {}"
    using rel source event_root
    unfolding one_due_gateH_entry_rel_def Let_def
    by blast
  have footprint:
    "raw_remove_exact_write_footprint ?h ?source ?p \<subseteq>
       raw_xlist_storage ?source (generic_raw ?source)"
    by (rule raw_remove_exact_footprint_subset_storage[
      OF source_rel member])
  show ?thesis
    unfolding one_due_generic_remove_heap_def
  proof (rule delay_raw_xlist_rel_storage_frame[OF old_event])
    fix address
    assume address: "address \<in> raw_xlist_storage e (event_raw e)"
    have outside:
      "address \<notin> raw_remove_exact_write_footprint ?h ?source ?p"
      using footprint storage_disjoint address by blast
    show "raw_remove_concrete_heap ?h ?p address = ?h address"
      by (rule raw_remove_concrete_heap_exact_external_frame[
        OF source_rel member outside])
  qed
qed

lemma one_due_gateH_linked_event_after_genericD:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C (DueEventLinked owner) S
       generic_raw event_raw"
  shows
    "raw_xlist_rel
       (one_due_generic_remove_heap D C
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))
       owner (event_raw owner) \<and>
     event_item_raw_ptr D (odc_task C) \<in> set (ring (event_raw owner))"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  let ?source = "odc_delayed_root C"
  let ?p = "one_due_generic_raw_ptr D (odc_task C)"
  have pre:
    "scheduler_family_pre_rel ?h (odc_generic_roots C)
       generic_raw (odc_live C) D"
    by (rule one_due_gateH_generic_preD[OF rel])
  have source: "?source \<in> odc_generic_roots C"
    using one_due_gateH_pure_entryD[OF rel]
    by (auto simp: one_due_entry_rel_def one_due_context_wf_def)
  have source_rel: "raw_xlist_rel ?h ?source (generic_raw ?source)"
    using pre source
    by (auto simp: scheduler_family_pre_rel_def raw_family_rel_def)
  have owner_entry:
    "scheduler_delay_owner_entry_rel ?h (odc_generic_roots C)
       generic_raw ?source ?p"
    using rel
    unfolding one_due_gateH_entry_rel_def Let_def
    by blast
  have source_member: "?p \<in> set (ring (generic_raw ?source))"
    by (rule scheduler_delay_owner_entry_member[OF owner_entry])
  note branch = one_due_gateH_event_branchD[OF rel]
  have owner_root: "owner \<in> odc_event_roots C"
      and event_member:
        "event_item_raw_ptr D (odc_task C) \<in>
           set (ring (event_raw owner))"
    using branch
    by (auto simp: one_due_external_roots_def)
  have event_rel: "raw_xlist_rel ?h owner (event_raw owner)"
    by (rule scheduler_event_root_family_raw_rootD[
      OF one_due_gateH_event_relD[OF rel] owner_root])
  have storage_disjoint:
    "raw_xlist_storage ?source (generic_raw ?source) \<inter>
       raw_xlist_storage owner (event_raw owner) = {}"
    using rel source owner_root
    unfolding one_due_gateH_entry_rel_def Let_def
    by blast
  have footprint:
    "raw_remove_exact_write_footprint ?h ?source ?p \<subseteq>
       raw_xlist_storage ?source (generic_raw ?source)"
    by (rule raw_remove_exact_footprint_subset_storage[
      OF source_rel source_member])
  have framed:
    "raw_xlist_rel (raw_remove_concrete_heap ?h ?p)
       owner (event_raw owner)"
  proof (rule delay_raw_xlist_rel_storage_frame[OF event_rel])
    fix address
    assume address:
      "address \<in> raw_xlist_storage owner (event_raw owner)"
    have outside:
      "address \<notin> raw_remove_exact_write_footprint ?h ?source ?p"
      using footprint storage_disjoint address by blast
    show "raw_remove_concrete_heap ?h ?p address = ?h address"
      by (rule raw_remove_concrete_heap_exact_external_frame[
        OF source_rel source_member outside])
  qed
  show ?thesis
    using framed event_member
    by (simp add: one_due_generic_remove_heap_def)
qed

lemma one_due_gateH_null_event_after_genericD:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C DueEventNull S
       generic_raw event_raw"
  shows
    "pvContainer_C
       (h_val
         (one_due_generic_remove_heap D C
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))
         (event_item_raw_ptr D (odc_task C))) = NULL"
proof -
  have live: "odc_task C \<in> odc_live C"
    by (rule one_due_gateH_task_liveD[OF rel])
  have initial:
    "pvContainer_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
         (event_item_raw_ptr D (odc_task C))) = NULL"
    using one_due_gateH_event_branchD[OF rel] by simp
  have frame:
    "h_val
       (one_due_generic_remove_heap D C
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))
       (event_item_raw_ptr D (odc_task C)) =
     h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (event_item_raw_ptr D (odc_task C))"
    by (rule one_due_gateH_generic_remove_event_item_frameD[OF rel live])
  show ?thesis using initial frame by simp
qed

theorem one_due_gateH_after_generic_obligations:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
  shows
    "one_due_after_generic_obligations D C branch
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       generic_raw event_raw"
proof -
  have source:
    "raw_xlist_rel
       (one_due_generic_remove_heap D C
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))
       (odc_delayed_root C)
       (list_remove_abs (one_due_generic_raw_ptr D (odc_task C))
         (generic_raw (odc_delayed_root C)))"
    by (rule one_due_gateH_generic_source_after_removeD[OF rel])
  have target:
    "raw_xlist_rel
       (one_due_generic_remove_heap D C
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))
       (one_due_target_root C) (generic_raw (one_due_target_root C))"
    by (rule one_due_gateH_generic_target_after_removeD[OF rel])
  have non_sources:
    "\<forall>g\<in>odc_generic_roots C.
       g \<noteq> odc_delayed_root C \<longrightarrow>
       raw_xlist_rel
         (one_due_generic_remove_heap D C
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))
         g (generic_raw g)"
  proof (intro ballI impI)
    fix g
    assume root: "g \<in> odc_generic_roots C"
      and other: "g \<noteq> odc_delayed_root C"
    show
      "raw_xlist_rel
         (one_due_generic_remove_heap D C
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))
         g (generic_raw g)"
      by (rule one_due_gateH_generic_non_source_after_removeD[
        OF rel root other])
  qed
  have fresh:
    "raw_fresh_for_insert (one_due_target_root C)
       (ring (generic_raw (one_due_target_root C)))
       (one_due_generic_raw_ptr D (odc_task C))"
    by (rule one_due_gateH_generic_target_freshD[OF rel])
  have keys:
    "\<forall>t\<in>odc_live C.
       raw_key_at
         (one_due_generic_remove_heap D C
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))
         (event_item_raw_ptr D t) = odc_K_E C t"
  proof (intro ballI)
    fix t
    assume live: "t \<in> odc_live C"
    show
      "raw_key_at
         (one_due_generic_remove_heap D C
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))
         (event_item_raw_ptr D t) = odc_K_E C t"
      by (rule one_due_gateH_total_K_E_after_genericD[OF rel live])
  qed
  have event_roots:
    "\<forall>e\<in>odc_event_roots C.
       raw_xlist_rel
         (one_due_generic_remove_heap D C
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))
         e (event_raw e)"
  proof (intro ballI)
    fix e
    assume root: "e \<in> odc_event_roots C"
    show
      "raw_xlist_rel
         (one_due_generic_remove_heap D C
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))
         e (event_raw e)"
      by (rule one_due_gateH_event_root_after_genericD[OF rel root])
  qed
  show ?thesis
  proof (cases branch)
    case (DueEventLinked owner)
    have rel_linked:
      "one_due_gateH_entry_rel D R c a C (DueEventLinked owner) S
         generic_raw event_raw"
      using rel DueEventLinked by simp
    have linked:
      "raw_xlist_rel
         (one_due_generic_remove_heap D C
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))
         owner (event_raw owner) \<and>
       event_item_raw_ptr D (odc_task C) \<in>
         set (ring (event_raw owner))"
      by (rule one_due_gateH_linked_event_after_genericD[OF rel_linked])
    show ?thesis
      using source non_sources target fresh event_roots keys linked DueEventLinked
      by (simp add: one_due_after_generic_obligations_def Let_def)
  next
    case DueEventNull
    have rel_null:
      "one_due_gateH_entry_rel D R c a C DueEventNull S
         generic_raw event_raw"
      using rel DueEventNull by simp
    have null:
      "pvContainer_C
         (h_val
           (one_due_generic_remove_heap D C
             (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))
           (event_item_raw_ptr D (odc_task C))) = NULL"
      by (rule one_due_gateH_null_event_after_genericD[OF rel_null])
    show ?thesis
      using source non_sources target fresh event_roots keys null DueEventNull
      by (simp add: one_due_after_generic_obligations_def Let_def)
  qed
qed

end
