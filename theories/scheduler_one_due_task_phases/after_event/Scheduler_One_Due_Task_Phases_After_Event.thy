theory Scheduler_One_Due_Task_Phases_After_Event
  imports
    "EAL6_FreeRTOS_V611_Scheduler_One_Due_Task_Phases_Post.Scheduler_One_Due_Task_Phases_Post"
begin

text \<open>
  Family obligations after BOTH removals of the unlocked-tick body: the
  Generic removal from the delayed source and the Event removal (or NULL
  skip) chosen by the arbitrary branch.  In the linked branch the Event
  owner ring loses exactly the due task's Event item, and every Generic
  ring -- the shrunk delayed source, the untouched ready target and every
  other root -- survives the second removal by exact-footprint framing
  against the storage separation the gate carries.  Insert freshness for
  the pending Generic re-insertion is a pure ring-value statement and is
  carried verbatim.  This is the family layer of the post-Event
  preservation contract; the TCB observation layer (priority and owner
  bytes through both removals) is a separate obligation.
\<close>

definition one_due_after_event_obligations ::
  "'tid scheduler_decode \<Rightarrow>
   ('tid, xLIST_C ptr) one_due_context \<Rightarrow>
   xLIST_C ptr one_due_event_branch \<Rightarrow>
   heap_mem \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   bool"
where
  "one_due_after_event_obligations
      D C branch h generic_raw event_raw \<longleftrightarrow>
     (let hg = one_due_generic_remove_heap D C h;
          he = one_due_event_remove_heap D C branch hg;
          source = odc_delayed_root C;
          target = one_due_target_root C;
          p = one_due_generic_raw_ptr D (odc_task C);
          q = event_item_raw_ptr D (odc_task C)
      in raw_xlist_rel he source
           (list_remove_abs p (generic_raw source)) \<and>
         (\<forall>g\<in>odc_generic_roots C. g \<noteq> source \<longrightarrow>
            raw_xlist_rel he g (generic_raw g)) \<and>
         raw_xlist_rel he target (generic_raw target) \<and>
         raw_fresh_for_insert target (ring (generic_raw target)) p \<and>
         (case branch of
            DueEventLinked owner \<Rightarrow>
              raw_xlist_rel he owner
                (list_remove_abs q (event_raw owner))
          | DueEventNull \<Rightarrow>
              (\<forall>e\<in>odc_event_roots C.
                 raw_xlist_rel he e (event_raw e))))"

lemma raw_xlist_storage_remove_subset:
  "raw_xlist_storage lp (list_remove_abs p xs) \<subseteq>
     raw_xlist_storage lp xs"
  using set_remove1_subset
  by (fastforce simp: raw_xlist_storage_def list_remove_abs_def)

lemma one_due_gateH_linked_ownerD:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C (DueEventLinked owner) S
       generic_raw event_raw"
  shows "owner \<in> odc_event_roots C"
proof -
  have branch:
    "one_due_event_branch_at C S (DueEventLinked owner)"
    using one_due_gateH_pure_entryD[OF rel]
    by (simp add: one_due_entry_rel_def)
  then show ?thesis
    by (auto simp: one_due_external_roots_def)
qed

lemma one_due_gateH_source_in_rootsD:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
  shows "odc_delayed_root C \<in> odc_generic_roots C"
  using one_due_gateH_pure_entryD[OF rel]
  by (auto simp: one_due_entry_rel_def one_due_context_wf_def)

lemma one_due_gateH_target_in_rootsD:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
  shows "one_due_target_root C \<in> odc_generic_roots C"
  using one_due_gateH_pure_entryD[OF rel]
  by (auto simp: one_due_entry_rel_def one_due_context_wf_def)

lemma one_due_gateH_storage_disjointD:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and g_root: "g \<in> odc_generic_roots C"
    and e_root: "e \<in> odc_event_roots C"
  shows
    "raw_xlist_storage g (generic_raw g) \<inter>
       raw_xlist_storage e (event_raw e) = {}"
  using rel g_root e_root
  unfolding one_due_gateH_entry_rel_def Let_def
  by blast

lemma one_due_event_remove_generic_frame:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C (DueEventLinked owner) S
       generic_raw event_raw"
    and hg_rel:
      "raw_xlist_rel
         (one_due_generic_remove_heap D C
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))
         g X"
    and disj:
      "raw_xlist_storage g X \<inter>
         raw_xlist_storage owner (event_raw owner) = {}"
  shows
    "raw_xlist_rel
       (raw_remove_concrete_heap
         (one_due_generic_remove_heap D C
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))
         (event_item_raw_ptr D (odc_task C)))
       g X"
proof -
  let ?hg = "one_due_generic_remove_heap D C
    (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))"
  let ?q = "event_item_raw_ptr D (odc_task C)"
  have owner_facts:
    "raw_xlist_rel ?hg owner (event_raw owner) \<and>
     ?q \<in> set (ring (event_raw owner))"
    by (rule one_due_gateH_linked_event_after_genericD[OF rel])
  have owner_rel: "raw_xlist_rel ?hg owner (event_raw owner)"
    and member: "?q \<in> set (ring (event_raw owner))"
    using owner_facts by blast+
  have footprint:
    "raw_remove_exact_write_footprint ?hg owner ?q \<subseteq>
       raw_xlist_storage owner (event_raw owner)"
    by (rule raw_remove_exact_footprint_subset_storage[
      OF owner_rel member])
  show ?thesis
  proof (rule delay_raw_xlist_rel_storage_frame[OF hg_rel])
    fix address
    assume address: "address \<in> raw_xlist_storage g X"
    have outside:
      "address \<notin> raw_remove_exact_write_footprint ?hg owner ?q"
      using footprint disj address by blast
    show "raw_remove_concrete_heap ?hg ?q address = ?hg address"
      by (rule raw_remove_concrete_heap_exact_external_frame[
        OF owner_rel member outside])
  qed
qed

theorem one_due_gateH_after_event_obligations:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
  shows
    "one_due_after_event_obligations D C branch
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       generic_raw event_raw"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  let ?hg = "one_due_generic_remove_heap D C ?h"
  let ?source = "odc_delayed_root C"
  let ?target = "one_due_target_root C"
  let ?p = "one_due_generic_raw_ptr D (odc_task C)"
  let ?q = "event_item_raw_ptr D (odc_task C)"
  note after_generic = one_due_gateH_after_generic_obligations[OF rel]
  have source_hg:
    "raw_xlist_rel ?hg ?source
       (list_remove_abs ?p (generic_raw ?source))"
    using after_generic
    by (simp add: one_due_after_generic_obligations_def Let_def)
  have non_sources_hg:
    "\<forall>g\<in>odc_generic_roots C. g \<noteq> ?source \<longrightarrow>
       raw_xlist_rel ?hg g (generic_raw g)"
    using after_generic
    by (simp add: one_due_after_generic_obligations_def Let_def)
  have target_hg:
    "raw_xlist_rel ?hg ?target (generic_raw ?target)"
    using after_generic
    by (simp add: one_due_after_generic_obligations_def Let_def)
  have fresh:
    "raw_fresh_for_insert ?target (ring (generic_raw ?target)) ?p"
    using after_generic
    by (simp add: one_due_after_generic_obligations_def Let_def)
  have event_roots_hg:
    "\<forall>e\<in>odc_event_roots C.
       raw_xlist_rel ?hg e (event_raw e)"
    using after_generic
    by (simp add: one_due_after_generic_obligations_def Let_def)
  show ?thesis
  proof (cases branch)
    case DueEventNull
    show ?thesis
      using source_hg non_sources_hg target_hg fresh event_roots_hg
        DueEventNull
      by (simp add: one_due_after_event_obligations_def Let_def
          one_due_event_remove_heap_def)
  next
    case (DueEventLinked owner)
    have rel_linked:
      "one_due_gateH_entry_rel D R c a C (DueEventLinked owner) S
         generic_raw event_raw"
      using rel DueEventLinked by simp
    have owner_root: "owner \<in> odc_event_roots C"
      by (rule one_due_gateH_linked_ownerD[OF rel_linked])
    have owner_facts:
      "raw_xlist_rel ?hg owner (event_raw owner) \<and>
       ?q \<in> set (ring (event_raw owner))"
      by (rule one_due_gateH_linked_event_after_genericD[OF rel_linked])
    have owner_he:
      "raw_xlist_rel (raw_remove_concrete_heap ?hg ?q) owner
         (list_remove_abs ?q (event_raw owner))"
      using owner_facts
      by (intro one_due_raw_remove_concrete_heap_refines) blast+
    have source_root: "?source \<in> odc_generic_roots C"
      by (rule one_due_gateH_source_in_rootsD[OF rel])
    have target_root: "?target \<in> odc_generic_roots C"
      by (rule one_due_gateH_target_in_rootsD[OF rel])
    have source_he:
      "raw_xlist_rel (raw_remove_concrete_heap ?hg ?q) ?source
         (list_remove_abs ?p (generic_raw ?source))"
    proof (rule one_due_event_remove_generic_frame[OF rel_linked
        source_hg])
      have base:
        "raw_xlist_storage ?source (generic_raw ?source) \<inter>
           raw_xlist_storage owner (event_raw owner) = {}"
        by (rule one_due_gateH_storage_disjointD[OF rel source_root
          owner_root])
      show
        "raw_xlist_storage ?source
           (list_remove_abs ?p (generic_raw ?source)) \<inter>
           raw_xlist_storage owner (event_raw owner) = {}"
        using base raw_xlist_storage_remove_subset[of ?source ?p
          "generic_raw ?source"]
        by blast
    qed
    have target_he:
      "raw_xlist_rel (raw_remove_concrete_heap ?hg ?q) ?target
         (generic_raw ?target)"
      by (rule one_due_event_remove_generic_frame[OF rel_linked
        target_hg one_due_gateH_storage_disjointD[OF rel target_root
          owner_root]])
    have non_sources_he:
      "\<forall>g\<in>odc_generic_roots C. g \<noteq> ?source \<longrightarrow>
         raw_xlist_rel (raw_remove_concrete_heap ?hg ?q) g
           (generic_raw g)"
    proof (intro ballI impI)
      fix g
      assume g_root: "g \<in> odc_generic_roots C"
        and other: "g \<noteq> ?source"
      show
        "raw_xlist_rel (raw_remove_concrete_heap ?hg ?q) g
           (generic_raw g)"
        by (rule one_due_event_remove_generic_frame[OF rel_linked
          bspec[OF non_sources_hg g_root, THEN mp, OF other]
          one_due_gateH_storage_disjointD[OF rel g_root owner_root]])
    qed
    show ?thesis
      using source_he non_sources_he target_he fresh owner_he
        DueEventLinked
      by (simp add: one_due_after_event_obligations_def Let_def
          one_due_event_remove_heap_def)
  qed
qed

end
