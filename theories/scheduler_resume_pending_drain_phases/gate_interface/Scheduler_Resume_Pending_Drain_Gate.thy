theory Scheduler_Resume_Pending_Drain_Gate
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Pending_Drain_Gate_Relation.Scheduler_Resume_Pending_Drain_Gate_Relation"
begin

text \<open>
  Existing generated leaf interfaces.  These are real generated-source
  theorems inherited from the universal list work; they do not prove the loop
  composition by themselves.  The head Event theorem is already discharged
  from the full entry relation.  Generic removal and ready insertion are
  exposed with precisely the intermediate raw-list/member/freshness facts that
  the phase-preservation proof must establish after the preceding writes.
\<close>

theorem resume_pending_head_event_remove_generated_leaf:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "Scheduler_V611_Delay_Translation.vListRemove'
       (scheduler_event_item_ptr (sd_tcb_ptr D t)) \<bullet> c
     \<lbrace>\<lambda>r s.
       r = Result () \<and>
       s = scheduler_mem_state
         (raw_remove_concrete_heap
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
           (abi_item_ptr
             (scheduler_event_item_ptr (sd_tcb_ptr D t)))) c
     \<rbrace>"
proof -
  have root: "rpc_pending_root C \<in> rpc_event_roots C"
    using resume_pending_gate_pure_entryD[OF rel]
    by (auto simp: resume_pending_entry_rel_def resume_pending_context_wf_def)
  have raw:
    "raw_xlist_rel
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (rpc_pending_root C) (event_raw (rpc_pending_root C))"
    by (rule scheduler_event_root_family_raw_rootD[
      OF resume_pending_gate_event_familyD[OF rel] root])
  have root_eq:
    "rpc_pending_root C = abi_list_ptr (sr_pending R)"
    using rel
    unfolding resume_pending_gate_entry_rel_def Let_def
    by blast
  have raw_source:
    "raw_xlist_rel
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (abi_list_ptr (sr_pending R))
       (event_raw (rpc_pending_root C))"
    using raw root_eq by simp
  have member:
    "abi_item_ptr (scheduler_event_item_ptr (sd_tcb_ptr D t)) \<in>
       set (ring (event_raw (rpc_pending_root C)))"
    using resume_pending_gate_head_event_memberD[OF rel tasks]
    by (simp add: event_item_raw_ptr_def)
  show ?thesis
    by (rule scheduler_vListRemove_general_exact_state[
      OF raw_source member])
qed

theorem resume_pending_head_generic_remove_entry_leaf:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "Scheduler_V611_Delay_Translation.vListRemove'
       (scheduler_generic_item_ptr (sd_tcb_ptr D t)) \<bullet> c
     \<lbrace>\<lambda>r s.
       r = Result () \<and>
       s = scheduler_mem_state
         (raw_remove_concrete_heap
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
           (abi_item_ptr
             (scheduler_generic_item_ptr (sd_tcb_ptr D t)))) c
     \<rbrace>"
proof -
  note owner_geometry = resume_pending_gate_head_generic_ownerD[OF rel tasks]
  have owner_entry:
    "scheduler_delay_owner_entry_rel
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (rpc_generic_roots C) generic_raw (rpc_generic_owner C t)
       (resume_pending_generic_raw_ptr D t)"
    using owner_geometry by blast
  have owner_root:
    "rpc_generic_owner C t \<in> rpc_generic_roots C"
    using owner_entry
    by (simp add: scheduler_delay_owner_entry_rel_def)
  have raw:
    "raw_xlist_rel
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (rpc_generic_owner C t) (generic_raw (rpc_generic_owner C t))"
    using resume_pending_gate_generic_familyD[OF rel] owner_root
    by (auto simp: scheduler_family_pre_rel_def raw_family_rel_def)
  have root_eq:
    "abi_list_ptr (resume_pending_owner_list_ptr R C t) =
       rpc_generic_owner C t"
  proof -
    have pending: "t \<in> set (rpc_tasks C)"
      using tasks by simp
    show ?thesis
      by (rule resume_pending_gate_owner_list_ptrD[OF rel pending])
  qed
  have raw_source:
    "raw_xlist_rel
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (abi_list_ptr (resume_pending_owner_list_ptr R C t))
       (generic_raw (rpc_generic_owner C t))"
    using raw root_eq by simp
  have raw_member:
    "resume_pending_generic_raw_ptr D t \<in>
       set (ring (generic_raw (rpc_generic_owner C t)))"
    by (rule scheduler_delay_owner_entry_member[OF owner_entry])
  have member:
    "abi_item_ptr (scheduler_generic_item_ptr (sd_tcb_ptr D t)) \<in>
       set (ring (generic_raw (rpc_generic_owner C t)))"
    using raw_member
    by (simp add: resume_pending_generic_raw_ptr_def
        scheduler_generic_item_ptr_def abi_generic_list_item_ptr_def)
  show ?thesis
    by (rule scheduler_vListRemove_general_exact_state[
      OF raw_source member])
qed

theorem resume_pending_generic_remove_generated_interface:
  assumes rel:
      "raw_xlist_rel
        (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
        (abi_list_ptr lp) xs"
    and member:
      "abi_item_ptr (scheduler_generic_item_ptr (sd_tcb_ptr D t)) \<in>
        set (ring xs)"
  shows
    "Scheduler_V611_Delay_Translation.vListRemove'
       (scheduler_generic_item_ptr (sd_tcb_ptr D t)) \<bullet> c
     \<lbrace>\<lambda>r s.
       r = Result () \<and>
       s = scheduler_mem_state
         (raw_remove_concrete_heap
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
           (abi_item_ptr
             (scheduler_generic_item_ptr (sd_tcb_ptr D t)))) c
     \<rbrace>"
  by (rule scheduler_vListRemove_general_exact_state[OF rel member])

theorem resume_pending_ready_insert_generated_interface:
  assumes rel:
      "raw_xlist_rel
        (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
        (abi_list_ptr lp) xs"
    and fresh:
      "raw_fresh_for_insert (abi_list_ptr lp) (ring xs)
        (abi_item_ptr (scheduler_generic_item_ptr (sd_tcb_ptr D t)))"
  shows
    "Scheduler_V611_Delay_Translation.vListInsertEnd' lp
       (scheduler_generic_item_ptr (sd_tcb_ptr D t)) \<bullet> c
     \<lbrace>\<lambda>r s.
       r = Result () \<and>
       s = scheduler_mem_state
         (raw_insert_concrete_heap
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
           (abi_list_ptr lp) xs
           (abi_item_ptr
             (scheduler_generic_item_ptr (sd_tcb_ptr D t)))) c
     \<rbrace>"
  by (rule scheduler_vListInsertEnd_general_exact_state[OF rel fresh])

text \<open>
  Exact remaining Gate-H obligations for this layer:

  * promote the head Event removal through the complete Event family, total
    K_E and all TaskObservation fields;
  * derive the current head's unique Generic owner after that write, then
    promote Generic removal through every non-owner Generic root and every
    Event root;
  * derive ready-target freshness from global unlinkedness, retain the captured
    K_G payload, and compose the inlined top write before vListInsertEnd;
  * re-establish both complete families and TaskObservation at YieldChecked,
    prove the commit lemma at the concrete heap level, and discharge the
    while-loop VCG using length todo;
  * only outside the drain loop, compose arbitrary missed-tick replay and the
    final missed-yield/yield branch.

  Therefore the four generated leaves/interfaces above are source facts, not a
  theorem for the whole pending loop or xTaskResumeAll.

  Quantifier ledger: C, its finite live set and pending list, every task,
  priority, Generic owner, ready root, Event root, K_G/K_E value, heap, raw
  family, cursor and address remain symbolic.  The numeral 4 is only the
  frozen configMAX_PRIORITIES bound; zero suspension depth is the derived
  loop-head phase of the outermost branch, not a chosen task/tick witness.
  The two generated-source root corollaries condition only on the frozen ABI
  record R = generated_scheduler_roots; this identifies program globals and
  does not instantiate any runtime task, priority, key, ring or heap value.
\<close>

end
