theory Scheduler_One_Due_Task_Phases_Generated
  imports
    "EAL6_FreeRTOS_V611_Scheduler_One_Due_Task_Phases_Post.Scheduler_One_Due_Task_Phases_Post"
begin

theorem one_due_generic_remove_generated_leaf:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
  shows
    "Scheduler_V611_Delay_Translation.vListRemove'
       (scheduler_generic_item_ptr (sd_tcb_ptr D (odc_task C))) \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       t = scheduler_mem_state
         (one_due_generic_remove_heap D C
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))) c
     \<rbrace>"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  let ?source = "Scheduler_V611_Parse.globals.pxDelayedTaskList_' c"
  let ?root = "odc_delayed_root C"
  let ?p = "one_due_generic_raw_ptr D (odc_task C)"
  have root: "?root \<in> odc_generic_roots C"
    using one_due_gateH_pure_entryD[OF rel]
    by (auto simp: one_due_entry_rel_def one_due_context_wf_def)
  have source_eq: "?root = abi_list_ptr ?source"
    using one_due_gateH_exact_rootsD[OF rel] by simp
  have raw_root: "raw_xlist_rel ?h ?root (generic_raw ?root)"
    using one_due_gateH_generic_preD[OF rel] root
    by (auto simp: scheduler_family_pre_rel_def raw_family_rel_def)
  have raw_source:
    "raw_xlist_rel ?h (abi_list_ptr ?source) (generic_raw ?root)"
    using raw_root source_eq by simp
  have owner:
    "raw_family_members (odc_generic_roots C) generic_raw ?p = {?root}"
    using one_due_gateH_generic_owner_and_keyD[OF rel] by blast
  have root_member:
    "?root \<in>
       raw_family_members (odc_generic_roots C) generic_raw ?p"
    using owner by simp
  have member:
    "?p \<in> set (ring (generic_raw ?root))"
    using root_member by (simp add: raw_family_members_def)
  have source_member:
    "abi_item_ptr
       (scheduler_generic_item_ptr (sd_tcb_ptr D (odc_task C))) \<in>
       set (ring (generic_raw ?root))"
    using member
    by (simp add: one_due_generic_raw_ptr_def
        scheduler_generic_item_ptr_def abi_generic_list_item_ptr_def)
  have execution:
    "Scheduler_V611_Delay_Translation.vListRemove'
       (scheduler_generic_item_ptr (sd_tcb_ptr D (odc_task C))) \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       t = scheduler_mem_state
         (raw_remove_concrete_heap ?h
           (abi_item_ptr
             (scheduler_generic_item_ptr
               (sd_tcb_ptr D (odc_task C))))) c
     \<rbrace>"
    by (rule scheduler_tick_vListRemove_general_exact[
      OF raw_source source_member])
  show ?thesis
    apply (rule runs_to_weaken[OF execution])
    by (simp add: one_due_generic_remove_heap_def
        one_due_generic_raw_ptr_def scheduler_generic_item_ptr_def
        abi_generic_list_item_ptr_def)
qed

theorem one_due_generic_remove_generated_resume_leaf:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
  shows
    "Scheduler_V611_Delay_Translation.vListRemove'
       (scheduler_generic_item_ptr (sd_tcb_ptr D (odc_task C))) \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       t = scheduler_mem_state
         (one_due_generic_remove_heap D C
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))) c \<and>
       one_due_after_generic_obligations D C branch
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
         generic_raw event_raw
     \<rbrace>"
proof -
  note execution = one_due_generic_remove_generated_leaf[OF rel]
  have obligations:
    "one_due_after_generic_obligations D C branch
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       generic_raw event_raw"
    by (rule one_due_gateH_after_generic_obligations[OF rel])
  show ?thesis
    apply (rule runs_to_weaken[OF execution])
    using obligations by simp
qed

lemma one_due_raw_list_root_has_source_preimage:
  fixes owner :: "List_V611_Raw_Skip_Translation.xLIST_C ptr"
  shows
    "\<exists>source :: Scheduler_V611_Parse.xLIST_C ptr.
       abi_list_ptr source = owner"
proof
  show
    "abi_list_ptr
       (PTR_COERCE(unit \<rightarrow> Scheduler_V611_Parse.xLIST_C)
         (PTR_COERCE(List_V611_Raw_Skip_Translation.xLIST_C \<rightarrow> unit)
           owner)) = owner"
    by (simp add: abi_list_ptr_def)
qed

theorem one_due_linked_event_remove_generated_leaf_after_generic:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C (DueEventLinked owner) S
       generic_raw event_raw"
  shows
    "Scheduler_V611_Delay_Translation.vListRemove'
       (scheduler_event_item_ptr (sd_tcb_ptr D (odc_task C))) \<bullet>
       (scheduler_mem_state
         (one_due_generic_remove_heap D C
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))) c)
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       t = scheduler_mem_state
         (one_due_event_remove_heap D C (DueEventLinked owner)
           (one_due_generic_remove_heap D C
             (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))) c
     \<rbrace>"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  let ?hg = "one_due_generic_remove_heap D C ?h"
  let ?p =
    "scheduler_event_item_ptr (sd_tcb_ptr D (odc_task C))"
  obtain source :: "Scheduler_V611_Parse.xLIST_C ptr" where
    source: "abi_list_ptr source = owner"
    using one_due_raw_list_root_has_source_preimage[where owner=owner]
    by blast
  have linked:
    "raw_xlist_rel ?hg owner (event_raw owner) \<and>
     event_item_raw_ptr D (odc_task C) \<in>
       set (ring (event_raw owner))"
    by (rule one_due_gateH_linked_event_after_genericD[OF rel])
  have raw_source:
    "raw_xlist_rel
       (hrs_mem
         (Scheduler_V611_Parse.globals.t_hrs_'
           (scheduler_mem_state ?hg c)))
       (abi_list_ptr source) (event_raw owner)"
    using linked source by simp
  have source_member:
    "abi_item_ptr ?p \<in> set (ring (event_raw owner))"
    using linked
    by (simp add: event_item_raw_ptr_def scheduler_event_item_ptr_def
        abi_event_list_item_ptr_def)
  note execution = scheduler_tick_vListRemove_general_exact[
    OF raw_source source_member]
  show ?thesis
    apply (rule runs_to_weaken[OF execution])
    by (simp add: one_due_event_remove_heap_def event_item_raw_ptr_def
        scheduler_event_item_ptr_def abi_event_list_item_ptr_def)
qed

theorem one_due_linked_generic_then_event_generated_sequence:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C (DueEventLinked owner) S
       generic_raw event_raw"
  shows
    "bind
       (Scheduler_V611_Delay_Translation.vListRemove'
         (scheduler_generic_item_ptr (sd_tcb_ptr D (odc_task C))))
       (\<lambda>_. Scheduler_V611_Delay_Translation.vListRemove'
         (scheduler_event_item_ptr (sd_tcb_ptr D (odc_task C)))) \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       t = scheduler_mem_state
         (one_due_event_remove_heap D C (DueEventLinked owner)
           (one_due_generic_remove_heap D C
             (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))) c
     \<rbrace>"
proof -
  note generic = one_due_generic_remove_generated_leaf[OF rel]
  note event =
    one_due_linked_event_remove_generated_leaf_after_generic[OF rel]
  show ?thesis
    apply (rule runs_to_bind)
    apply (rule runs_to_weaken[OF generic])
     apply clarsimp
    apply (rule runs_to_weaken[OF event])
    by simp
qed

text \<open>
  Named source cutpoints for one execution of the actual delayed-task while
  body.  These definitions are not an abstract replacement for the generated
  program: the theorem one_due_vTaskIncrementTick_named_outer_source below
  folds them back into the exact @{thm vTaskIncrementTick'_def} term.

  The first predicate is exactly the generated read of the embedded Event
  item's pvContainer field after the Generic removal.  The false branch is the
  generated skip.  The residual source term starts with the inlined
  uxTopReadyPriority conditional, then checks the frozen four-priority bound,
  selects the generated ready-array element, calls generated vListInsertEnd',
  and finally fetches the next delayed-list head.
\<close>

definition one_due_tick_event_guard ::
  "Scheduler_V611_Parse.tskTaskControlBlock_C ptr \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> bool"
where
  "one_due_tick_event_guard pxTCB s \<longleftrightarrow>
     Scheduler_V611_Parse.xLIST_ITEM_C.pvContainer_C
       (Scheduler_V611_Parse.tskTaskControlBlock_C.xEventListItem_C
         (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s)) pxTCB))
       \<noteq> NULL"

definition one_due_tick_event_dispatch_source ::
  "Scheduler_V611_Parse.tskTaskControlBlock_C ptr \<Rightarrow>
   (unit, unit, Scheduler_V611_Parse.globals) spec_monad"
where
  "one_due_tick_event_dispatch_source pxTCB =
     condition (one_due_tick_event_guard pxTCB)
       (Scheduler_V611_Delay_Translation.vListRemove'
         (scheduler_event_item_ptr pxTCB))
       skip"

definition one_due_tick_top_ready_tail_source ::
  "Scheduler_V611_Parse.tskTaskControlBlock_C ptr \<Rightarrow>
   (unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr,
     Scheduler_V611_Parse.globals) spec_monad"
where
  "one_due_tick_top_ready_tail_source pxTCB = do {
     condition
       (\<lambda>s. Scheduler_V611_Parse.globals.uxTopReadyPriority_' s <
          Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
            (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
              pxTCB))
       (modify
         (\<lambda>s. s\<lparr>Scheduler_V611_Parse.globals.uxTopReadyPriority_' :=
           Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
             (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
               pxTCB)\<rparr>))
       skip;
     guard
       (\<lambda>s. Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
          (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
            pxTCB) < 4);
     guard (\<lambda>_. c_guard Scheduler_V611_Parse.pxReadyTasksLists_');
     pxList \<leftarrow> gets
       (\<lambda>s. array_ptr_index Scheduler_V611_Parse.pxReadyTasksLists_'
          False
          (unat
            (Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
              (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
                pxTCB))));
     ret \<leftarrow> Scheduler_V611_Delay_Translation.vListInsertEnd'
       pxList (scheduler_generic_item_ptr pxTCB);
     guard
       (\<lambda>s. c_guard
         (Scheduler_V611_Parse.globals.pxDelayedTaskList_' s));
     ret \<leftarrow> condition
       (\<lambda>s. Scheduler_V611_Parse.xLIST_C.uxNumberOfItems_C
          (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
            (Scheduler_V611_Parse.globals.pxDelayedTaskList_' s)) \<noteq> 0)
       (do {
         guard
           (\<lambda>s. c_guard
             (Scheduler_V611_Parse.xMINI_LIST_ITEM_C.pxNext_C
               (Scheduler_V611_Parse.xLIST_C.xListEnd_C
                 (h_val
                   (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
                   (Scheduler_V611_Parse.globals.pxDelayedTaskList_' s)))));
         guard
           (\<lambda>s. c_guard
             (PTR(Scheduler_V611_Parse.xMINI_LIST_ITEM_C)
               &(Scheduler_V611_Parse.globals.pxDelayedTaskList_' s
                 \<rightarrow>[''xListEnd_C''])));
         gets
           (\<lambda>s. Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
             (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
               (Scheduler_V611_Parse.xMINI_LIST_ITEM_C.pxNext_C
                 (Scheduler_V611_Parse.xLIST_C.xListEnd_C
                   (h_val
                     (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
                     (Scheduler_V611_Parse.globals.pxDelayedTaskList_' s))))))
       })
       (return NULL);
     return
       (PTR_COERCE(unit \<rightarrow>
          Scheduler_V611_Parse.tskTaskControlBlock_C) ret)
   }"

definition one_due_tick_after_generic_source ::
  "Scheduler_V611_Parse.tskTaskControlBlock_C ptr \<Rightarrow>
   (unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr,
     Scheduler_V611_Parse.globals) spec_monad"
where
  "one_due_tick_after_generic_source pxTCB = do {
     ret \<leftarrow> one_due_tick_event_dispatch_source pxTCB;
     one_due_tick_top_ready_tail_source pxTCB
   }"

definition one_due_tick_loop_body_source ::
  "Scheduler_V611_Parse.tskTaskControlBlock_C ptr \<Rightarrow>
    (unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr,
      Scheduler_V611_Parse.globals) exn_monad"
where
  "one_due_tick_loop_body_source pxTCB = do {
     liftE (do {
       guard (\<lambda>_. c_guard (scheduler_generic_item_ptr pxTCB));
       guard (\<lambda>_. c_guard pxTCB)
     });
     condition
       (\<lambda>s. Scheduler_V611_Parse.globals.xTickCount_' s <
          Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C
            (Scheduler_V611_Parse.tskTaskControlBlock_C.xGenericListItem_C
              (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
                pxTCB)))
       (throw ())
       skip;
     liftE (do {
       ret \<leftarrow> Scheduler_V611_Delay_Translation.vListRemove'
         (scheduler_generic_item_ptr pxTCB);
       one_due_tick_after_generic_source pxTCB
     })
   }"

definition one_due_tick_unlocked_source ::
  "(unit, unit, Scheduler_V611_Parse.globals) spec_monad"
where
  "one_due_tick_unlocked_source = do {
     modify
       (Scheduler_V611_Parse.globals.xTickCount_'_update (\<lambda>a. a + 1));
     condition
       (\<lambda>s. Scheduler_V611_Parse.globals.xTickCount_' s = 0)
       (do {
         pxTemp \<leftarrow> gets
           Scheduler_V611_Parse.globals.pxDelayedTaskList_';
         modify
           (\<lambda>s. s\<lparr>Scheduler_V611_Parse.globals.pxDelayedTaskList_' :=
             Scheduler_V611_Parse.globals.pxOverflowDelayedTaskList_' s\<rparr>);
         modify
           (Scheduler_V611_Parse.globals.pxOverflowDelayedTaskList_'_update
             (\<lambda>_. pxTemp));
         guard
           (\<lambda>s. 0 \<le> 2147483649 +
             sint (Scheduler_V611_Parse.globals.xNumOfOverflows_' s));
         guard
           (\<lambda>s. sint
             (Scheduler_V611_Parse.globals.xNumOfOverflows_' s) < INT_MAX);
         modify
           (Scheduler_V611_Parse.globals.xNumOfOverflows_'_update
             (\<lambda>a. a + 1))
       })
       skip;
     guard
       (\<lambda>s. c_guard
         (Scheduler_V611_Parse.globals.pxDelayedTaskList_' s));
     ret \<leftarrow> condition
       (\<lambda>s. Scheduler_V611_Parse.xLIST_C.uxNumberOfItems_C
          (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
            (Scheduler_V611_Parse.globals.pxDelayedTaskList_' s)) \<noteq> 0)
       (do {
         guard
           (\<lambda>s. c_guard
             (Scheduler_V611_Parse.xMINI_LIST_ITEM_C.pxNext_C
               (Scheduler_V611_Parse.xLIST_C.xListEnd_C
                 (h_val
                   (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
                   (Scheduler_V611_Parse.globals.pxDelayedTaskList_' s)))));
         guard
           (\<lambda>s. c_guard
             (PTR(Scheduler_V611_Parse.xMINI_LIST_ITEM_C)
               &(Scheduler_V611_Parse.globals.pxDelayedTaskList_' s
                 \<rightarrow>[''xListEnd_C''])));
         gets
           (\<lambda>s. Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
             (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
               (Scheduler_V611_Parse.xMINI_LIST_ITEM_C.pxNext_C
                 (Scheduler_V611_Parse.xLIST_C.xListEnd_C
                   (h_val
                     (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
                     (Scheduler_V611_Parse.globals.pxDelayedTaskList_' s))))))
       })
       (return NULL);
      finally
        (do {
          pxTCB \<leftarrow> whileLoop (\<lambda>pxTCB _. pxTCB \<noteq> NULL)
            one_due_tick_loop_body_source
            (PTR_COERCE(unit \<rightarrow>
              Scheduler_V611_Parse.tskTaskControlBlock_C) ret);
          skip
        })
    }"

theorem one_due_vTaskIncrementTick_named_outer_source:
  "Scheduler_V611_Delay_Translation.vTaskIncrementTick' \<equiv>
     condition
       (\<lambda>s. Scheduler_V611_Parse.globals.uxSchedulerSuspended_' s = 0)
       one_due_tick_unlocked_source
       (modify
         (Scheduler_V611_Parse.globals.uxMissedTicks_'_update
           (\<lambda>a. a + 1)))"
  unfolding
    one_due_tick_unlocked_source_def
    one_due_tick_loop_body_source_def
    one_due_tick_after_generic_source_def
    one_due_tick_top_ready_tail_source_def
    one_due_tick_event_dispatch_source_def
    one_due_tick_event_guard_def
    scheduler_generic_item_ptr_def
    scheduler_event_item_ptr_def
  by (rule Scheduler_V611_Delay_Translation.vTaskIncrementTick'_def)

corollary one_due_gateH_source_ready_rootD:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and roots: "R = generated_scheduler_roots"
  shows
    "one_due_target_root C =
       abi_list_ptr
         (array_ptr_index Scheduler_V611_Parse.pxReadyTasksLists_'
           False (odc_priority C (odc_task C)))"
  using one_due_gateH_exact_rootsD[OF rel] roots by simp

corollary one_due_gateH_source_ready_selectionD:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and roots: "R = generated_scheduler_roots"
  shows
    "one_due_target_root C =
       abi_list_ptr
         (array_ptr_index Scheduler_V611_Parse.pxReadyTasksLists_'
           False
           (unat
             (Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
               (h_val
                 (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
                 (sd_tcb_ptr D (odc_task C))))))"
proof -
  have root:
    "one_due_target_root C =
       abi_list_ptr
         (array_ptr_index Scheduler_V611_Parse.pxReadyTasksLists_'
           False (odc_priority C (odc_task C)))"
    by (rule one_due_gateH_source_ready_rootD[OF rel roots])
  have priority:
    "unat
       (Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
         (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
           (sd_tcb_ptr D (odc_task C)))) =
     odc_priority C (odc_task C)"
    by (rule one_due_gateH_priorityD[OF rel])
  show ?thesis using root priority by simp
qed

lemma one_due_tick_linked_event_guard_after_genericD:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C (DueEventLinked owner) S
       generic_raw event_raw"
  shows
    "one_due_tick_event_guard
       (sd_tcb_ptr D (odc_task C))
       (scheduler_mem_state
         (one_due_generic_remove_heap D C
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))) c)"
proof -
  let ?h = "one_due_generic_remove_heap D C
    (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))"
  have linked:
    "raw_xlist_rel ?h owner (event_raw owner) \<and>
     event_item_raw_ptr D (odc_task C) \<in> set (ring (event_raw owner))"
    by (rule one_due_gateH_linked_event_after_genericD[OF rel])
  have container:
    "List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvContainer_C
       (h_val ?h (event_item_raw_ptr D (odc_task C))) =
     PTR_COERCE(List_V611_Raw_Skip_Translation.xLIST_C \<rightarrow> unit)
       owner"
    using linked
    by (auto simp: raw_xlist_rel_def raw_xlist_view_def)
  have owner_guard: "c_guard owner"
    using linked
    by (auto simp: raw_xlist_rel_def raw_xlist_layout_def)
  have owner_not_null:
    "PTR_COERCE(List_V611_Raw_Skip_Translation.xLIST_C \<rightarrow> unit)
       owner \<noteq> NULL"
  proof -
    have "owner \<noteq> NULL"
      by (rule c_guard_NULL[OF owner_guard])
    then show ?thesis by simp
  qed
  show ?thesis
    unfolding one_due_tick_event_guard_def
    using container owner_not_null
    by (simp flip: scheduler_event_item_h_val abi_item_container_h_val
        add: event_item_raw_ptr_def scheduler_event_item_ptr_def
          abi_event_list_item_ptr_def)
qed

lemma one_due_tick_null_event_guard_after_genericD:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C DueEventNull S
       generic_raw event_raw"
  shows
    "\<not> one_due_tick_event_guard
       (sd_tcb_ptr D (odc_task C))
       (scheduler_mem_state
         (one_due_generic_remove_heap D C
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))) c)"
proof -
  have null:
    "List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvContainer_C
       (h_val
         (one_due_generic_remove_heap D C
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))
         (event_item_raw_ptr D (odc_task C))) = NULL"
    by (rule one_due_gateH_null_event_after_genericD[OF rel])
  show ?thesis
    unfolding one_due_tick_event_guard_def
    using null
    by (simp flip: scheduler_event_item_h_val abi_item_container_h_val
        add: event_item_raw_ptr_def scheduler_event_item_ptr_def
          abi_event_list_item_ptr_def)
qed

theorem one_due_generated_event_dispatch_cutpoint:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
  shows
    "one_due_tick_event_dispatch_source
       (sd_tcb_ptr D (odc_task C)) \<bullet>
       (scheduler_mem_state
         (one_due_generic_remove_heap D C
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))) c)
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       t = scheduler_mem_state
         (one_due_event_remove_heap D C branch
           (one_due_generic_remove_heap D C
             (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))) c
     \<rbrace>"
proof (cases branch)
  case (DueEventLinked owner)
  have rel_linked:
    "one_due_gateH_entry_rel D R c a C (DueEventLinked owner) S
       generic_raw event_raw"
    using rel DueEventLinked by simp
  have enabled:
    "one_due_tick_event_guard
       (sd_tcb_ptr D (odc_task C))
       (scheduler_mem_state
         (one_due_generic_remove_heap D C
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))) c)"
    by (rule one_due_tick_linked_event_guard_after_genericD[OF rel_linked])
  note execution =
    one_due_linked_event_remove_generated_leaf_after_generic[OF rel_linked]
  show ?thesis
    unfolding one_due_tick_event_dispatch_source_def
    apply (simp only: runs_to_condition_iff enabled if_True)
    using execution DueEventLinked by simp
next
  case DueEventNull
  have rel_null:
    "one_due_gateH_entry_rel D R c a C DueEventNull S
       generic_raw event_raw"
    using rel DueEventNull by simp
  have disabled:
    "\<not> one_due_tick_event_guard
       (sd_tcb_ptr D (odc_task C))
       (scheduler_mem_state
         (one_due_generic_remove_heap D C
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))) c)"
    by (rule one_due_tick_null_event_guard_after_genericD[OF rel_null])
  show ?thesis
    unfolding one_due_tick_event_dispatch_source_def
    apply (simp only: runs_to_condition_iff disabled if_False)
    using DueEventNull
    by (runs_to_vcg; simp add: one_due_event_remove_heap_def)
qed

theorem one_due_generated_event_then_top_ready_cutpoint:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and tail:
    "one_due_tick_top_ready_tail_source
       (sd_tcb_ptr D (odc_task C)) \<bullet>
       (scheduler_mem_state
         (one_due_event_remove_heap D C branch
           (one_due_generic_remove_heap D C
             (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))) c)
     \<lbrace>Q\<rbrace>"
  shows
    "one_due_tick_after_generic_source
       (sd_tcb_ptr D (odc_task C)) \<bullet>
       (scheduler_mem_state
         (one_due_generic_remove_heap D C
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))) c)
     \<lbrace>Q\<rbrace>"
proof -
  note event = one_due_generated_event_dispatch_cutpoint[OF rel]
  show ?thesis
    unfolding one_due_tick_after_generic_source_def
    apply (rule runs_to_bind)
    apply (rule runs_to_weaken[OF event])
    using tail by auto
qed

theorem one_due_generated_generic_event_then_top_ready_cutpoint:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and tail:
    "one_due_tick_top_ready_tail_source
       (sd_tcb_ptr D (odc_task C)) \<bullet>
       (scheduler_mem_state
         (one_due_event_remove_heap D C branch
           (one_due_generic_remove_heap D C
             (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))) c)
     \<lbrace>Q\<rbrace>"
  shows
    "bind
       (Scheduler_V611_Delay_Translation.vListRemove'
         (scheduler_generic_item_ptr (sd_tcb_ptr D (odc_task C))))
       (\<lambda>_. one_due_tick_after_generic_source
         (sd_tcb_ptr D (odc_task C))) \<bullet> c
     \<lbrace>Q\<rbrace>"
proof -
  note generic = one_due_generic_remove_generated_leaf[OF rel]
  note after = one_due_generated_event_then_top_ready_cutpoint[OF rel tail]
  show ?thesis
    apply (rule runs_to_bind)
    apply (rule runs_to_weaken[OF generic])
     apply clarsimp
    apply (rule after)
    done
qed

text \<open>
  The named source theorem above is an exact refactoring of the generated
  vTaskIncrementTick' definition.  It exposes the actual delayed-task loop,
  its physical pvContainer read, the generated Event vListRemove' call or NULL
  skip, the uxTopReadyPriority conditional assignment, the four-priority
  guard, the generated ready-array selection and vListInsertEnd' call, and the
  next delayed-head fetch.  No task, priority, pointer, tick, ring, cursor,
  payload, heap, or global is fixed to a runtime constant.

  The dispatch theorem proves that the physical generated conditional selects
  precisely the linked remove or NULL skip described by the arbitrary branch.
  The continuation theorems compose that decision with the preceding generated
  Generic remove and then hand the exact residual top/ready source term to the
  next VCG proof.  A theorem for the complete while body is
  intentionally not claimed yet: that residual continuation is a real proof
  obligation, not a proof-side replacement for the generated code.

  The immediate Generic contract carries the updated delayed root, every
  non-source Generic root, and every Event raw root.  After the actual Event
  branch, the next resume contract must promote the pointwise facts to complete
  Generic and Event family relations and also carry cross-family storage
  separation and TaskObservation/priority/owner frames.

  The two ready-selection corollaries align sr_ready R with the generated
  array_ptr_index expression under the compile-time identification
  R = generated_scheduler_roots; this is not a runtime value restriction.
  The smallest remaining lemma must transport that selection, the TCB priority
  and owner observations, the ready-root relation and insert freshness through
  both removals.  Together with the generated ready-array guard, that
  post-Event preservation contract is the exact precondition needed by the
  generated vListInsertEnd' leaf.  The next-head read must then re-establish the
  loop invariant, including the exceptional future-head exit.

  Nor does one_due_gateH_entry_rel yet identify the snapshot families with
  every scheduler_abs ready/delayed/suspended field or external Event
  membership with sa_event_waiting.  Those mappings, plus the scheduler scalar
  and delayed-role relation, are an explicit next bridge before any theorem may
  be advertised as tick_wake_one_abs or the complete Gate-H result.  TopRaised
  is deliberately only an intermediate source-order state; a ready-cache
  witness is required again only after GenericReady.
\<close>

end
