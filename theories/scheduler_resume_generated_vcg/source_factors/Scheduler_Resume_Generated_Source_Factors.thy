theory Scheduler_Resume_Generated_Source_Factors
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Pending_Drain_Gate.Scheduler_Resume_Pending_Drain_Gate"
begin

section \<open>Named generated-source factors\<close>

definition resume_pending_generated_head_read ::
  "(unit ptr, Scheduler_V611_Parse.globals) res_monad"
where
  "resume_pending_generated_head_read =
     condition
       (\<lambda>s. Scheduler_V611_Parse.xLIST_C.uxNumberOfItems_C
          (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
            Scheduler_V611_Parse.xPendingReadyList_') \<noteq> 0)
       (do {
          guard (\<lambda>s. c_guard
            (Scheduler_V611_Parse.xMINI_LIST_ITEM_C.pxNext_C
              (Scheduler_V611_Parse.xLIST_C.xListEnd_C
                (h_val (hrs_mem
                  (Scheduler_V611_Parse.globals.t_hrs_' s))
                  Scheduler_V611_Parse.xPendingReadyList_'))));
          gets (\<lambda>s. Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
            (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
              (Scheduler_V611_Parse.xMINI_LIST_ITEM_C.pxNext_C
                (Scheduler_V611_Parse.xLIST_C.xListEnd_C
                  (h_val (hrs_mem
                    (Scheduler_V611_Parse.globals.t_hrs_' s))
                    Scheduler_V611_Parse.xPendingReadyList_')))))
        })
       (return NULL)"

definition resume_pending_generated_cond ::
  "(Scheduler_V611_Parse.tskTaskControlBlock_C ptr \<times> int) \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> bool"
where
  "resume_pending_generated_cond pair s \<longleftrightarrow> fst pair \<noteq> NULL"

definition resume_pending_generated_body ::
  "(Scheduler_V611_Parse.tskTaskControlBlock_C ptr \<times> int) \<Rightarrow>
   ((Scheduler_V611_Parse.tskTaskControlBlock_C ptr \<times> int),
    Scheduler_V611_Parse.globals) res_monad"
where
  "resume_pending_generated_body pair =
     (case pair of (pxTCB, xYieldRequired) \<Rightarrow> do {
        guard (\<lambda>_. c_guard pxTCB);
        ret \<leftarrow> Scheduler_V611_Delay_Translation.vListRemove'
          (PTR(Scheduler_V611_Parse.xLIST_ITEM_C)
            &(pxTCB\<rightarrow>[''xEventListItem_C'']));
        ret \<leftarrow> Scheduler_V611_Delay_Translation.vListRemove'
          (PTR(Scheduler_V611_Parse.xLIST_ITEM_C)
            &(pxTCB\<rightarrow>[''xGenericListItem_C'']));
        condition
          (\<lambda>s. Scheduler_V611_Parse.globals.uxTopReadyPriority_' s <
            Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
              (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
                pxTCB))
          (modify (\<lambda>s. s\<lparr>
            Scheduler_V611_Parse.globals.uxTopReadyPriority_' :=
              Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
                (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
                  pxTCB)\<rparr>))
          skip;
        x \<leftarrow> guard
          (\<lambda>s. Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
            (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
              pxTCB) < 4);
        guard (\<lambda>_. c_guard Scheduler_V611_Parse.pxReadyTasksLists_');
        pxList \<leftarrow> gets (\<lambda>s.
          array_ptr_index Scheduler_V611_Parse.pxReadyTasksLists_' False
            (unat
              (Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
                (h_val (hrs_mem
                  (Scheduler_V611_Parse.globals.t_hrs_' s)) pxTCB))));
        ret \<leftarrow> Scheduler_V611_Delay_Translation.vListInsertEnd'
          pxList
          (PTR(Scheduler_V611_Parse.xLIST_ITEM_C)
            &(pxTCB\<rightarrow>[''xGenericListItem_C'']));
        guard (\<lambda>s. c_guard
          (Scheduler_V611_Parse.globals.pxCurrentTCB_' s));
        xYieldRequired \<leftarrow> condition
          (\<lambda>s. Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
              (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
                (Scheduler_V611_Parse.globals.pxCurrentTCB_' s)) \<le>
            Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
              (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
                pxTCB))
          (return 1)
          (return xYieldRequired);
        next_owner \<leftarrow> resume_pending_generated_head_read;
        return
          (PTR_COERCE(unit \<rightarrow>
             Scheduler_V611_Parse.tskTaskControlBlock_C) next_owner,
           xYieldRequired)
      })"

definition resume_missed_generated_cond ::
  "unit \<Rightarrow> Scheduler_V611_Parse.globals \<Rightarrow> bool"
where
  "resume_missed_generated_cond _ s \<longleftrightarrow>
     0 < Scheduler_V611_Parse.globals.uxMissedTicks_' s"

definition resume_missed_generated_body ::
  "unit \<Rightarrow> (unit, Scheduler_V611_Parse.globals) res_monad"
where
  "resume_missed_generated_body _ = do {
     ret \<leftarrow> Scheduler_V611_Delay_Translation.vTaskIncrementTick';
     modify (Scheduler_V611_Parse.globals.uxMissedTicks_'_update
       (\<lambda>a. a - 1))
   }"

section \<open>Initial pending-head read\<close>

lemma resume_pending_gate_nonempty_source_pending_countD:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
    and roots: "R = generated_scheduler_roots"
  shows
    "Scheduler_V611_Parse.xLIST_C.uxNumberOfItems_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
         Scheduler_V611_Parse.xPendingReadyList_') \<noteq> 0"
proof -
  have pending_root: "rpc_pending_root C \<in> rpc_event_roots C"
    using resume_pending_gate_pure_entryD[OF rel]
    by (auto simp: resume_pending_entry_rel_def
        resume_pending_context_wf_def)
  have count:
    "unat (List_V611_Raw_Skip_Translation.xLIST_C.uxNumberOfItems_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
         (rpc_pending_root C))) =
       length (ring (rps_event_family S (rpc_pending_root C)))"
    by (rule scheduler_event_root_family_countD[
      OF resume_pending_gate_event_familyD[OF rel] pending_root])
  have ring:
    "ring (rps_event_family S (rpc_pending_root C)) =
       Event t # map Event rest"
    using resume_pending_gate_pure_entryD[OF rel] tasks
    by (simp add: resume_pending_entry_rel_def)
  have root:
    "rpc_pending_root C =
       abi_list_ptr Scheduler_V611_Parse.xPendingReadyList_'"
    by (rule resume_pending_gate_source_pending_rootD[OF rel roots])
  have raw_nonzero:
    "List_V611_Raw_Skip_Translation.xLIST_C.uxNumberOfItems_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
         (abi_list_ptr Scheduler_V611_Parse.xPendingReadyList_')) \<noteq> 0"
    using count ring root by (auto simp: unat_eq_0)
  have count_eq:
    "List_V611_Raw_Skip_Translation.xLIST_C.uxNumberOfItems_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
         (abi_list_ptr Scheduler_V611_Parse.xPendingReadyList_')) =
     Scheduler_V611_Parse.xLIST_C.uxNumberOfItems_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
         Scheduler_V611_Parse.xPendingReadyList_')"
    by (rule abi_list_count_h_val)
  show ?thesis
    using raw_nonzero count_eq by simp
qed

theorem resume_pending_generated_head_read_nonempty:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
    and roots: "R = generated_scheduler_roots"
  shows
    "resume_pending_generated_head_read \<bullet> c
     \<lbrace>\<lambda>r s.
       r = Result
         (PTR_COERCE(Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow> unit)
           (sd_tcb_ptr D t)) \<and>
       s = c
     \<rbrace>"
proof -
  have live: "t \<in> sa_live a"
    using resume_pending_gate_head_liveD[OF rel tasks] rel
    unfolding resume_pending_gate_entry_rel_def Let_def
    by blast
  have observation:
    "TaskObservationRel D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) a"
    using rel
    unfolding resume_pending_gate_entry_rel_def Let_def
    by blast
  have event_guard:
    "c_guard (scheduler_event_item_ptr (sd_tcb_ptr D t))"
    using TaskObservationRel_liveD[OF observation live] by blast
  note head_owner = resume_pending_gate_head_owner_priorityD[OF rel tasks]
  have head_ptr:
    "Scheduler_V611_Parse.xMINI_LIST_ITEM_C.pxNext_C
       (Scheduler_V611_Parse.xLIST_C.xListEnd_C
         (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
           Scheduler_V611_Parse.xPendingReadyList_')) =
       scheduler_event_item_ptr (sd_tcb_ptr D t)"
    using head_owner roots
    by (simp add: scheduler_list_head_item_def)
  have event_owner:
    "Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
         (scheduler_event_item_ptr (sd_tcb_ptr D t))) =
       PTR_COERCE(Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow> unit)
         (sd_tcb_ptr D t)"
    using TaskObservationRel_liveD[OF observation live] by blast
  note count = resume_pending_gate_nonempty_source_pending_countD[
    OF rel tasks roots]
  show ?thesis
    unfolding resume_pending_generated_head_read_def
    apply runs_to_vcg
    using count head_ptr event_guard event_owner
    by simp_all
qed

theorem resume_pending_generated_head_read_empty:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = []"
    and roots: "R = generated_scheduler_roots"
  shows
    "resume_pending_generated_head_read \<bullet> c
     \<lbrace>\<lambda>r s. r = Result NULL \<and> s = c\<rbrace>"
proof -
  note count = resume_pending_gate_empty_source_pending_countD[
    OF rel tasks roots]
  show ?thesis
    unfolding resume_pending_generated_head_read_def
    apply runs_to_vcg
    using count by simp_all
qed

end
