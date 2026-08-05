theory Scheduler_One_Due_Task_Phases_Tick_Loop
  imports
    "EAL6_FreeRTOS_V611_Scheduler_One_Due_Task_Phases_Reentry_GateH.Scheduler_One_Due_Task_Phases_Reentry_GateH"
begin

text \<open>
  The complete due-iteration of the generated delayed-task loop body.
  At a gate state the two guards discharge from the observation, the
  due-compare condition takes the skip branch because the gate carries
  the head's dueness, and the residual Generic remove, Event dispatch
  and top/ready tail execute through the accepted cutpoints down to
  the delayed-head remainder, whose continuation receives the exact
  insert heap and the pinned globals.
\<close>

lemma one_due_tcb_generic_key_read:
  "Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C
     (Scheduler_V611_Parse.tskTaskControlBlock_C.xGenericListItem_C
       (h_val h tp)) =
   raw_key_at h (abi_generic_list_item_ptr tp)"
  by (simp add: raw_key_at_def abi_generic_list_item_ptr_def
      scheduler_generic_item_ptr_def abi_item_key_h_val
      flip: scheduler_generic_item_h_val)

lemma one_due_gateH_head_dueD:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
  shows
    "ods_generic_payload S (odc_task C) \<le> odc_tick C"
  using one_due_gateH_pure_entryD[OF rel]
  by (simp add: one_due_entry_rel_def)

lemma one_due_gateH_tick_wordD:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
  shows
    "odc_tick C = Scheduler_V611_Parse.globals.xTickCount_' c"
  using rel
  unfolding one_due_gateH_entry_rel_def Let_def
  by blast

theorem one_due_tick_body_composed:
  fixes Q
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and roots: "R = generated_scheduler_roots"
    and cont:
      "\<And>t. hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' t) =
           one_due_ready_insert_heap D C generic_raw
             (one_due_event_remove_heap D C branch
               (one_due_generic_remove_heap D C
                 (hrs_mem
                   (Scheduler_V611_Parse.globals.t_hrs_' c)))) \<Longrightarrow>
         Scheduler_V611_Parse.globals.pxDelayedTaskList_' t =
           Scheduler_V611_Parse.globals.pxDelayedTaskList_' c \<Longrightarrow>
         Scheduler_V611_Parse.globals.uxTopReadyPriority_' t =
           (if Scheduler_V611_Parse.globals.uxTopReadyPriority_' c <
              Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
                (h_val
                  (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
                  (sd_tcb_ptr D (odc_task C)))
            then
              Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
                (h_val
                  (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
                  (sd_tcb_ptr D (odc_task C)))
            else
              Scheduler_V611_Parse.globals.uxTopReadyPriority_' c)
           \<Longrightarrow>
         Scheduler_V611_Parse.globals.xTickCount_' t =
           Scheduler_V611_Parse.globals.xTickCount_' c \<Longrightarrow>
         one_due_tick_delayed_remainder \<bullet> t \<lbrace>Q\<rbrace>"
  shows
    "one_due_tick_loop_body_source (sd_tcb_ptr D (odc_task C)) \<bullet> c
     \<lbrace>\<lambda>r t. \<exists>v. r = Result v \<and> Q (Result v) t\<rbrace>"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  let ?tp = "sd_tcb_ptr D (odc_task C)"
  have task_live: "odc_task C \<in> odc_live C"
    by (rule one_due_gateH_task_liveD[OF rel])
  have task_abs: "odc_task C \<in> sa_live a"
    using task_live one_due_gateH_live_absD[OF rel] by simp
  have obs:
    "TaskObservationRel D ?h a"
    by (rule one_due_gateH_task_observationD[OF rel])
  note obs_task = TaskObservationRel_liveD[OF obs task_abs]
  have guard_item:
    "c_guard (scheduler_generic_item_ptr ?tp)"
    using obs_task by blast
  have guard_tcb: "c_guard ?tp"
    using obs_task by blast
  have key_read:
    "Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C
       (Scheduler_V611_Parse.tskTaskControlBlock_C.xGenericListItem_C
         (h_val ?h ?tp)) =
     ods_generic_payload S (odc_task C)"
    using one_due_tcb_generic_key_read[of ?h ?tp]
      one_due_gateH_generic_keysD[OF rel task_live]
    by (simp add: one_due_generic_raw_ptr_def)
  have not_due_false:
    "\<not> Scheduler_V611_Parse.globals.xTickCount_' c <
       Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C
         (Scheduler_V611_Parse.tskTaskControlBlock_C.xGenericListItem_C
           (h_val ?h ?tp))"
    using key_read one_due_gateH_head_dueD[OF rel]
      one_due_gateH_tick_wordD[OF rel]
    by (simp add: not_less)
  have tail:
    "one_due_tick_top_ready_tail_source ?tp \<bullet>
       (scheduler_mem_state
         (one_due_event_remove_heap D C branch
           (one_due_generic_remove_heap D C ?h)) c)
     \<lbrace>Q\<rbrace>"
    by (rule one_due_tick_tail_insert_composed[OF rel roots cont])
  have inner:
    "bind
       (Scheduler_V611_Delay_Translation.vListRemove'
         (scheduler_generic_item_ptr ?tp))
       (\<lambda>_. one_due_tick_after_generic_source ?tp) \<bullet> c
     \<lbrace>Q\<rbrace>"
    by (rule one_due_generated_generic_event_then_top_ready_cutpoint[
      OF rel tail])
  show ?thesis
    unfolding one_due_tick_loop_body_source_def
    apply runs_to_vcg
    subgoal by (rule guard_item)
    subgoal by (rule guard_tcb)
    subgoal using not_due_false by simp
    subgoal
      apply (rule runs_to_weaken[OF
        inner[unfolded runs_to_bind_iff]])
      apply clarsimp
      apply (rule runs_to_weaken)
       apply assumption
      apply clarsimp
      done
    done
qed

definition one_due_tick_body_post ::
  "'tid scheduler_decode \<Rightarrow>
   ('tid, xLIST_C ptr) one_due_context \<Rightarrow>
   xLIST_C ptr one_due_event_branch \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow>
   (unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr)
     exception_or_result \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> bool"
where
  "one_due_tick_body_post D C branch generic_raw c r t \<longleftrightarrow>
     hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' t) =
       one_due_ready_insert_heap D C generic_raw
         (one_due_event_remove_heap D C branch
           (one_due_generic_remove_heap D C
             (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))) \<and>
     Scheduler_V611_Parse.globals.pxDelayedTaskList_' t =
       Scheduler_V611_Parse.globals.pxDelayedTaskList_' c \<and>
     Scheduler_V611_Parse.globals.uxTopReadyPriority_' t =
       (if Scheduler_V611_Parse.globals.uxTopReadyPriority_' c <
          Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
            (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
              (sd_tcb_ptr D (odc_task C)))
        then Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
            (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
              (sd_tcb_ptr D (odc_task C)))
        else Scheduler_V611_Parse.globals.uxTopReadyPriority_' c)
     \<and>
     Scheduler_V611_Parse.globals.xTickCount_' t =
       Scheduler_V611_Parse.globals.xTickCount_' c \<and>
     r = Result (
       if ring (list_remove_abs
            (one_due_generic_raw_ptr D (odc_task C))
            (generic_raw (odc_delayed_root C))) = []
       then NULL
       else PTR_COERCE(unit \<rightarrow>
              Scheduler_V611_Parse.tskTaskControlBlock_C)
         (List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
           (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
             (hd (ring (list_remove_abs
               (one_due_generic_raw_ptr D (odc_task C))
               (generic_raw (odc_delayed_root C))))))))"

theorem one_due_tick_body_exact:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and roots: "R = generated_scheduler_roots"
  shows
    "one_due_tick_loop_body_source (sd_tcb_ptr D (odc_task C)) \<bullet> c
     \<lbrace>\<lambda>r t. \<exists>v. r = Result v \<and>
        one_due_tick_body_post D C branch generic_raw c
          (Result v) t\<rbrace>"
proof (rule one_due_tick_body_composed[OF rel roots])
  fix t :: "Scheduler_V611_Parse.globals"
  assume h:
    "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' t) =
     one_due_ready_insert_heap D C generic_raw
       (one_due_event_remove_heap D C branch
         (one_due_generic_remove_heap D C
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))))"
    and d:
    "Scheduler_V611_Parse.globals.pxDelayedTaskList_' t =
     Scheduler_V611_Parse.globals.pxDelayedTaskList_' c"
    and p:
    "Scheduler_V611_Parse.globals.uxTopReadyPriority_' t =
     (if Scheduler_V611_Parse.globals.uxTopReadyPriority_' c <
        Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
          (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
            (sd_tcb_ptr D (odc_task C)))
      then Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
          (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
            (sd_tcb_ptr D (odc_task C)))
      else Scheduler_V611_Parse.globals.uxTopReadyPriority_' c)"
    and k:
    "Scheduler_V611_Parse.globals.xTickCount_' t =
     Scheduler_V611_Parse.globals.xTickCount_' c"
  show "one_due_tick_delayed_remainder \<bullet> t
     \<lbrace>one_due_tick_body_post D C branch generic_raw c\<rbrace>"
    apply (rule runs_to_weaken[OF
      one_due_tick_delayed_remainder_exact[OF rel h d]])
    using h d p k
    by (auto simp: one_due_tick_body_post_def)
qed

end
