theory Scheduler_P2_Raw_Relation
  imports
    "EAL6_FreeRTOS_V611_Scheduler_List_ABI_Bridge.Scheduler_List_ABI_Bridge"
    "EAL6_FreeRTOS_V611_Scheduler_Raw_List_Relabel.Scheduler_Raw_List_Relabel"
    "EAL6_FreeRTOS_V611_Scheduler_P2_Model.Scheduler_P2_Model"
begin

text \<open>
  First layered scheduler representation relation over the checked
  translation-unit ABI lens.  Decoder and footprint laws remain explicit
  assumptions: this theory proves conditional P2 endpoint introduction, not
  existence of a concrete preimage and not source refinement.
\<close>

record 'tid scheduler_decode =
  sd_tcb_ptr ::
    "'tid \<Rightarrow> Scheduler_V611_Parse.tskTaskControlBlock_C ptr"
  sd_tcb_decode ::
    "Scheduler_V611_Parse.tskTaskControlBlock_C ptr \<Rightarrow> 'tid option"
  sd_node_decode ::
    "List_V611_Raw_Skip_Translation.xLIST_ITEM_C ptr
       \<Rightarrow> 'tid node_kind option"

record scheduler_roots =
  sr_ready :: "nat \<Rightarrow> Scheduler_V611_Parse.xLIST_C ptr"
  sr_delayed_a :: "Scheduler_V611_Parse.xLIST_C ptr"
  sr_delayed_b :: "Scheduler_V611_Parse.xLIST_C ptr"
  sr_pending :: "Scheduler_V611_Parse.xLIST_C ptr"
  sr_suspended :: "Scheduler_V611_Parse.xLIST_C ptr"

definition generated_scheduler_roots :: scheduler_roots where
  "generated_scheduler_roots =
     \<lparr>
       sr_ready =
         array_ptr_index Scheduler_V611_Parse.pxReadyTasksLists_' False,
       sr_delayed_a = Scheduler_V611_Parse.xDelayedTaskList1_',
       sr_delayed_b = Scheduler_V611_Parse.xDelayedTaskList2_',
       sr_pending = Scheduler_V611_Parse.xPendingReadyList_',
       sr_suspended = Scheduler_V611_Parse.xSuspendedTaskList_'
     \<rparr>"

lemma generated_scheduler_roots_fields[simp]:
  "sr_ready generated_scheduler_roots p =
     array_ptr_index Scheduler_V611_Parse.pxReadyTasksLists_' False p \<and>
   sr_delayed_a generated_scheduler_roots =
     Scheduler_V611_Parse.xDelayedTaskList1_' \<and>
   sr_delayed_b generated_scheduler_roots =
     Scheduler_V611_Parse.xDelayedTaskList2_' \<and>
   sr_pending generated_scheduler_roots =
     Scheduler_V611_Parse.xPendingReadyList_' \<and>
   sr_suspended generated_scheduler_roots =
     Scheduler_V611_Parse.xSuspendedTaskList_'"
  by (simp add: generated_scheduler_roots_def)

definition scheduler_decode_rel ::
  "'tid scheduler_decode \<Rightarrow> 'tid scheduler_abs \<Rightarrow> bool"
where
  "scheduler_decode_rel D a \<longleftrightarrow>
     inj_on (sd_tcb_ptr D) (sa_live a) \<and>
     (\<forall>t \<in> sa_live a.
        sd_tcb_decode D (sd_tcb_ptr D t) = Some t \<and>
        sd_node_decode D (abi_generic_list_item_ptr (sd_tcb_ptr D t)) =
          Some (Generic t) \<and>
        sd_node_decode D (abi_event_list_item_ptr (sd_tcb_ptr D t)) =
          Some (Event t)) \<and>
     (\<forall>p t. sd_tcb_decode D p = Some t \<longrightarrow>
        t \<in> sa_live a \<and> p = sd_tcb_ptr D t) \<and>
     (\<forall>p t. sd_node_decode D p = Some (Generic t) \<longrightarrow>
        p = abi_generic_list_item_ptr (sd_tcb_ptr D t)) \<and>
     (\<forall>p t. sd_node_decode D p = Some (Event t) \<longrightarrow>
        p = abi_event_list_item_ptr (sd_tcb_ptr D t)) \<and>
     (\<forall>p n. sd_node_decode D p = Some n \<longrightarrow>
        node_owner n \<in> sa_live a)"

lemma scheduler_tcb_decode_iff:
  assumes rel: "scheduler_decode_rel D a"
  shows
    "sd_tcb_decode D p = Some t \<longleftrightarrow>
       t \<in> sa_live a \<and> p = sd_tcb_ptr D t"
  using rel
  by (auto simp: scheduler_decode_rel_def)

lemma scheduler_node_decode_Generic_iff:
  assumes rel: "scheduler_decode_rel D a"
  shows
    "sd_node_decode D p = Some (Generic t) \<longleftrightarrow>
       t \<in> sa_live a \<and>
       p = abi_generic_list_item_ptr (sd_tcb_ptr D t)"
proof
  assume decoded: "sd_node_decode D p = Some (Generic t)"
  from rel decoded have owner_live:
    "node_owner (Generic t) \<in> sa_live a"
    unfolding scheduler_decode_rel_def by blast
  then have live: "t \<in> sa_live a" by simp
  from rel decoded have ptr:
    "p = abi_generic_list_item_ptr (sd_tcb_ptr D t)"
    unfolding scheduler_decode_rel_def by blast
  show "t \<in> sa_live a \<and>
        p = abi_generic_list_item_ptr (sd_tcb_ptr D t)"
    using live ptr by blast
next
  assume rhs:
    "t \<in> sa_live a \<and>
     p = abi_generic_list_item_ptr (sd_tcb_ptr D t)"
  from rel have forward:
    "\<forall>u \<in> sa_live a.
       sd_node_decode D (abi_generic_list_item_ptr (sd_tcb_ptr D u)) =
         Some (Generic u)"
    unfolding scheduler_decode_rel_def by blast
  from forward rhs show "sd_node_decode D p = Some (Generic t)"
    by blast
qed

lemma scheduler_node_decode_Event_iff:
  assumes rel: "scheduler_decode_rel D a"
  shows
    "sd_node_decode D p = Some (Event t) \<longleftrightarrow>
       t \<in> sa_live a \<and>
       p = abi_event_list_item_ptr (sd_tcb_ptr D t)"
proof
  assume decoded: "sd_node_decode D p = Some (Event t)"
  from rel decoded have owner_live:
    "node_owner (Event t) \<in> sa_live a"
    unfolding scheduler_decode_rel_def by blast
  then have live: "t \<in> sa_live a" by simp
  from rel decoded have ptr:
    "p = abi_event_list_item_ptr (sd_tcb_ptr D t)"
    unfolding scheduler_decode_rel_def by blast
  show "t \<in> sa_live a \<and>
        p = abi_event_list_item_ptr (sd_tcb_ptr D t)"
    using live ptr by blast
next
  assume rhs:
    "t \<in> sa_live a \<and>
     p = abi_event_list_item_ptr (sd_tcb_ptr D t)"
  from rel have forward:
    "\<forall>u \<in> sa_live a.
       sd_node_decode D (abi_event_list_item_ptr (sd_tcb_ptr D u)) =
         Some (Event u)"
    unfolding scheduler_decode_rel_def by blast
  from forward rhs show "sd_node_decode D p = Some (Event t)"
    by blast
qed

definition scheduler_lists_rel ::
  "'tid scheduler_decode \<Rightarrow> scheduler_roots \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> bool"
where
  "scheduler_lists_rel D R c a \<longleftrightarrow>
     (let h = hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c);
          decode = sd_node_decode D
      in (\<forall>p<4.
            sched_xlist_rel decode h (abi_list_ptr (sr_ready R p))
              (sa_ready a p)) \<and>
         sched_xlist_rel decode h (abi_list_ptr (sr_delayed_a R))
           (sa_delayed_a a) \<and>
         sched_xlist_rel decode h (abi_list_ptr (sr_delayed_b R))
           (sa_delayed_b a) \<and>
         sched_xlist_rel decode h (abi_list_ptr (sr_pending R))
           (sa_pending a) \<and>
         sched_xlist_rel decode h (abi_list_ptr (sr_suspended R))
           (sa_suspended a))"

definition scheduler_role_rel ::
  "scheduler_roots \<Rightarrow> Scheduler_V611_Parse.globals \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> bool"
where
  "scheduler_role_rel R c a \<longleftrightarrow>
     Scheduler_V611_Parse.globals.pxDelayedTaskList_' c =
       (if sa_current_role_a a then sr_delayed_a R else sr_delayed_b R) \<and>
     Scheduler_V611_Parse.globals.pxOverflowDelayedTaskList_' c =
       (if sa_current_role_a a then sr_delayed_b R else sr_delayed_a R)"

definition scheduler_scalar_rel ::
  "Scheduler_V611_Parse.globals \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> bool"
where
  "scheduler_scalar_rel c a \<longleftrightarrow>
     Scheduler_V611_Parse.globals.xTickCount_' c = sa_tick a \<and>
     unat (Scheduler_V611_Parse.globals.uxSchedulerSuspended_' c) =
       sa_suspend_depth a \<and>
     unat (Scheduler_V611_Parse.globals.uxMissedTicks_' c) =
       sa_missed_ticks a \<and>
     Scheduler_V611_Parse.globals.xMissedYield_' c =
       (if sa_missed_yield a then 1 else 0) \<and>
     unat (Scheduler_V611_Parse.globals.uxTopReadyPriority_' c) =
       sa_top_ready a \<and>
     Scheduler_V611_Parse.globals.xNumOfOverflows_' c =
       of_nat (sa_overflows a) \<and>
     unat (Scheduler_V611_Parse.globals.uxCurrentNumberOfTasks_' c) =
       card (sa_live a) \<and>
     unat (Scheduler_V611_Parse.globals.eal6_port_yield_count_' c) =
       sa_yield_count a"

definition scheduler_current_rel ::
  "'tid scheduler_decode \<Rightarrow> Scheduler_V611_Parse.globals
     \<Rightarrow> 'tid scheduler_abs \<Rightarrow> bool"
where
  "scheduler_current_rel D c a \<longleftrightarrow>
     (case sa_current a of
        None \<Rightarrow> Scheduler_V611_Parse.globals.pxCurrentTCB_' c = NULL
      | Some t \<Rightarrow>
          Scheduler_V611_Parse.globals.pxCurrentTCB_' c = sd_tcb_ptr D t)"

definition scheduler_boundary_rel ::
  "Scheduler_V611_Parse.globals \<Rightarrow> bool"
where
  "scheduler_boundary_rel c \<longleftrightarrow>
     Scheduler_V611_Parse.globals.xSchedulerRunning_' c = 1 \<and>
     Scheduler_V611_Parse.globals.eal6_port_critical_depth_' c = 0 \<and>
     Scheduler_V611_Parse.globals.eal6_port_interrupts_disabled_' c = 0"

definition raw_scheduler_rel ::
  "'tid scheduler_decode \<Rightarrow> scheduler_roots \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> bool"
where
  "raw_scheduler_rel D R c a \<longleftrightarrow>
     core_wf a \<and>
     scheduler_decode_rel D a \<and>
     scheduler_lists_rel D R c a \<and>
     scheduler_role_rel R c a \<and>
     scheduler_scalar_rel c a \<and>
     scheduler_current_rel D c a \<and>
     scheduler_boundary_rel c"

datatype scheduler_phase = StableRunning | YieldPending

definition yield_pending_wf :: "'tid scheduler_abs \<Rightarrow> bool" where
  "yield_pending_wf a \<longleftrightarrow>
     core_wf a \<and>
     sa_suspend_depth a = 0 \<and>
     sa_missed_ticks a = 0 \<and>
     ring (sa_pending a) = [] \<and>
     sa_yield_count a > 0"

fun scheduler_endpoint_rel ::
  "scheduler_phase \<Rightarrow> 'tid scheduler_decode \<Rightarrow>
   scheduler_roots \<Rightarrow> Scheduler_V611_Parse.globals \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> bool"
where
  "scheduler_endpoint_rel StableRunning D R c a =
     (raw_scheduler_rel D R c a \<and> settled_wf a)"
| "scheduler_endpoint_rel YieldPending D R c a =
     (raw_scheduler_rel D R c a \<and> yield_pending_wf a)"

lemma raw_scheduler_relI:
  assumes core: "core_wf a"
    and decode: "scheduler_decode_rel D a"
    and lists: "scheduler_lists_rel D R c a"
    and roles: "scheduler_role_rel R c a"
    and scalars: "scheduler_scalar_rel c a"
    and current: "scheduler_current_rel D c a"
    and boundary: "scheduler_boundary_rel c"
  shows "raw_scheduler_rel D R c a"
  using assms by (simp add: raw_scheduler_rel_def)

lemma sched_xlist_rel_emptyE:
  assumes sched: "sched_xlist_rel D h lp q"
    and abs_ring: "ring q = []"
    and abs_cursor: "cursor q = None"
  obtains rx where
    "raw_xlist_rel h lp rx"
    "ring rx = []"
    "cursor rx = None"
proof -
  from sched obtain rx where
      raw: "raw_xlist_rel h lp rx"
    and relabel: "xlist_relabel D rx q"
    by (auto simp: sched_xlist_rel_def)
  have raw_ring: "ring rx = []"
    using xlist_relabel_ring_length[OF relabel] abs_ring
    by (cases "ring rx") auto
  have raw_cursor: "cursor rx = None"
    using relabel abs_cursor
    by (cases "cursor rx") (auto simp: xlist_relabel_def)
  show ?thesis by (rule that[OF raw raw_ring raw_cursor])
qed

lemma p2_pre_ready2_raw_singletonE:
  assumes decode: "scheduler_decode_rel D p2_pre"
    and lists: "scheduler_lists_rel D R c p2_pre"
  obtains rx where
    "raw_xlist_rel
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (abi_list_ptr (sr_ready R 2)) rx"
    "ring rx =
       [abi_generic_list_item_ptr (sd_tcb_ptr D P2_RUN)]"
    "cursor rx =
       Some (abi_generic_list_item_ptr (sd_tcb_ptr D P2_RUN))"
proof -
  have sched:
    "sched_xlist_rel (sd_node_decode D)
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (abi_list_ptr (sr_ready R 2)) (sa_ready p2_pre 2)"
  proof -
    from lists have ready_all:
      "\<forall>p<4. sched_xlist_rel (sd_node_decode D)
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
         (abi_list_ptr (sr_ready R p)) (sa_ready p2_pre p)"
      unfolding scheduler_lists_rel_def Let_def by blast
    from ready_all show ?thesis by simp
  qed
  then obtain rx where
      raw: "raw_xlist_rel
        (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
        (abi_list_ptr (sr_ready R 2)) rx"
    and relabel:
      "xlist_relabel (sd_node_decode D) rx (sa_ready p2_pre 2)"
    by (auto simp: sched_xlist_rel_def)
  have abs_ring:
    "ring (sa_ready p2_pre 2) = [Generic P2_RUN]"
    by (simp add: p2_pre_def)
  have abs_cursor:
    "cursor (sa_ready p2_pre 2) = Some (Generic P2_RUN)"
    by (simp add: p2_pre_def)
  have raw_length: "length (ring rx) = 1"
    using xlist_relabel_ring_length[OF relabel] abs_ring by simp
  then obtain p where raw_ring: "ring rx = [p]"
    by (cases "ring rx") auto
  have pairs:
    "list_all2
       (\<lambda>p n. sd_node_decode D p = Some n)
       (ring rx) (ring (sa_ready p2_pre 2))"
    using relabel by (simp add: xlist_relabel_def)
  have p_decode: "sd_node_decode D p = Some (Generic P2_RUN)"
    using pairs raw_ring abs_ring by simp
  have p_eq:
    "p = abi_generic_list_item_ptr (sd_tcb_ptr D P2_RUN)"
    using scheduler_node_decode_Generic_iff[OF decode, of p P2_RUN]
      p_decode
    by (simp add: p2_pre_def)
  have cursor_rel:
    "rel_option (\<lambda>q n. sd_node_decode D q = Some n)
       (cursor rx) (Some (Generic P2_RUN))"
    using relabel abs_cursor by (simp add: xlist_relabel_def)
  then obtain q where
      cursor_q: "cursor rx = Some q"
    and q_decode: "sd_node_decode D q = Some (Generic P2_RUN)"
    by (cases "cursor rx") auto
  have q_eq:
    "q = abi_generic_list_item_ptr (sd_tcb_ptr D P2_RUN)"
    using scheduler_node_decode_Generic_iff[OF decode, of q P2_RUN]
      q_decode
    by (simp add: p2_pre_def)
  have raw_cursor:
    "cursor rx =
       Some (abi_generic_list_item_ptr (sd_tcb_ptr D P2_RUN))"
    using cursor_q q_eq by simp
  show ?thesis
    by (rule that[OF raw]) (simp_all add: raw_ring p_eq raw_cursor)
qed

lemma p2_pre_delayed_a_raw_emptyE:
  assumes lists: "scheduler_lists_rel D R c p2_pre"
  obtains rx where
    "raw_xlist_rel
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (abi_list_ptr (sr_delayed_a R)) rx"
    "ring rx = []"
    "cursor rx = None"
proof -
  from lists have sched:
    "sched_xlist_rel (sd_node_decode D)
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (abi_list_ptr (sr_delayed_a R)) (sa_delayed_a p2_pre)"
    unfolding scheduler_lists_rel_def Let_def by blast
  have abs_ring: "ring (sa_delayed_a p2_pre) = []"
    by (simp add: p2_pre_def empty_node_ring_def)
  have abs_cursor: "cursor (sa_delayed_a p2_pre) = None"
    by (simp add: p2_pre_def empty_node_ring_def)
  from sched_xlist_rel_emptyE[OF sched abs_ring abs_cursor]
  obtain rx where
      raw: "raw_xlist_rel
        (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
        (abi_list_ptr (sr_delayed_a R)) rx"
    and ring: "ring rx = []"
    and cursor: "cursor rx = None" .
  show ?thesis by (rule that[OF raw ring cursor])
qed

lemma p2_pre_pending_raw_emptyE:
  assumes lists: "scheduler_lists_rel D R c p2_pre"
  obtains rx where
    "raw_xlist_rel
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (abi_list_ptr (sr_pending R)) rx"
    "ring rx = []"
    "cursor rx = None"
proof -
  from lists have sched:
    "sched_xlist_rel (sd_node_decode D)
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (abi_list_ptr (sr_pending R)) (sa_pending p2_pre)"
    unfolding scheduler_lists_rel_def Let_def by blast
  have abs_ring: "ring (sa_pending p2_pre) = []"
    by (simp add: p2_pre_def empty_node_ring_def)
  have abs_cursor: "cursor (sa_pending p2_pre) = None"
    by (simp add: p2_pre_def empty_node_ring_def)
  from sched_xlist_rel_emptyE[OF sched abs_ring abs_cursor]
  obtain rx where
      raw: "raw_xlist_rel
        (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
        (abi_list_ptr (sr_pending R)) rx"
    and ring: "ring rx = []"
    and cursor: "cursor rx = None" .
  show ?thesis by (rule that[OF raw ring cursor])
qed

theorem p2_pre_conditional_endpointI:
  assumes decode: "scheduler_decode_rel D p2_pre"
    and lists: "scheduler_lists_rel D R c p2_pre"
    and roles: "scheduler_role_rel R c p2_pre"
    and scalars: "scheduler_scalar_rel c p2_pre"
    and current: "scheduler_current_rel D c p2_pre"
    and boundary: "scheduler_boundary_rel c"
  shows "scheduler_endpoint_rel StableRunning D R c p2_pre"
proof -
  have core: "core_wf p2_pre"
    using p2_pre_settled settled_wf_imp_core_wf by blast
  have raw: "raw_scheduler_rel D R c p2_pre"
    by (rule raw_scheduler_relI[OF core decode lists roles scalars current boundary])
  show ?thesis using raw p2_pre_settled by simp
qed

theorem p2_post_conditional_endpointI:
  assumes decode: "scheduler_decode_rel D p2_post"
    and lists: "scheduler_lists_rel D R c p2_post"
    and roles: "scheduler_role_rel R c p2_post"
    and scalars: "scheduler_scalar_rel c p2_post"
    and current: "scheduler_current_rel D c p2_post"
    and boundary: "scheduler_boundary_rel c"
  shows
    "scheduler_endpoint_rel YieldPending D R c p2_post \<and>
     \<not> settled_wf p2_post"
proof -
  have raw: "raw_scheduler_rel D R c p2_post"
    by (rule raw_scheduler_relI[
          OF p2_post_core decode lists roles scalars current boundary])
  have pending: "yield_pending_wf p2_post"
    using p2_post_core
    by (simp add: yield_pending_wf_def p2_post_def empty_node_ring_def)
  show ?thesis using raw pending p2_post_not_settled by simp
qed

text \<open>
  These introduction rules deliberately stop before concrete non-vacuity.
  A later witness must construct two full TCBs, all eight roots, decoder laws,
  object separation, and every scalar equation rather than assuming them.
\<close>

end
