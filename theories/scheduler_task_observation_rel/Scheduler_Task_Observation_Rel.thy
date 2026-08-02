theory Scheduler_Task_Observation_Rel
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Outer_Scaffold.Scheduler_Resume_Outer_Scaffold"
    "EAL6_FreeRTOS_V611_Scheduler_Universal_Geometry.Scheduler_Universal_Geometry"
    "EAL6_FreeRTOS_V611_Scheduler_Remove_Unlinked_Ownership.Scheduler_Remove_Unlinked_Ownership"
begin

text \<open>
  Universal task observations missing from raw_xlist_rel.  The relation is
  indexed by an arbitrary finite live set through the scheduler state.  The
  proof configuration's priority bound is the source constant 4, but no task
  is assigned a particular priority.
\<close>

definition TaskObservationRel ::
  "'tid scheduler_decode \<Rightarrow> heap_mem \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> bool"
where
  "TaskObservationRel D h a \<longleftrightarrow>
     finite (sa_live a) \<and>
     (\<forall>t \<in> sa_live a.
       c_guard (sd_tcb_ptr D t) \<and>
       c_guard (scheduler_generic_item_ptr (sd_tcb_ptr D t)) \<and>
       c_guard (scheduler_event_item_ptr (sd_tcb_ptr D t)) \<and>
       sa_priority a t < 4 \<and>
       unat (Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
         (h_val h (sd_tcb_ptr D t))) = sa_priority a t \<and>
       Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
         (h_val h (sd_tcb_ptr D t)) < 4 \<and>
       Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
         (h_val h (scheduler_generic_item_ptr (sd_tcb_ptr D t))) =
           PTR_COERCE(Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow> unit)
             (sd_tcb_ptr D t) \<and>
       Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
         (h_val h (scheduler_event_item_ptr (sd_tcb_ptr D t))) =
           PTR_COERCE(Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow> unit)
             (sd_tcb_ptr D t))"

lemma TaskObservationRel_liveD:
  assumes obs: "TaskObservationRel D h a"
    and live: "t \<in> sa_live a"
  shows
    "c_guard (sd_tcb_ptr D t) \<and>
     c_guard (scheduler_generic_item_ptr (sd_tcb_ptr D t)) \<and>
     c_guard (scheduler_event_item_ptr (sd_tcb_ptr D t)) \<and>
     sa_priority a t < 4 \<and>
     unat (Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val h (sd_tcb_ptr D t))) = sa_priority a t \<and>
     Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val h (sd_tcb_ptr D t)) < 4 \<and>
     Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val h (scheduler_generic_item_ptr (sd_tcb_ptr D t))) =
         PTR_COERCE(Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow> unit)
           (sd_tcb_ptr D t) \<and>
     Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val h (scheduler_event_item_ptr (sd_tcb_ptr D t))) =
         PTR_COERCE(Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow> unit)
           (sd_tcb_ptr D t)"
  using obs live by (auto simp: TaskObservationRel_def)

text \<open>
  The scheduler-owned pending list is only one possible owner of an Event
  item.  A blocked task may instead be owned by an application event list,
  whose root is deliberately absent from scheduler_roots.  The arbitrary
  function E supplies those external roots as ghost representation data; it
  does not fix a task, priority, root address, or list shape.

  None is the operational Unlinked phase.  This is the phase reached after
  removing a pending Event item and retained while the same TCB's Generic
  item is removed and inserted into a ready list.
\<close>

definition scheduler_event_expected_container ::
  "scheduler_roots \<Rightarrow>
   ('tid \<Rightarrow> Scheduler_V611_Parse.xLIST_C ptr) \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> 'tid \<Rightarrow>
   Scheduler_V611_Parse.xLIST_C ptr option"
where
  "scheduler_event_expected_container R E a t =
     (if t \<in> event_task_set (sa_pending a)
      then Some (sr_pending R)
      else if t \<in> sa_event_waiting a
      then Some (E t)
      else None)"

definition SchedulerEventRoleWF :: "'tid scheduler_abs \<Rightarrow> bool" where
  "SchedulerEventRoleWF a \<longleftrightarrow>
     event_task_set (sa_pending a) \<subseteq> sa_live a \<and>
     sa_event_waiting a \<subseteq> sa_live a \<and>
     event_task_set (sa_pending a) \<inter> sa_event_waiting a = {}"

definition TaskEventContainerRel ::
  "'tid scheduler_decode \<Rightarrow> scheduler_roots \<Rightarrow>
   ('tid \<Rightarrow> Scheduler_V611_Parse.xLIST_C ptr) \<Rightarrow>
   heap_mem \<Rightarrow> 'tid scheduler_abs \<Rightarrow> bool"
where
  "TaskEventContainerRel D R E h a \<longleftrightarrow>
     SchedulerEventRoleWF a \<and>
     (\<forall>t \<in> sa_live a.
       case scheduler_event_expected_container R E a t of
         None \<Rightarrow>
           Scheduler_V611_Parse.xLIST_ITEM_C.pvContainer_C
             (h_val h (scheduler_event_item_ptr (sd_tcb_ptr D t))) = NULL
       | Some lp \<Rightarrow>
           c_guard lp \<and>
           Scheduler_V611_Parse.xLIST_ITEM_C.pvContainer_C
             (h_val h (scheduler_event_item_ptr (sd_tcb_ptr D t))) =
               PTR_COERCE(Scheduler_V611_Parse.xLIST_C \<rightarrow> unit) lp)"

lemma core_wf_SchedulerEventRoleWF:
  assumes core: "core_wf a"
  shows "SchedulerEventRoleWF a"
  using core
  by (auto simp: core_wf_def membership_wf_def SchedulerEventRoleWF_def
      Let_def)

lemma TaskEventContainerRel_role_wfD:
  assumes rel: "TaskEventContainerRel D R E h a"
  shows "SchedulerEventRoleWF a"
  using rel by (simp add: TaskEventContainerRel_def)

lemma TaskEventContainerRel_pendingD:
  assumes rel: "TaskEventContainerRel D R E h a"
    and live: "t \<in> sa_live a"
    and pending: "t \<in> event_task_set (sa_pending a)"
  shows
    "c_guard (sr_pending R) \<and>
     Scheduler_V611_Parse.xLIST_ITEM_C.pvContainer_C
       (h_val h (scheduler_event_item_ptr (sd_tcb_ptr D t))) =
       PTR_COERCE(Scheduler_V611_Parse.xLIST_C \<rightarrow> unit) (sr_pending R)"
  using rel live pending
  by (auto simp: TaskEventContainerRel_def
      scheduler_event_expected_container_def)

lemma TaskEventContainerRel_waitingD:
  assumes rel: "TaskEventContainerRel D R E h a"
    and live: "t \<in> sa_live a"
    and waiting: "t \<in> sa_event_waiting a"
  shows
    "c_guard (E t) \<and>
     Scheduler_V611_Parse.xLIST_ITEM_C.pvContainer_C
       (h_val h (scheduler_event_item_ptr (sd_tcb_ptr D t))) =
       PTR_COERCE(Scheduler_V611_Parse.xLIST_C \<rightarrow> unit) (E t)"
proof -
  have not_pending: "t \<notin> event_task_set (sa_pending a)"
    using TaskEventContainerRel_role_wfD[OF rel] waiting
    by (auto simp: SchedulerEventRoleWF_def)
  show ?thesis
    using rel live waiting not_pending
    by (auto simp: TaskEventContainerRel_def
        scheduler_event_expected_container_def)
qed

lemma TaskEventContainerRel_unlinkedD:
  assumes rel: "TaskEventContainerRel D R E h a"
    and live: "t \<in> sa_live a"
    and not_pending: "t \<notin> event_task_set (sa_pending a)"
    and not_waiting: "t \<notin> sa_event_waiting a"
  shows
    "Scheduler_V611_Parse.xLIST_ITEM_C.pvContainer_C
       (h_val h (scheduler_event_item_ptr (sd_tcb_ptr D t))) = NULL"
  using rel live not_pending not_waiting
  by (auto simp: TaskEventContainerRel_def
      scheduler_event_expected_container_def)

definition scheduler_list_head_item ::
  "heap_mem \<Rightarrow> Scheduler_V611_Parse.xLIST_C ptr \<Rightarrow>
   Scheduler_V611_Parse.xLIST_ITEM_C ptr"
where
  "scheduler_list_head_item h lp =
     Scheduler_V611_Parse.xMINI_LIST_ITEM_C.pxNext_C
       (Scheduler_V611_Parse.xLIST_C.xListEnd_C (h_val h lp))"

lemma sched_xlist_rel_head_decode:
  assumes rel: "sched_xlist_rel decode h (abi_list_ptr lp) q"
    and nonempty: "ring q = n # ns"
  shows
    "decode (abi_item_ptr (scheduler_list_head_item h lp)) = Some n"
proof -
  from rel obtain rx where
      raw: "raw_xlist_rel h (abi_list_ptr lp) rx"
    and relabel: "xlist_relabel decode rx q"
    by (auto simp: sched_xlist_rel_def)
  from relabel have pairs:
    "list_all2 (\<lambda>p node. decode p = Some node) (ring rx) (ring q)"
    by (simp add: xlist_relabel_def)
  from pairs nonempty obtain p ps where
      raw_ring: "ring rx = p # ps"
    and decoded: "decode p = Some n"
    by (cases "ring rx") auto
  have links: "raw_ring_links h (abi_list_ptr lp) (ring rx)"
    using raw by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have raw_head:
    "List_V611_Raw_Skip_Translation.xMINI_LIST_ITEM_C.pxNext_C
       (List_V611_Raw_Skip_Translation.xLIST_C.xListEnd_C
         (h_val h (abi_list_ptr lp))) = p"
    using links raw_ring
    by (simp add: raw_ring_links_def raw_edge_pairs_def raw_next_at_def
        raw_prev_at_def raw_end_item_def)
  have abi_head:
    "List_V611_Raw_Skip_Translation.xMINI_LIST_ITEM_C.pxNext_C
       (List_V611_Raw_Skip_Translation.xLIST_C.xListEnd_C
         (h_val h (abi_list_ptr lp))) =
     abi_item_ptr (scheduler_list_head_item h lp)"
    by (simp add: scheduler_list_head_item_def abi_sentinel_next_h_val)
  show ?thesis using decoded raw_head abi_head by simp
qed

lemma sched_xlist_rel_event_head_ptr:
  assumes lists: "sched_xlist_rel (sd_node_decode D) h (abi_list_ptr lp) q"
    and decode: "scheduler_decode_rel D a"
    and head: "ring q = Event t # ns"
  shows
    "scheduler_list_head_item h lp =
       scheduler_event_item_ptr (sd_tcb_ptr D t)"
proof -
  have decoded:
    "sd_node_decode D (abi_item_ptr (scheduler_list_head_item h lp)) =
       Some (Event t)"
    by (rule sched_xlist_rel_head_decode[OF lists head])
  have raw_eq:
    "abi_item_ptr (scheduler_list_head_item h lp) =
       abi_event_list_item_ptr (sd_tcb_ptr D t)"
    using scheduler_node_decode_Event_iff[OF decode, where
      p="abi_item_ptr (scheduler_list_head_item h lp)" and t=t]
      decoded by blast
  have coerced:
    "abi_item_ptr (scheduler_list_head_item h lp) =
       abi_item_ptr (scheduler_event_item_ptr (sd_tcb_ptr D t))"
    using raw_eq by simp
  show ?thesis using coerced by (rule iffD1[OF abi_item_ptr_eq_iff])
qed

lemma sched_xlist_rel_generic_head_ptr:
  assumes lists: "sched_xlist_rel (sd_node_decode D) h (abi_list_ptr lp) q"
    and decode: "scheduler_decode_rel D a"
    and head: "ring q = Generic t # ns"
  shows
    "scheduler_list_head_item h lp =
       scheduler_generic_item_ptr (sd_tcb_ptr D t)"
proof -
  have decoded:
    "sd_node_decode D (abi_item_ptr (scheduler_list_head_item h lp)) =
       Some (Generic t)"
    by (rule sched_xlist_rel_head_decode[OF lists head])
  have raw_eq:
    "abi_item_ptr (scheduler_list_head_item h lp) =
       abi_generic_list_item_ptr (sd_tcb_ptr D t)"
    using scheduler_node_decode_Generic_iff[OF decode, where
      p="abi_item_ptr (scheduler_list_head_item h lp)" and t=t]
      decoded by blast
  have coerced:
    "abi_item_ptr (scheduler_list_head_item h lp) =
       abi_item_ptr (scheduler_generic_item_ptr (sd_tcb_ptr D t))"
    using raw_eq by simp
  show ?thesis using coerced by (rule iffD1[OF abi_item_ptr_eq_iff])
qed

theorem represented_event_head_owner_priority:
  assumes lists: "sched_xlist_rel (sd_node_decode D) h (abi_list_ptr lp) q"
    and decode: "scheduler_decode_rel D a"
    and obs: "TaskObservationRel D h a"
    and head: "ring q = Event t # ns"
  shows
    "scheduler_list_head_item h lp =
       scheduler_event_item_ptr (sd_tcb_ptr D t) \<and>
     Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val h (scheduler_list_head_item h lp)) =
         PTR_COERCE(Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow> unit)
           (sd_tcb_ptr D t) \<and>
     unat (Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val h (sd_tcb_ptr D t))) = sa_priority a t \<and>
     sa_priority a t < 4"
proof -
  have ptr: "scheduler_list_head_item h lp =
      scheduler_event_item_ptr (sd_tcb_ptr D t)"
    by (rule sched_xlist_rel_event_head_ptr[OF lists decode head])
  have decoded:
    "sd_node_decode D (abi_item_ptr (scheduler_list_head_item h lp)) =
       Some (Event t)"
    by (rule sched_xlist_rel_head_decode[OF lists head])
  have live: "t \<in> sa_live a"
    using scheduler_node_decode_Event_iff[
      OF decode,
      where p="abi_item_ptr (scheduler_list_head_item h lp)" and t=t]
      decoded by blast
  note fields = TaskObservationRel_liveD[OF obs live]
  show ?thesis using ptr fields by simp
qed

theorem represented_generic_head_owner_priority:
  assumes lists: "sched_xlist_rel (sd_node_decode D) h (abi_list_ptr lp) q"
    and decode: "scheduler_decode_rel D a"
    and obs: "TaskObservationRel D h a"
    and head: "ring q = Generic t # ns"
  shows
    "scheduler_list_head_item h lp =
       scheduler_generic_item_ptr (sd_tcb_ptr D t) \<and>
     Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val h (scheduler_list_head_item h lp)) =
         PTR_COERCE(Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow> unit)
           (sd_tcb_ptr D t) \<and>
     unat (Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val h (sd_tcb_ptr D t))) = sa_priority a t \<and>
     sa_priority a t < 4"
proof -
  have ptr: "scheduler_list_head_item h lp =
      scheduler_generic_item_ptr (sd_tcb_ptr D t)"
    by (rule sched_xlist_rel_generic_head_ptr[OF lists decode head])
  have decoded:
    "sd_node_decode D (abi_item_ptr (scheduler_list_head_item h lp)) =
       Some (Generic t)"
    by (rule sched_xlist_rel_head_decode[OF lists head])
  have live: "t \<in> sa_live a"
    using scheduler_node_decode_Generic_iff[
      OF decode,
      where p="abi_item_ptr (scheduler_list_head_item h lp)" and t=t]
      decoded by blast
  note fields = TaskObservationRel_liveD[OF obs live]
  show ?thesis using ptr fields by simp
qed

text \<open>
  Footprint bricks.  A list link/container write is a whole embedded-item
  update whose new value preserves pvOwner; a list count/index write is a
  whole list-root update disjoint from the TCB.  These lemmas prove owner and
  priority observations survive those exact classes of writes.
\<close>

lemma scheduler_event_item_whole_write_to_tcb:
  assumes guard: "c_guard tp"
  shows
    "heap_update (scheduler_event_item_ptr tp) v h =
     heap_update tp
       (Scheduler_V611_Parse.tskTaskControlBlock_C.xEventListItem_C_update
         (\<lambda>_. v) (h_val h tp)) h"
  unfolding scheduler_event_item_ptr_def
  by (rule Scheduler_V611_Parse.tskTaskControlBlock_C_heap_update_fields(3)[
        OF guard])

lemma scheduler_generic_item_h_val:
  "h_val h (scheduler_generic_item_ptr tp) =
   Scheduler_V611_Parse.tskTaskControlBlock_C.xGenericListItem_C
     (h_val h tp)"
  unfolding scheduler_generic_item_ptr_def
  by (rule Scheduler_V611_Parse.tskTaskControlBlock_C_h_val_fields(2))

lemma scheduler_event_item_h_val:
  "h_val h (scheduler_event_item_ptr tp) =
   Scheduler_V611_Parse.tskTaskControlBlock_C.xEventListItem_C
     (h_val h tp)"
  unfolding scheduler_event_item_ptr_def
  by (rule Scheduler_V611_Parse.tskTaskControlBlock_C_h_val_fields(3))

lemma scheduler_generic_item_write_observation_frame:
  assumes guard: "c_guard tp"
    and owner:
      "Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C v =
       Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
         (h_val h (scheduler_generic_item_ptr tp))"
  shows
    "Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val (heap_update (scheduler_generic_item_ptr tp) v h) tp) =
       Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C (h_val h tp) \<and>
     Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val (heap_update (scheduler_generic_item_ptr tp) v h)
         (scheduler_generic_item_ptr tp)) =
       Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
         (h_val h (scheduler_generic_item_ptr tp))"
proof -
  have whole:
    "heap_update (scheduler_generic_item_ptr tp) v h =
     heap_update tp
       (Scheduler_V611_Parse.tskTaskControlBlock_C.xGenericListItem_C_update
         (\<lambda>_. v) (h_val h tp)) h"
    by (rule scheduler_generic_item_whole_write_to_tcb[OF guard])
  have tcb_after:
    "h_val (heap_update (scheduler_generic_item_ptr tp) v h) tp =
     Scheduler_V611_Parse.tskTaskControlBlock_C.xGenericListItem_C_update
       (\<lambda>_. v) (h_val h tp)"
    using whole guard by (simp add: h_val_heap_update)
  have priority:
    "Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val (heap_update (scheduler_generic_item_ptr tp) v h) tp) =
     Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C (h_val h tp)"
    using tcb_after by simp
  have written:
    "h_val (heap_update (scheduler_generic_item_ptr tp) v h)
       (scheduler_generic_item_ptr tp) = v"
    using scheduler_generic_item_h_val[
      where h="heap_update (scheduler_generic_item_ptr tp) v h" and tp=tp]
      tcb_after by simp
  show ?thesis using priority written owner by simp
qed

lemma scheduler_generic_item_write_sibling_event_frame:
  assumes guard: "c_guard tp"
  shows
    "h_val (heap_update (scheduler_generic_item_ptr tp) v h)
       (scheduler_event_item_ptr tp) =
       h_val h (scheduler_event_item_ptr tp) \<and>
     Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val (heap_update (scheduler_generic_item_ptr tp) v h) tp) =
       Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C (h_val h tp)"
proof -
  have whole:
    "heap_update (scheduler_generic_item_ptr tp) v h =
     heap_update tp
       (Scheduler_V611_Parse.tskTaskControlBlock_C.xGenericListItem_C_update
         (\<lambda>_. v) (h_val h tp)) h"
    by (rule scheduler_generic_item_whole_write_to_tcb[OF guard])
  have tcb_after:
    "h_val (heap_update (scheduler_generic_item_ptr tp) v h) tp =
     Scheduler_V611_Parse.tskTaskControlBlock_C.xGenericListItem_C_update
       (\<lambda>_. v) (h_val h tp)"
    using whole guard by (simp add: h_val_heap_update)
  have event:
    "h_val (heap_update (scheduler_generic_item_ptr tp) v h)
       (scheduler_event_item_ptr tp) =
     h_val h (scheduler_event_item_ptr tp)"
    using scheduler_event_item_h_val[
      where h="heap_update (scheduler_generic_item_ptr tp) v h" and tp=tp]
      scheduler_event_item_h_val[where h=h and tp=tp] tcb_after
    by simp
  have priority:
    "Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val (heap_update (scheduler_generic_item_ptr tp) v h) tp) =
     Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C (h_val h tp)"
    using tcb_after by simp
  show ?thesis using event priority by simp
qed

corollary scheduler_generic_item_write_preserves_event_container:
  assumes guard: "c_guard tp"
  shows
    "Scheduler_V611_Parse.xLIST_ITEM_C.pvContainer_C
       (h_val (heap_update (scheduler_generic_item_ptr tp) v h)
         (scheduler_event_item_ptr tp)) =
     Scheduler_V611_Parse.xLIST_ITEM_C.pvContainer_C
       (h_val h (scheduler_event_item_ptr tp))"
  using scheduler_generic_item_write_sibling_event_frame[OF guard,
      where v=v and h=h]
  by simp

corollary scheduler_generic_item_write_preserves_event_unlinked:
  assumes guard: "c_guard tp"
    and unlinked:
      "Scheduler_V611_Parse.xLIST_ITEM_C.pvContainer_C
         (h_val h (scheduler_event_item_ptr tp)) = NULL"
  shows
    "Scheduler_V611_Parse.xLIST_ITEM_C.pvContainer_C
       (h_val (heap_update (scheduler_generic_item_ptr tp) v h)
         (scheduler_event_item_ptr tp)) = NULL"
  using scheduler_generic_item_write_preserves_event_container[OF guard,
      where v=v and h=h] unlinked by simp

lemma scheduler_event_item_write_observation_frame:
  assumes guard: "c_guard tp"
    and owner:
      "Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C v =
       Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
         (h_val h (scheduler_event_item_ptr tp))"
  shows
    "Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val (heap_update (scheduler_event_item_ptr tp) v h) tp) =
       Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C (h_val h tp) \<and>
     Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val (heap_update (scheduler_event_item_ptr tp) v h)
         (scheduler_event_item_ptr tp)) =
       Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
         (h_val h (scheduler_event_item_ptr tp))"
proof -
  have whole:
    "heap_update (scheduler_event_item_ptr tp) v h =
     heap_update tp
       (Scheduler_V611_Parse.tskTaskControlBlock_C.xEventListItem_C_update
         (\<lambda>_. v) (h_val h tp)) h"
    by (rule scheduler_event_item_whole_write_to_tcb[OF guard])
  have tcb_after:
    "h_val (heap_update (scheduler_event_item_ptr tp) v h) tp =
     Scheduler_V611_Parse.tskTaskControlBlock_C.xEventListItem_C_update
       (\<lambda>_. v) (h_val h tp)"
    using whole guard by (simp add: h_val_heap_update)
  have priority:
    "Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val (heap_update (scheduler_event_item_ptr tp) v h) tp) =
     Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C (h_val h tp)"
    using tcb_after by simp
  have written:
    "h_val (heap_update (scheduler_event_item_ptr tp) v h)
       (scheduler_event_item_ptr tp) = v"
    using scheduler_event_item_h_val[
      where h="heap_update (scheduler_event_item_ptr tp) v h" and tp=tp]
      tcb_after by simp
  show ?thesis using priority written owner by simp
qed

lemma scheduler_event_item_write_sibling_generic_frame:
  assumes guard: "c_guard tp"
  shows
    "h_val (heap_update (scheduler_event_item_ptr tp) v h)
       (scheduler_generic_item_ptr tp) =
       h_val h (scheduler_generic_item_ptr tp) \<and>
     Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val (heap_update (scheduler_event_item_ptr tp) v h) tp) =
       Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C (h_val h tp)"
proof -
  have whole:
    "heap_update (scheduler_event_item_ptr tp) v h =
     heap_update tp
       (Scheduler_V611_Parse.tskTaskControlBlock_C.xEventListItem_C_update
         (\<lambda>_. v) (h_val h tp)) h"
    by (rule scheduler_event_item_whole_write_to_tcb[OF guard])
  have tcb_after:
    "h_val (heap_update (scheduler_event_item_ptr tp) v h) tp =
     Scheduler_V611_Parse.tskTaskControlBlock_C.xEventListItem_C_update
       (\<lambda>_. v) (h_val h tp)"
    using whole guard by (simp add: h_val_heap_update)
  have generic:
    "h_val (heap_update (scheduler_event_item_ptr tp) v h)
       (scheduler_generic_item_ptr tp) =
     h_val h (scheduler_generic_item_ptr tp)"
    using scheduler_generic_item_h_val[
      where h="heap_update (scheduler_event_item_ptr tp) v h" and tp=tp]
      scheduler_generic_item_h_val[where h=h and tp=tp] tcb_after
    by simp
  have priority:
    "Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val (heap_update (scheduler_event_item_ptr tp) v h) tp) =
     Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C (h_val h tp)"
    using tcb_after by simp
  show ?thesis using generic priority by simp
qed

lemma scheduler_list_root_write_observation_frame:
  assumes disjoint:
    "scheduler_list_region lp \<inter> universal_tcb_region tp = {}"
  shows
    "h_val (heap_update lp (v :: Scheduler_V611_Parse.xLIST_C) h) tp =
       h_val h tp"
proof -
  have byte_disjoint:
    "{ptr_val lp..+
       length (to_bytes v
         (heap_list h
           (size_of TYPE(Scheduler_V611_Parse.xLIST_C)) (ptr_val lp)))} \<inter>
     {ptr_val tp..+
       size_of TYPE(Scheduler_V611_Parse.tskTaskControlBlock_C)} = {}"
    using disjoint
    by (simp add: scheduler_list_region_def universal_tcb_region_def)
  have heap_lists_same:
    "heap_list
       (heap_update_list (ptr_val lp)
         (to_bytes v
           (heap_list h
             (size_of TYPE(Scheduler_V611_Parse.xLIST_C)) (ptr_val lp))) h)
       (size_of TYPE(Scheduler_V611_Parse.tskTaskControlBlock_C))
       (ptr_val tp) =
     heap_list h
       (size_of TYPE(Scheduler_V611_Parse.tskTaskControlBlock_C))
       (ptr_val tp)"
    by (rule heap_list_update_disjoint_same[OF byte_disjoint])
  show ?thesis
    unfolding h_val_def heap_update_def
    using heap_lists_same by simp
qed

lemma raw_remove_concrete_heap_removed_owner_frame:
  assumes rel: "raw_xlist_rel h lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
       (h_val (raw_remove_concrete_heap h p) p) =
     List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C (h_val h p)"
proof -
  let ?hu = "raw_source_unlink_two h p"
  let ?hi = "raw_remove_index_heap ?hu lp p"
  let ?hc = "raw_remove_container_heap ?hi p"
  have layout: "raw_xlist_layout lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def)
  have p_guard: "c_guard p"
    using layout member by (auto simp: raw_xlist_layout_def)
  have item_list: "raw_item_region p \<inter> raw_list_region lp = {}"
    using layout member by (auto simp: raw_xlist_layout_def)
  have unlink_same: "h_val ?hu p = h_val h p"
    by (rule raw_source_unlink_two_item_same[OF rel member])
  have index_same: "h_val ?hi p = h_val ?hu p"
  proof (cases "List_V611_Raw_Skip_Translation.xLIST_C.pxIndex_C
      (h_val ?hu lp) = p")
    case True
    show ?thesis
      unfolding raw_remove_index_heap_def
      apply (simp only: if_P[OF True])
      by (rule
        List_V611_Raw_R6_Remove_Topology_Effect.raw_list_update_preserves_disjoint_item[
          OF item_list])
  next
    case False
    show ?thesis
      unfolding raw_remove_index_heap_def by (simp only: if_not_P[OF False])
  qed
  have container_owner:
    "List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
       (h_val ?hc p) =
     List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
       (h_val ?hi p)"
    unfolding raw_remove_container_heap_def
    using p_guard by (simp add: h_val_heap_update)
  have count_same:
    "h_val (raw_remove_count_heap ?hc lp) p = h_val ?hc p"
    unfolding raw_remove_count_heap_def
    by (rule
      List_V611_Raw_R6_Remove_Topology_Effect.raw_list_update_preserves_disjoint_item[
        OF item_list])
  have concrete:
    "raw_remove_concrete_heap h p = raw_remove_source_heap h lp p"
    by (rule raw_remove_concrete_heap_eq[OF rel member])
  show ?thesis
    using concrete unlink_same index_same container_owner count_same
    by (simp add: raw_remove_source_heap_def raw_remove_suffix_heap_def)
qed

lemma raw_remove_event_item_establishes_unlinked_owner_frame:
  assumes rel: "raw_xlist_rel h lp xs"
    and member:
      "abi_event_list_item_ptr tp \<in> set (ring xs)"
  shows
    "Scheduler_V611_Parse.xLIST_ITEM_C.pvContainer_C
       (h_val
         (raw_remove_concrete_heap h (abi_event_list_item_ptr tp))
         (scheduler_event_item_ptr tp)) = NULL \<and>
     Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val
         (raw_remove_concrete_heap h (abi_event_list_item_ptr tp))
         (scheduler_event_item_ptr tp)) =
       Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
         (h_val h (scheduler_event_item_ptr tp))"
proof -
  have unlinked:
    "raw_remove_unlinked_effect h
       (raw_remove_concrete_heap h (abi_event_list_item_ptr tp))
       lp xs (abi_event_list_item_ptr tp)"
    by (rule raw_remove_concrete_heap_unlinked_effect[OF rel member])
  have owner:
    "List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
       (h_val
         (raw_remove_concrete_heap h (abi_event_list_item_ptr tp))
         (abi_event_list_item_ptr tp)) =
     List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
       (h_val h (abi_event_list_item_ptr tp))"
    by (rule raw_remove_concrete_heap_removed_owner_frame[OF rel member])
  show ?thesis
    using unlinked owner
    by (simp add: raw_remove_unlinked_effect_def abi_item_container_h_val
        abi_item_owner_h_val abi_event_list_item_ptr_def
        scheduler_event_item_ptr_def)
qed

end
