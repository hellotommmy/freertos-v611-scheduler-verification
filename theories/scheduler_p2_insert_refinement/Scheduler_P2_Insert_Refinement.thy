theory Scheduler_P2_Insert_Refinement
  imports
    "EAL6_FreeRTOS_V611_Scheduler_P2_Insert_Source.Scheduler_P2_Insert_Source"
    "EAL6_FreeRTOS_V611_List_Raw_R6_Ordered_Insert_Empty_Refinement.List_V611_Raw_R6_Ordered_Insert_Empty_Refinement"
begin

text \<open>
  Project the checked exact heap into the P2 delayed-list abstraction.  The
  source theorem remains scheduler-universe; only its already-normalised raw
  transformer is fed to the independently checked pure refinement theorem.
\<close>

lemma p2_remove_wake_insert_delayed_a_refines:
  fixes s :: Scheduler_V611_Parse.globals
  assumes decode: "scheduler_decode_rel D p2_pre"
    and lists: "scheduler_lists_rel D R s p2_pre"
    and footprint:
      "p2_source_footprint D R
        (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))"
  shows
    "sched_xlist_rel (sd_node_decode D)
       (raw_ordered_insert_empty_heap
         (p2_remove_then_wake_heap
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s)) D)
         (abi_list_ptr (sr_delayed_a R))
         (abi_generic_list_item_ptr (sd_tcb_ptr D P2_RUN)))
       (abi_list_ptr (sr_delayed_a R)) p2_run_delayed"
proof -
  let ?h0 = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s)"
  let ?hk = "p2_remove_then_wake_heap ?h0 D"
  let ?lp = "abi_list_ptr (sr_delayed_a R)"
  let ?rp = "abi_generic_list_item_ptr (sd_tcb_ptr D P2_RUN)"
  from p2_remove_then_wake_delayed_a_ordered_emptyE[
      OF decode lists footprint]
  obtain rx where
      rel: "raw_xlist_rel ?hk ?lp rx"
    and empty: "ring rx = []"
    and cursor: "cursor rx = None"
    and sentinel: "raw_sentinel_max ?hk ?lp"
    and fresh: "raw_fresh_for_insert ?lp (ring rx) ?rp"
    and key: "raw_key_at ?hk ?rp = 7" .
  let ?rx' =
    "list_insert_ordered_abs ?rp (raw_key_at ?hk ?rp) rx"
  have raw_post:
    "raw_xlist_rel (raw_ordered_insert_empty_heap ?hk ?lp ?rp)
      ?lp ?rx'"
    by (rule raw_ordered_insert_empty_transformer_refines[
          OF rel empty fresh])
  have raw_ring: "ring ?rx' = [?rp]"
    using empty by (simp add: list_insert_ordered_abs_def)
  have raw_cursor: "cursor ?rx' = None"
    using cursor by (simp add: list_insert_ordered_abs_def Let_def)
  have raw_key: "item_key ?rx' ?rp = 7"
    using key by (simp add: list_insert_ordered_abs_def Let_def)
  have decode_item:
    "sd_node_decode D ?rp = Some (Generic P2_RUN)"
    using scheduler_node_decode_Generic_iff[
        OF decode, of ?rp P2_RUN]
    by (simp add: p2_pre_def)
  have abstract_ring: "ring p2_run_delayed = [Generic P2_RUN]"
    by simp
  have abstract_cursor: "cursor p2_run_delayed = None"
    by simp
  have key_agreement:
    "item_key ?rx' ?rp =
     item_key p2_run_delayed (Generic P2_RUN)"
    using raw_key by simp
  show ?thesis
    apply (rule sched_xlist_rel_ordered_singletonI[
        where rx="?rx'" and p="?rp" and t=P2_RUN])
    apply (rule raw_post)
    apply (rule raw_ring)
    apply (rule raw_cursor)
    apply (rule abstract_ring)
    apply (rule abstract_cursor)
    apply (rule decode_item)
    apply (rule key_agreement)
    done
qed

theorem scheduler_vListInsert_p2_delayed_a_refines:
  fixes s0 s1 :: Scheduler_V611_Parse.globals
  assumes decode: "scheduler_decode_rel D p2_pre"
    and lists: "scheduler_lists_rel D R s0 p2_pre"
    and footprint:
      "p2_source_footprint D R
        (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s0))"
    and heap_entry:
      "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s1) =
       p2_remove_then_wake_heap
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s0)) D"
  shows
    "Scheduler_V611_Delay_Translation.vListInsert'
       (sr_delayed_a R)
       (scheduler_generic_item_ptr (sd_tcb_ptr D P2_RUN)) \<bullet> s1
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       sched_xlist_rel (sd_node_decode D)
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' t))
         (abi_list_ptr (sr_delayed_a R)) p2_run_delayed
     \<rbrace>"
proof -
  note heap_effect =
    scheduler_vListInsert_p2_delayed_a_after_remove_wake[
      OF decode lists footprint heap_entry]
  have relation_post:
    "sched_xlist_rel (sd_node_decode D)
       (raw_ordered_insert_empty_heap
         (p2_remove_then_wake_heap
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s0)) D)
         (abi_list_ptr (sr_delayed_a R))
         (abi_generic_list_item_ptr (sd_tcb_ptr D P2_RUN)))
       (abi_list_ptr (sr_delayed_a R)) p2_run_delayed"
    by (rule p2_remove_wake_insert_delayed_a_refines[
          OF decode lists footprint])
  show ?thesis
    apply (rule runs_to_weaken[OF heap_effect])
    using relation_post by auto
qed

end
