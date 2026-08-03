theory Scheduler_Resume_Generated_Top_Raised
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Generic_Unlinked.Scheduler_Resume_Generated_Generic_Unlinked"
begin

section \<open>Priority observation after both generated removes\<close>

lemma resume_pending_generic_remove_priority_frame:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
    and live: "u \<in> rpc_live C"
  shows
    "Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val (resume_pending_generic_remove_heap D t c)
         (sd_tcb_ptr D u)) =
     Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val (resume_pending_event_remove_heap D t c)
         (sd_tcb_ptr D u))"
proof -
  let ?hE = "resume_pending_event_remove_heap D t c"
  let ?owner = "rpc_generic_owner C t"
  let ?p = "resume_pending_generic_raw_ptr D t"
  let ?tp = "sd_tcb_ptr D u"
  have owner_entry:
    "scheduler_delay_owner_entry_rel ?hE (rpc_generic_roots C)
       generic_raw ?owner ?p"
    by (rule resume_pending_event_remove_generic_owner_frame[OF rel tasks])
  have owner: "?owner \<in> rpc_generic_roots C"
    using owner_entry by (simp add: scheduler_delay_owner_entry_rel_def)
  have member: "?p \<in> set (ring (generic_raw ?owner))"
    by (rule scheduler_delay_owner_entry_member[OF owner_entry])
  have bytes:
    "\<forall>address\<in>universal_priority_field_region ?tp.
       raw_remove_concrete_heap ?hE ?p address = ?hE address"
    by (rule scheduler_family_remove_priority_byte_frame[
      OF resume_pending_event_remove_generic_family_frame[OF rel tasks]
      owner member live])
  have field_same:
    "h_val (raw_remove_concrete_heap ?hE ?p)
       (universal_priority_field_ptr ?tp) =
     h_val ?hE (universal_priority_field_ptr ?tp)"
  proof (rule delay_h_val_region_cong)
    fix address
    assume "address \<in>
      {ptr_val (universal_priority_field_ptr ?tp)..+size_of TYPE(32 word)}"
    then show "raw_remove_concrete_heap ?hE ?p address = ?hE address"
      using bytes by (simp add: universal_priority_field_region_def)
  qed
  show ?thesis
    using field_same
    unfolding resume_pending_generic_remove_heap_def
      universal_priority_field_ptr_def
    by (simp only:
      Scheduler_V611_Parse.tskTaskControlBlock_C_h_val_fields(4))
qed

lemma resume_pending_two_removes_head_priorityD:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "unat (Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val (resume_pending_generic_remove_heap D t c)
         (sd_tcb_ptr D t))) = rpc_priority C t \<and>
     Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val (resume_pending_generic_remove_heap D t c)
         (sd_tcb_ptr D t)) < 4"
proof -
  have live: "t \<in> rpc_live C"
    by (rule resume_pending_gate_head_liveD[OF rel tasks])
  have original:
    "unat (Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
         (sd_tcb_ptr D t))) = rpc_priority C t \<and>
     rpc_priority C t < 4"
    using resume_pending_gate_head_owner_priorityD[OF rel tasks] by blast
  note event = resume_pending_event_remove_priority_frame[OF rel tasks live]
  note generic = resume_pending_generic_remove_priority_frame[OF rel tasks live]
  have unat_post:
    "unat (Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val (resume_pending_generic_remove_heap D t c)
         (sd_tcb_ptr D t))) = rpc_priority C t"
    using original event generic by simp
  have word_bound:
    "Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val (resume_pending_generic_remove_heap D t c)
         (sd_tcb_ptr D t)) < 4"
    using unat_post original
    by (simp add: word_less_nat_alt)
  show ?thesis using unat_post word_bound by simp
qed

section \<open>Exact generated top-priority conditional\<close>

definition resume_pending_generated_raise_top ::
  "'tid scheduler_decode \<Rightarrow> 'tid \<Rightarrow>
   (unit, Scheduler_V611_Parse.globals) res_monad"
where
  "resume_pending_generated_raise_top D t =
     condition
       (\<lambda>s. Scheduler_V611_Parse.globals.uxTopReadyPriority_' s <
         Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
           (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
             (sd_tcb_ptr D t)))
       (modify (\<lambda>s. s\<lparr>
         Scheduler_V611_Parse.globals.uxTopReadyPriority_' :=
           Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
             (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
               (sd_tcb_ptr D t))\<rparr>))
       skip"

definition resume_pending_top_raised_state ::
  "'tid scheduler_decode \<Rightarrow> 'tid \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> Scheduler_V611_Parse.globals"
where
  "resume_pending_top_raised_state D t c =
     (let base = scheduler_mem_state
         (resume_pending_generic_remove_heap D t c) c;
          priority = Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
            (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' base))
              (sd_tcb_ptr D t))
      in if Scheduler_V611_Parse.globals.uxTopReadyPriority_' base < priority
         then base\<lparr>Scheduler_V611_Parse.globals.uxTopReadyPriority_' :=
           priority\<rparr>
         else base)"

lemma resume_pending_generated_raise_top_exact:
  "resume_pending_generated_raise_top D t \<bullet>
     (scheduler_mem_state (resume_pending_generic_remove_heap D t c) c)
   \<lbrace>\<lambda>r s.
     r = Result () \<and> s = resume_pending_top_raised_state D t c
   \<rbrace>"
  unfolding resume_pending_generated_raise_top_def
    resume_pending_top_raised_state_def Let_def
  by runs_to_vcg

lemma resume_pending_top_raised_semantics:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "unat (Scheduler_V611_Parse.globals.uxTopReadyPriority_'
       (resume_pending_top_raised_state D t c)) =
       max (rpc_entry_top C) (rpc_priority C t) \<and>
     hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
       (resume_pending_top_raised_state D t c)) =
       resume_pending_generic_remove_heap D t c"
proof -
  have top_forward:
    "rpc_entry_top C =
       unat (Scheduler_V611_Parse.globals.uxTopReadyPriority_' c)"
    using rel
    unfolding resume_pending_gate_entry_rel_def Let_def
    by blast
  have top:
    "unat (Scheduler_V611_Parse.globals.uxTopReadyPriority_' c) =
       rpc_entry_top C"
    using top_forward by simp
  note priority = resume_pending_two_removes_head_priorityD[OF rel tasks]
  let ?base =
    "scheduler_mem_state (resume_pending_generic_remove_heap D t c) c"
  let ?top = "Scheduler_V611_Parse.globals.uxTopReadyPriority_' ?base"
  let ?priority =
    "Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
      (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' ?base))
        (sd_tcb_ptr D t))"
  have base_top:
    "Scheduler_V611_Parse.globals.uxTopReadyPriority_' ?base =
       Scheduler_V611_Parse.globals.uxTopReadyPriority_' c"
    by (simp add: scheduler_mem_state_def)
  have top_nat: "unat ?top = rpc_entry_top C"
    using top base_top by simp
  have priority_nat: "unat ?priority = rpc_priority C t"
    using priority by simp
  have compare:
    "(?top < ?priority) =
       (rpc_entry_top C < rpc_priority C t)"
    using top_nat priority_nat by (simp add: word_less_nat_alt)
  show ?thesis
    unfolding resume_pending_top_raised_state_def Let_def
    using top_nat priority_nat compare
    by (auto simp: max_def split: if_splits)
qed

lemma resume_pending_top_raised_phaseD:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "resume_pending_loop_phase_inv C S [] (t # rest) RP_TopRaised
       (resume_pending_raise_top_state C t
         (resume_pending_generic_unlink_state C t
           (resume_pending_event_unlink_state C t S)))"
  by (rule resume_pending_loop_phase_inv_top_step[
      OF resume_pending_generic_unlinked_phaseD[OF rel tasks]])

theorem resume_pending_generated_top_raised_cutpoint:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "bind
       (Scheduler_V611_Delay_Translation.vListRemove'
         (scheduler_event_item_ptr (sd_tcb_ptr D t)))
       (\<lambda>_. bind
         (Scheduler_V611_Delay_Translation.vListRemove'
           (scheduler_generic_item_ptr (sd_tcb_ptr D t)))
         (\<lambda>_. resume_pending_generated_raise_top D t)) \<bullet> c
     \<lbrace>\<lambda>r s.
       r = Result () \<and>
       s = resume_pending_top_raised_state D t c \<and>
       unat (Scheduler_V611_Parse.globals.uxTopReadyPriority_' s) =
         rps_top (resume_pending_raise_top_state C t
           (resume_pending_generic_unlink_state C t
             (resume_pending_event_unlink_state C t S))) \<and>
       scheduler_family_pre_rel
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
         (rpc_generic_roots C)
         (resume_pending_generic_raw_after C D t generic_raw)
         (rpc_live C) D \<and>
       scheduler_event_root_family_rel D
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
         (rpc_event_roots C) (rpc_pending_root C)
         (resume_pending_event_raw_after C D t event_raw)
         (rps_event_family (resume_pending_event_unlink_state C t S))
         (rpc_live C) (rpc_K_E C) \<and>
       resume_pending_loop_phase_inv C S [] (t # rest) RP_TopRaised
         (resume_pending_raise_top_state C t
           (resume_pending_generic_unlink_state C t
             (resume_pending_event_unlink_state C t S)))
     \<rbrace>"
proof -
  note event_source =
    resume_pending_generated_event_unlinked_cutpoint[OF rel tasks]
  note generic_source =
    resume_pending_generic_remove_generated_after_event[OF rel tasks]
  note top = resume_pending_generated_raise_top_exact[
    where D=D and t=t and c=c]
  have source:
    "bind
       (Scheduler_V611_Delay_Translation.vListRemove'
         (scheduler_event_item_ptr (sd_tcb_ptr D t)))
       (\<lambda>_. bind
         (Scheduler_V611_Delay_Translation.vListRemove'
           (scheduler_generic_item_ptr (sd_tcb_ptr D t)))
         (\<lambda>_. resume_pending_generated_raise_top D t)) \<bullet> c
     \<lbrace>\<lambda>r s.
       r = Result () \<and> s = resume_pending_top_raised_state D t c
     \<rbrace>"
  proof -
    show ?thesis
      apply (rule runs_to_bind)
      apply (rule runs_to_weaken[OF event_source])
       apply clarsimp
      apply (rule runs_to_bind)
      apply (rule runs_to_weaken[OF generic_source])
       apply clarsimp
      apply (rule runs_to_weaken[OF top])
      by simp_all
  qed
  note generic = resume_pending_generic_remove_family_post[OF rel tasks]
  note event = resume_pending_generic_remove_event_family_frame[OF rel tasks]
  note semantics = resume_pending_top_raised_semantics[OF rel tasks]
  note phase = resume_pending_top_raised_phaseD[OF rel tasks]
  have entry_top: "rps_top S = rpc_entry_top C"
    using resume_pending_gate_pure_entryD[OF rel]
    by (simp add: resume_pending_entry_rel_def)
  show ?thesis
    apply (rule runs_to_weaken[OF source])
    using generic event semantics phase entry_top
    by (auto simp: scheduler_node_kind_family_remove_post_def Let_def
        resume_pending_generic_raw_after_def
        resume_pending_raise_top_state_def
        resume_pending_generic_unlink_state_def
        resume_pending_event_unlink_state_def)
qed

end
