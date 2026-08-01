theory Scheduler_P2_Delay_Refinement
  imports
    "EAL6_FreeRTOS_V611_Scheduler_P2_Delay_Source.Scheduler_P2_Delay_Source"
    "EAL6_FreeRTOS_V611_Scheduler_P2_Post_Relation.Scheduler_P2_Post_Relation"
begin

text \<open>
  Final assembly layer for the positive-delay P2 path.  The operational
  theorem and the pure heap relation remain separate parents.  This first
  result closes every non-list component of the requested post endpoint.
\<close>

lemma p2_final_nonlist_relations:
  fixes c :: Scheduler_V611_Parse.globals
  assumes endpoint:
      "scheduler_endpoint_rel StableRunning D R c p2_pre"
  shows
    "scheduler_decode_rel D p2_post \<and>
     scheduler_role_rel R (p2_delay_2_source_state c D R) p2_post \<and>
     scheduler_scalar_rel (p2_delay_2_source_state c D R) p2_post \<and>
     scheduler_current_rel D (p2_delay_2_source_state c D R) p2_post \<and>
     scheduler_boundary_rel (p2_delay_2_source_state c D R)"
proof -
  have raw: "raw_scheduler_rel D R c p2_pre"
    using endpoint by simp
  have decode0: "scheduler_decode_rel D p2_pre"
    and roles0: "scheduler_role_rel R c p2_pre"
    and scalars0: "scheduler_scalar_rel c p2_pre"
    and current0: "scheduler_current_rel D c p2_pre"
    and boundary0: "scheduler_boundary_rel c"
    using raw by (auto simp: raw_scheduler_rel_def)

  have decode1: "scheduler_decode_rel D p2_post"
    using decode0
    by (simp add: scheduler_decode_rel_def p2_pre_def p2_post_def)

  have roles1:
      "scheduler_role_rel R
        (p2_delay_2_source_state c D R) p2_post"
    using roles0
    by (simp add: scheduler_role_rel_def
        p2_delay_2_source_state_def p2_yield_state_def
        p2_resume_quiet_state_def scheduler_mem_state_def
        p2_suspend_state_def p2_pre_def p2_post_def)

  have suspended_u:
      "unat
        (Scheduler_V611_Parse.globals.uxSchedulerSuspended_' c) = 0"
    and yield_u:
      "unat
        (Scheduler_V611_Parse.globals.eal6_port_yield_count_' c) = 0"
    using scalars0
    by (simp_all add: scheduler_scalar_rel_def p2_pre_def)
  have suspended0:
      "Scheduler_V611_Parse.globals.uxSchedulerSuspended_' c = 0"
    using suspended_u by (simp add: unat_eq_0)
  have yield0:
      "Scheduler_V611_Parse.globals.eal6_port_yield_count_' c = 0"
    using yield_u by (simp add: unat_eq_0)

  have scalars1:
      "scheduler_scalar_rel
        (p2_delay_2_source_state c D R) p2_post"
    using scalars0 suspended0 yield0
    by (simp add: scheduler_scalar_rel_def
        p2_delay_2_source_state_def p2_yield_state_def
        p2_resume_quiet_state_def scheduler_mem_state_def
        p2_suspend_state_def p2_pre_def p2_post_def)

  have current1:
      "scheduler_current_rel D
        (p2_delay_2_source_state c D R) p2_post"
    using current0
    by (simp add: scheduler_current_rel_def
        p2_delay_2_source_state_def p2_yield_state_def
        p2_resume_quiet_state_def scheduler_mem_state_def
        p2_suspend_state_def p2_pre_def p2_post_def)

  have boundary1:
      "scheduler_boundary_rel (p2_delay_2_source_state c D R)"
    using boundary0
    by (simp add: scheduler_boundary_rel_def
        p2_delay_2_source_state_def p2_yield_state_def
        p2_resume_quiet_state_def scheduler_mem_state_def
        p2_suspend_state_def)

  show ?thesis
    using decode1 roles1 scalars1 current1 boundary1 by blast
qed

lemma p2_delay_2_source_state_is_post:
  fixes c :: Scheduler_V611_Parse.globals
  assumes endpoint:
      "scheduler_endpoint_rel StableRunning D R c p2_pre"
    and footprint:
      "p2_source_footprint D R
        (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))"
  shows
    "scheduler_endpoint_rel YieldPending D R
       (p2_delay_2_source_state c D R) p2_post \<and>
     \<not> settled_wf p2_post"
proof -
  have raw: "raw_scheduler_rel D R c p2_pre"
    using endpoint by simp
  have decode0: "scheduler_decode_rel D p2_pre"
    and lists0: "scheduler_lists_rel D R c p2_pre"
    using raw by (auto simp: raw_scheduler_rel_def)
  have final_heap:
      "hrs_mem
         (Scheduler_V611_Parse.globals.t_hrs_'
           (p2_delay_2_source_state c D R)) =
       p2_remove_wake_insert_heap
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) D R"
    by (simp add: p2_delay_2_source_state_def p2_yield_state_def
        p2_resume_quiet_state_def scheduler_mem_state_def
        p2_suspend_state_def hrs_mem_update)
  have lists1:
      "scheduler_lists_rel D R
        (p2_delay_2_source_state c D R) p2_post"
    by (rule p2_remove_wake_insert_lists_rel[
          OF decode0 lists0 footprint final_heap])
  from p2_final_nonlist_relations[OF endpoint]
  have decode1: "scheduler_decode_rel D p2_post"
    and roles1:
      "scheduler_role_rel R (p2_delay_2_source_state c D R) p2_post"
    and scalars1:
      "scheduler_scalar_rel (p2_delay_2_source_state c D R) p2_post"
    and current1:
      "scheduler_current_rel D (p2_delay_2_source_state c D R) p2_post"
    and boundary1:
      "scheduler_boundary_rel (p2_delay_2_source_state c D R)"
    by blast+
  show ?thesis
    by (rule p2_post_conditional_endpointI[
          OF decode1 lists1 roles1 scalars1 current1 boundary1])
qed

theorem scheduler_vTaskDelay_2_p2_conditional_refines:
  fixes c :: Scheduler_V611_Parse.globals
  assumes endpoint:
      "scheduler_endpoint_rel StableRunning D R c p2_pre"
    and footprint:
      "p2_source_footprint D R
        (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))"
  shows
    "Scheduler_V611_Delay_Translation.vTaskDelay' (2 :: 32 word) \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       scheduler_endpoint_rel YieldPending D R t p2_post \<and>
       \<not> settled_wf p2_post
     \<rbrace>"
proof -
  note exact = scheduler_vTaskDelay_2_p2_exact_state[
      OF endpoint footprint]
  have post:
      "scheduler_endpoint_rel YieldPending D R
         (p2_delay_2_source_state c D R) p2_post \<and>
       \<not> settled_wf p2_post"
    by (rule p2_delay_2_source_state_is_post[OF endpoint footprint])
  show ?thesis
    apply (rule runs_to_weaken[OF exact])
    using post by auto
qed

corollary scheduler_vTaskDelay_2_p2_refines_task_delay_abs:
  fixes c :: Scheduler_V611_Parse.globals
  assumes endpoint:
      "scheduler_endpoint_rel StableRunning D R c p2_pre"
    and footprint:
      "p2_source_footprint D R
        (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))"
  shows
    "Scheduler_V611_Delay_Translation.vTaskDelay' (2 :: 32 word) \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       scheduler_endpoint_rel YieldPending D R t
         (task_delay_abs 2 p2_pre)
     \<rbrace>"
proof -
  note concrete = scheduler_vTaskDelay_2_p2_conditional_refines[
      OF endpoint footprint]
  show ?thesis
    apply (rule runs_to_weaken[OF concrete])
    by (simp add: task_delay_abs_2_p2)
qed

end
