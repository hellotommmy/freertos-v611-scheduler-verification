theory Scheduler_Generic_Root_Universe_Base
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Event_Root_Family_Rel.Scheduler_Event_Root_Family_Rel"
    "EAL6_FreeRTOS_V611_Scheduler_P2_Frozen_Static_Layout.Scheduler_P2_Frozen_Static_Layout"
begin

text \<open>
  Gate-H root-universe closure for the frozen proof-port configuration.

  The only constants fixed here are properties of the selected compilation:
  configMAX_PRIORITIES is 4, INCLUDE_vTaskDelete is 1, and the addressed
  global list objects are those certified by the frozen layout ledger.  The
  four ready-array slots and the addressed global roots are therefore a
  binary-layout boundary, not fixed scheduler inputs.  Every live-task set,
  task identity, runtime priority below 4, item key, ring length/order/cursor,
  heap, decoder, and external Event root remains universally quantified.

  xPendingReadyList is an Event-item root.  It is deliberately absent from
  the Generic universe.  Because INCLUDE_vTaskDelete is 1 in the frozen
  FreeRTOSConfig.h, xTasksWaitingTermination is a live Generic-item role and
  is deliberately present.  Omitting that ninth addressed object was a real
  model hole in the earlier eight-root P2 inventory.
\<close>

datatype generated_generic_root_role =
    GenericReadyRoot nat
  | GenericDelayedARoot
  | GenericDelayedBRoot
  | GenericSuspendedRoot
  | GenericTerminationRoot

fun generated_generic_role_source_root ::
  "generated_generic_root_role \<Rightarrow>
   Scheduler_V611_Parse.xLIST_C ptr"
where
  "generated_generic_role_source_root (GenericReadyRoot p) =
     sr_ready generated_scheduler_roots p"
| "generated_generic_role_source_root GenericDelayedARoot =
     sr_delayed_a generated_scheduler_roots"
| "generated_generic_role_source_root GenericDelayedBRoot =
     sr_delayed_b generated_scheduler_roots"
| "generated_generic_role_source_root GenericSuspendedRoot =
     sr_suspended generated_scheduler_roots"
| "generated_generic_role_source_root GenericTerminationRoot =
     Scheduler_V611_Parse.xTasksWaitingTermination_'"

definition GeneratedGenericRootRoles ::
  "generated_generic_root_role set"
where
  "GeneratedGenericRootRoles =
     {GenericReadyRoot 0, GenericReadyRoot 1,
      GenericReadyRoot 2, GenericReadyRoot 3,
      GenericDelayedARoot, GenericDelayedBRoot,
      GenericSuspendedRoot, GenericTerminationRoot}"

definition GeneratedGenericSourceRootUniverse ::
  "Scheduler_V611_Parse.xLIST_C ptr set"
where
  "GeneratedGenericSourceRootUniverse =
     generated_generic_role_source_root ` GeneratedGenericRootRoles"

definition GenericRootUniverse ::
  "List_V611_Raw_Skip_Translation.xLIST_C ptr set"
where
  "GenericRootUniverse =
     abi_list_ptr ` GeneratedGenericSourceRootUniverse"

definition GeneratedPendingEventRoot ::
  "List_V611_Raw_Skip_Translation.xLIST_C ptr"
where
  "GeneratedPendingEventRoot =
     abi_list_ptr (sr_pending generated_scheduler_roots)"

text \<open>The named-root list is just the frozen addressed list with the
  pending Event root removed.  This is also the role-injectivity ledger.\<close>

lemma frozen_addressed_xlist_roots_named:
  "frozen_addressed_xlist_roots =
    [sr_ready generated_scheduler_roots 0,
     sr_ready generated_scheduler_roots 1,
     sr_ready generated_scheduler_roots 2,
     sr_ready generated_scheduler_roots 3,
     sr_delayed_a generated_scheduler_roots,
     sr_delayed_b generated_scheduler_roots,
     sr_pending generated_scheduler_roots,
     sr_suspended generated_scheduler_roots,
     Scheduler_V611_Parse.xTasksWaitingTermination_']"
  by (simp only: frozen_addressed_xlist_roots_def
      p2_physical_roots_def append.simps)

lemma frozen_generated_named_roots_distinct:
  "distinct
    [sr_ready generated_scheduler_roots 0,
     sr_ready generated_scheduler_roots 1,
     sr_ready generated_scheduler_roots 2,
     sr_ready generated_scheduler_roots 3,
     sr_delayed_a generated_scheduler_roots,
     sr_delayed_b generated_scheduler_roots,
     sr_pending generated_scheduler_roots,
     sr_suspended generated_scheduler_roots,
     Scheduler_V611_Parse.xTasksWaitingTermination_']"
  using frozen_addressed_xlist_roots_distinct
  by (simp only: frozen_addressed_xlist_roots_named)

lemma GeneratedGenericRootRoles_finite [simp]:
  "finite GeneratedGenericRootRoles"
  by (simp add: GeneratedGenericRootRoles_def)

lemma GeneratedGenericSourceRootUniverse_finite [simp]:
  "finite GeneratedGenericSourceRootUniverse"
  by (simp add: GeneratedGenericSourceRootUniverse_def)

lemma GenericRootUniverse_finite [simp]:
  "finite GenericRootUniverse"
  by (simp add: GenericRootUniverse_def)

lemma generated_ready_role_cases:
  fixes p :: nat
  assumes "p < 4"
  shows "p = 0 \<or> p = 1 \<or> p = 2 \<or> p = 3"
  using assms by arith

lemma generated_generic_role_source_root_inj:
  "inj_on generated_generic_role_source_root GeneratedGenericRootRoles"
  using frozen_generated_named_roots_distinct
  by (auto simp only: inj_on_def GeneratedGenericRootRoles_def
      generated_generic_role_source_root.simps distinct.simps set_simps
      insert_iff singleton_iff)

lemma generated_generic_role_raw_root_inj:
  "inj_on (abi_list_ptr \<circ> generated_generic_role_source_root)
     GeneratedGenericRootRoles"
  using generated_generic_role_source_root_inj
  by (auto simp only: inj_on_def comp_apply abi_list_ptr_eq_iff)

lemma GeneratedGenericSourceRootUniverse_exact:
  "GeneratedGenericSourceRootUniverse =
    {sr_ready generated_scheduler_roots 0,
     sr_ready generated_scheduler_roots 1,
     sr_ready generated_scheduler_roots 2,
     sr_ready generated_scheduler_roots 3,
     sr_delayed_a generated_scheduler_roots,
     sr_delayed_b generated_scheduler_roots,
     sr_suspended generated_scheduler_roots,
     Scheduler_V611_Parse.xTasksWaitingTermination_'}"
  by (simp only: GeneratedGenericSourceRootUniverse_def
      GeneratedGenericRootRoles_def image_insert image_empty
      generated_generic_role_source_root.simps)

lemma GeneratedGenericSourceRootUniverse_cases:
  "lp \<in> GeneratedGenericSourceRootUniverse \<longleftrightarrow>
     (\<exists>p<4. lp = sr_ready generated_scheduler_roots p) \<or>
     lp = sr_delayed_a generated_scheduler_roots \<or>
     lp = sr_delayed_b generated_scheduler_roots \<or>
     lp = sr_suspended generated_scheduler_roots \<or>
     lp = Scheduler_V611_Parse.xTasksWaitingTermination_'"
proof -
  have bounded:
    "\<And>p::nat. p < 4 \<Longrightarrow>
       p = 0 \<or> p = 1 \<or> p = 2 \<or> p = 3"
    by (rule generated_ready_role_cases)
  have priority_bounds:
    "(0::nat) < 4 \<and> (1::nat) < 4 \<and>
     (2::nat) < 4 \<and> (3::nat) < 4"
    by simp
  show ?thesis
    using bounded priority_bounds
    by (auto simp only: GeneratedGenericSourceRootUniverse_exact
        insert_iff singleton_iff)
qed

lemma GenericRootUniverse_cases:
  "lp \<in> GenericRootUniverse \<longleftrightarrow>
     (\<exists>p<4.
        lp = abi_list_ptr (sr_ready generated_scheduler_roots p)) \<or>
     lp = abi_list_ptr (sr_delayed_a generated_scheduler_roots) \<or>
     lp = abi_list_ptr (sr_delayed_b generated_scheduler_roots) \<or>
     lp = abi_list_ptr (sr_suspended generated_scheduler_roots) \<or>
     lp = abi_list_ptr Scheduler_V611_Parse.xTasksWaitingTermination_'"
proof
  assume member: "lp \<in> GenericRootUniverse"
  then obtain source_lp where
      source: "source_lp \<in> GeneratedGenericSourceRootUniverse"
    and lp_eq: "lp = abi_list_ptr source_lp"
    unfolding GenericRootUniverse_def by blast
  have source_cases:
    "(\<exists>p<4. source_lp = sr_ready generated_scheduler_roots p) \<or>
     source_lp = sr_delayed_a generated_scheduler_roots \<or>
     source_lp = sr_delayed_b generated_scheduler_roots \<or>
     source_lp = sr_suspended generated_scheduler_roots \<or>
     source_lp = Scheduler_V611_Parse.xTasksWaitingTermination_'"
    using source
    by (simp only: GeneratedGenericSourceRootUniverse_cases)
  show
    "(\<exists>p<4.
        lp = abi_list_ptr (sr_ready generated_scheduler_roots p)) \<or>
     lp = abi_list_ptr (sr_delayed_a generated_scheduler_roots) \<or>
     lp = abi_list_ptr (sr_delayed_b generated_scheduler_roots) \<or>
     lp = abi_list_ptr (sr_suspended generated_scheduler_roots) \<or>
     lp = abi_list_ptr Scheduler_V611_Parse.xTasksWaitingTermination_'"
    using source_cases lp_eq by blast
next
  assume cases:
    "(\<exists>p<4.
        lp = abi_list_ptr (sr_ready generated_scheduler_roots p)) \<or>
     lp = abi_list_ptr (sr_delayed_a generated_scheduler_roots) \<or>
     lp = abi_list_ptr (sr_delayed_b generated_scheduler_roots) \<or>
     lp = abi_list_ptr (sr_suspended generated_scheduler_roots) \<or>
     lp = abi_list_ptr Scheduler_V611_Parse.xTasksWaitingTermination_'"
  have source_witness:
    "\<exists>source_lp\<in>GeneratedGenericSourceRootUniverse.
       lp = abi_list_ptr source_lp"
    using cases
    by (blast intro: iffD2[OF GeneratedGenericSourceRootUniverse_cases])
  show "lp \<in> GenericRootUniverse"
    using source_witness
    unfolding GenericRootUniverse_def by blast
qed

lemma GeneratedGenericSourceRootUniverse_addressed:
  "GeneratedGenericSourceRootUniverse =
     set frozen_addressed_xlist_roots -
       {sr_pending generated_scheduler_roots}"
proof (rule set_eqI)
  fix lp
  note named_distinct = frozen_generated_named_roots_distinct
  show
    "lp \<in> GeneratedGenericSourceRootUniverse \<longleftrightarrow>
     lp \<in> set frozen_addressed_xlist_roots -
       {sr_pending generated_scheduler_roots}"
    using named_distinct
    by (auto simp only: GeneratedGenericSourceRootUniverse_exact
        frozen_addressed_xlist_roots_named distinct.simps set_simps
        insert_iff singleton_iff Diff_iff)
qed

lemma GeneratedPendingEventRoot_not_Generic [simp]:
  "GeneratedPendingEventRoot \<notin> GenericRootUniverse"
proof
  assume pending:
    "GeneratedPendingEventRoot \<in> GenericRootUniverse"
  then obtain lp where source:
      "lp \<in> GeneratedGenericSourceRootUniverse"
    and equal: "GeneratedPendingEventRoot = abi_list_ptr lp"
    unfolding GenericRootUniverse_def by blast
  have lp_pending:
    "lp = sr_pending generated_scheduler_roots"
    using equal
    unfolding GeneratedPendingEventRoot_def
    by (simp only: abi_list_ptr_eq_iff)
  have
    "lp \<notin> GeneratedGenericSourceRootUniverse"
    using GeneratedGenericSourceRootUniverse_addressed lp_pending by blast
  then show False using source by contradiction
qed

lemma GeneratedSourceRootUniverse_complete_partition:
  "GeneratedGenericSourceRootUniverse \<union>
       {sr_pending generated_scheduler_roots} =
     set frozen_addressed_xlist_roots"
proof -
  have pending:
    "sr_pending generated_scheduler_roots \<in>
       set frozen_addressed_xlist_roots"
    using frozen_addressed_global_pointers
    by (simp add: frozen_addressed_xlist_roots_named)
  show ?thesis
    using GeneratedGenericSourceRootUniverse_addressed pending by blast
qed

lemma GenericRootUniverse_readyI:
  assumes "p < 4"
  shows
    "abi_list_ptr (sr_ready generated_scheduler_roots p)
       \<in> GenericRootUniverse"
  using assms by (auto simp: GenericRootUniverse_cases)

lemma GenericRootUniverse_delayed_aI [simp]:
  "abi_list_ptr (sr_delayed_a generated_scheduler_roots)
     \<in> GenericRootUniverse"
  by (simp add: GenericRootUniverse_cases)

lemma GenericRootUniverse_delayed_bI [simp]:
  "abi_list_ptr (sr_delayed_b generated_scheduler_roots)
     \<in> GenericRootUniverse"
  by (simp add: GenericRootUniverse_cases)

lemma GenericRootUniverse_suspendedI [simp]:
  "abi_list_ptr (sr_suspended generated_scheduler_roots)
     \<in> GenericRootUniverse"
  by (simp add: GenericRootUniverse_cases)

lemma GenericRootUniverse_terminationI [simp]:
  "abi_list_ptr Scheduler_V611_Parse.xTasksWaitingTermination_'
     \<in> GenericRootUniverse"
  by (simp add: GenericRootUniverse_cases)

lemma GeneratedGenericSourceRootUniverse_guarded:
  "\<forall>lp\<in>GeneratedGenericSourceRootUniverse. c_guard lp"
  using frozen_addressed_xlist_roots_guarded
    GeneratedGenericSourceRootUniverse_addressed by blast

lemma GenericRootUniverse_guarded:
  "\<forall>lp\<in>GenericRootUniverse. c_guard lp"
  using GeneratedGenericSourceRootUniverse_guarded
  by (auto simp: GenericRootUniverse_def abi_list_ptr_c_guard)

lemma GeneratedGenericSourceRootUniverse_pairwise_disjoint:
  assumes lp: "lp \<in> GeneratedGenericSourceRootUniverse"
    and lq: "lq \<in> GeneratedGenericSourceRootUniverse"
    and different: "lp \<noteq> lq"
  shows
    "scheduler_list_region lp \<inter> scheduler_list_region lq = {}"
  using frozen_addressed_xlist_roots_pairwise_disjoint
    GeneratedGenericSourceRootUniverse_addressed lp lq different
  by blast

lemma GenericRootUniverse_pairwise_disjoint:
  assumes lp: "lp \<in> GenericRootUniverse"
    and lq: "lq \<in> GenericRootUniverse"
    and different: "lp \<noteq> lq"
  shows "raw_list_region lp \<inter> raw_list_region lq = {}"
proof -
  obtain sp where sp:
      "sp \<in> GeneratedGenericSourceRootUniverse"
    and lp_eq: "lp = abi_list_ptr sp"
    using lp by (auto simp: GenericRootUniverse_def)
  obtain sq where sq:
      "sq \<in> GeneratedGenericSourceRootUniverse"
    and lq_eq: "lq = abi_list_ptr sq"
    using lq by (auto simp: GenericRootUniverse_def)
  have source_different: "sp \<noteq> sq"
    using different lp_eq lq_eq by simp
  have source_disjoint:
    "scheduler_list_region sp \<inter> scheduler_list_region sq = {}"
    by (rule GeneratedGenericSourceRootUniverse_pairwise_disjoint[
          OF sp sq source_different])
  show ?thesis
    using source_disjoint lp_eq lq_eq
    by (simp add: abi_list_region_eq)
qed

end
