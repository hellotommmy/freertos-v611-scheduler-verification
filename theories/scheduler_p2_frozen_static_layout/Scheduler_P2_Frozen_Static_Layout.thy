theory Scheduler_P2_Frozen_Static_Layout
  imports
    "EAL6_FreeRTOS_V611_Scheduler_P2_Source_Footprint.Scheduler_P2_Source_Footprint"
    "EAL6_FreeRTOS_V611_Scheduler_P2_Frozen_Root_Probe.Scheduler_P2_Frozen_Root_Probe"
begin

text \<open>
  G2: the complete addressed-data set selected by the frozen proof-TU ELF.
  The first five constants generate the eight physical P2 roots; the sixth is
  the termination-wait root that CParser also identified as addressed data.
\<close>

lemma frozen_addressed_global_pointers:
  "Scheduler_V611_Parse.pxReadyTasksLists_' =
       (Ptr 0x00102020 :: (Scheduler_V611_Parse.xLIST_C[4]) ptr) \<and>
   Scheduler_V611_Parse.xDelayedTaskList1_' =
       (Ptr 0x0010208c :: Scheduler_V611_Parse.xLIST_C ptr) \<and>
   Scheduler_V611_Parse.xDelayedTaskList2_' =
       (Ptr 0x001020a0 :: Scheduler_V611_Parse.xLIST_C ptr) \<and>
   Scheduler_V611_Parse.xPendingReadyList_' =
       (Ptr 0x001020bc :: Scheduler_V611_Parse.xLIST_C ptr) \<and>
   Scheduler_V611_Parse.xSuspendedTaskList_' =
       (Ptr 0x001020d4 :: Scheduler_V611_Parse.xLIST_C ptr) \<and>
   Scheduler_V611_Parse.xTasksWaitingTermination_' =
       (Ptr 0x001020e8 :: Scheduler_V611_Parse.xLIST_C ptr)"
  by (simp add: Scheduler_V611_Parse.pxReadyTasksLists_'_def
      Scheduler_V611_Parse.xDelayedTaskList1_'_def
      Scheduler_V611_Parse.xDelayedTaskList2_'_def
      Scheduler_V611_Parse.xPendingReadyList_'_def
      Scheduler_V611_Parse.xSuspendedTaskList_'_def
      Scheduler_V611_Parse.xTasksWaitingTermination_'_def)

lemma frozen_p2_physical_roots [simp]:
  "p2_physical_roots generated_scheduler_roots =
    [Ptr 0x00102020, Ptr 0x00102034, Ptr 0x00102048,
     Ptr 0x0010205c, Ptr 0x0010208c, Ptr 0x001020a0,
     Ptr 0x001020bc, Ptr 0x001020d4]"
  by (simp add: p2_physical_roots_def generated_scheduler_roots_def
      Scheduler_V611_Parse.pxReadyTasksLists_'_def
      Scheduler_V611_Parse.xDelayedTaskList1_'_def
      Scheduler_V611_Parse.xDelayedTaskList2_'_def
      Scheduler_V611_Parse.xPendingReadyList_'_def
      Scheduler_V611_Parse.xSuspendedTaskList_'_def
      array_ptr_index_def ptr_add_def Scheduler_V611_Parse.xLIST_C_size_of)

lemma frozen_xlist_guardI:
  fixes a :: addr
  assumes positive: "0 < unat a"
    and no_wrap: "unat a + 20 \<le> addr_card"
    and aligned: "4 dvd unat a"
  shows "c_guard (Ptr a :: Scheduler_V611_Parse.xLIST_C ptr)"
proof -
  have membership:
    "((0 :: addr) \<in> {a..+20}) =
      (unat a \<le> unat (0 :: addr) \<and>
       unat (0 :: addr) < unat a + 20)"
    by (rule intvl_no_overflow_nat[OF no_wrap])
  have no_null: "(0 :: addr) \<notin> {a..+20}"
    using membership positive by simp
  show ?thesis
    using aligned no_null
    by (simp add: c_guard_def c_null_guard_def ptr_aligned_def align_of_def
        size_of_def Scheduler_V611_Parse.xLIST_C_align_of
        Scheduler_V611_Parse.xLIST_C_size_of)
qed

lemma frozen_p2_physical_roots_distinct:
  "distinct (p2_physical_roots generated_scheduler_roots)"
  by simp

lemma frozen_p2_physical_roots_guarded:
  "\<forall>lp \<in> set (p2_physical_roots generated_scheduler_roots).
     c_guard lp"
  unfolding frozen_p2_physical_roots
  apply simp
  apply (intro conjI)
  apply (all \<open>rule frozen_xlist_guardI;
    simp add: addr_card_def card_word\<close>)
  done

lemma frozen_p2_physical_root_word_order:
  assumes lp: "lp \<in> set (p2_physical_roots generated_scheduler_roots)"
    and lq: "lq \<in> set (p2_physical_roots generated_scheduler_roots)"
    and distinct: "lp \<noteq> lq"
  shows
    "(ptr_val lp + of_nat 20 \<le> ptr_val lq \<and>
       ptr_val lp \<le> ptr_val lp + of_nat 20 \<and>
       ptr_val lq \<le> ptr_val lq + of_nat 20) \<or>
     (ptr_val lq + of_nat 20 \<le> ptr_val lp \<and>
       ptr_val lq \<le> ptr_val lq + of_nat 20 \<and>
       ptr_val lp \<le> ptr_val lp + of_nat 20)"
proof -
  from lp have lp_cases:
    "lp = Ptr 0x00102020 \<or> lp = Ptr 0x00102034 \<or>
     lp = Ptr 0x00102048 \<or> lp = Ptr 0x0010205c \<or>
     lp = Ptr 0x0010208c \<or> lp = Ptr 0x001020a0 \<or>
     lp = Ptr 0x001020bc \<or> lp = Ptr 0x001020d4"
    by simp
  from lq have lq_cases:
    "lq = Ptr 0x00102020 \<or> lq = Ptr 0x00102034 \<or>
     lq = Ptr 0x00102048 \<or> lq = Ptr 0x0010205c \<or>
     lq = Ptr 0x0010208c \<or> lq = Ptr 0x001020a0 \<or>
     lq = Ptr 0x001020bc \<or> lq = Ptr 0x001020d4"
    by simp
  from lp_cases lq_cases distinct show ?thesis
    apply (elim disjE)
    apply (all \<open>hypsubst\<close>)
    apply (all \<open>simp\<close>)
    done
qed

lemma frozen_p2_physical_roots_pairwise_disjoint:
  "\<forall>lp \<in> set (p2_physical_roots generated_scheduler_roots).
   \<forall>lq \<in> set (p2_physical_roots generated_scheduler_roots).
     lp \<noteq> lq \<longrightarrow>
       scheduler_list_region lp \<inter> scheduler_list_region lq = {}"
proof (intro ballI impI)
  fix lp lq
  assume lp: "lp \<in> set (p2_physical_roots generated_scheduler_roots)"
    and lq: "lq \<in> set (p2_physical_roots generated_scheduler_roots)"
    and distinct: "lp \<noteq> lq"
  have order:
    "(ptr_val lp + of_nat 20 \<le> ptr_val lq \<and>
       ptr_val lp \<le> ptr_val lp + of_nat 20 \<and>
       ptr_val lq \<le> ptr_val lq + of_nat 20) \<or>
     (ptr_val lq + of_nat 20 \<le> ptr_val lp \<and>
       ptr_val lq \<le> ptr_val lq + of_nat 20 \<and>
       ptr_val lp \<le> ptr_val lp + of_nat 20)"
    by (rule frozen_p2_physical_root_word_order[OF lp lq distinct])
  have size_bound: "(20 :: nat) < 2 ^ LENGTH(32)"
    by simp
  have list_size:
    "size_of TYPE(Scheduler_V611_Parse.xLIST_C) = 20"
    by (simp add: Scheduler_V611_Parse.xLIST_C_size_of)
  show "scheduler_list_region lp \<inter> scheduler_list_region lq = {}"
    using order size_bound list_size
    unfolding scheduler_list_region_def
    by (metis intvl_disjoint1 intvl_disjoint2)
qed

definition frozen_addressed_xlist_roots ::
  "Scheduler_V611_Parse.xLIST_C ptr list"
where
  "frozen_addressed_xlist_roots =
     p2_physical_roots generated_scheduler_roots @
       [Scheduler_V611_Parse.xTasksWaitingTermination_']"

lemma frozen_addressed_xlist_roots_exact [simp]:
  "frozen_addressed_xlist_roots =
    [Ptr 0x00102020, Ptr 0x00102034, Ptr 0x00102048,
     Ptr 0x0010205c, Ptr 0x0010208c, Ptr 0x001020a0,
     Ptr 0x001020bc, Ptr 0x001020d4, Ptr 0x001020e8]"
  by (simp add: frozen_addressed_xlist_roots_def
      Scheduler_V611_Parse.xTasksWaitingTermination_'_def)

lemma frozen_addressed_xlist_roots_distinct:
  "distinct frozen_addressed_xlist_roots"
  by simp

lemma frozen_addressed_xlist_roots_guarded:
  "\<forall>lp \<in> set frozen_addressed_xlist_roots. c_guard lp"
proof -
  have termination_guard:
    "c_guard Scheduler_V611_Parse.xTasksWaitingTermination_'"
    unfolding Scheduler_V611_Parse.xTasksWaitingTermination_'_def
    by (rule frozen_xlist_guardI;
        simp add: addr_card_def card_word)
  show ?thesis
    using frozen_p2_physical_roots_guarded termination_guard
    by (auto simp: frozen_addressed_xlist_roots_def
        Scheduler_V611_Parse.xTasksWaitingTermination_'_def)
qed

lemma frozen_p2_root_termination_disjoint:
  assumes lp: "lp \<in> set (p2_physical_roots generated_scheduler_roots)"
  shows
    "scheduler_list_region lp \<inter>
       scheduler_list_region
         Scheduler_V611_Parse.xTasksWaitingTermination_' = {}"
proof -
  from lp have lp_cases:
    "lp = Ptr 0x00102020 \<or> lp = Ptr 0x00102034 \<or>
     lp = Ptr 0x00102048 \<or> lp = Ptr 0x0010205c \<or>
     lp = Ptr 0x0010208c \<or> lp = Ptr 0x001020a0 \<or>
     lp = Ptr 0x001020bc \<or> lp = Ptr 0x001020d4"
    by simp
  from lp_cases show ?thesis
    apply (elim disjE)
    apply (all \<open>hypsubst\<close>)
    apply (all \<open>unfold scheduler_list_region_def\<close>)
    apply (all \<open>rule intvl_disjoint1;
      simp add: Scheduler_V611_Parse.xTasksWaitingTermination_'_def
        Scheduler_V611_Parse.xLIST_C_size_of\<close>)
    done
qed

lemma frozen_addressed_xlist_roots_pairwise_disjoint:
  "\<forall>lp \<in> set frozen_addressed_xlist_roots.
   \<forall>lq \<in> set frozen_addressed_xlist_roots.
     lp \<noteq> lq \<longrightarrow>
       scheduler_list_region lp \<inter> scheduler_list_region lq = {}"
proof (intro ballI impI)
  fix lp lq
  assume lp: "lp \<in> set frozen_addressed_xlist_roots"
    and lq: "lq \<in> set frozen_addressed_xlist_roots"
    and distinct: "lp \<noteq> lq"
  have lp_cases:
    "lp \<in> set (p2_physical_roots generated_scheduler_roots) \<or>
     lp = Scheduler_V611_Parse.xTasksWaitingTermination_'"
    using lp by (simp add: frozen_addressed_xlist_roots_def
        Scheduler_V611_Parse.xTasksWaitingTermination_'_def)
  have lq_cases:
    "lq \<in> set (p2_physical_roots generated_scheduler_roots) \<or>
     lq = Scheduler_V611_Parse.xTasksWaitingTermination_'"
    using lq by (simp add: frozen_addressed_xlist_roots_def
        Scheduler_V611_Parse.xTasksWaitingTermination_'_def)
  show "scheduler_list_region lp \<inter> scheduler_list_region lq = {}"
  proof (cases
      "lp = Scheduler_V611_Parse.xTasksWaitingTermination_'")
    case True
    then have lq_p2:
      "lq \<in> set (p2_physical_roots generated_scheduler_roots)"
      using lq_cases distinct by blast
    show ?thesis
      using frozen_p2_root_termination_disjoint[OF lq_p2] True
      by (simp add: Int_commute)
  next
    case False
    then have lp_p2:
      "lp \<in> set (p2_physical_roots generated_scheduler_roots)"
      using lp_cases by blast
    show ?thesis
    proof (cases
        "lq = Scheduler_V611_Parse.xTasksWaitingTermination_'")
      case True
      show ?thesis
        using frozen_p2_root_termination_disjoint[OF lp_p2] True by simp
    next
      case False
      then have lq_p2:
        "lq \<in> set (p2_physical_roots generated_scheduler_roots)"
        using lq_cases by blast
      show ?thesis
        using frozen_p2_physical_roots_pairwise_disjoint
          lp_p2 lq_p2 distinct by blast
    qed
  qed
qed

theorem frozen_addressed_xlist_geometry:
  "distinct frozen_addressed_xlist_roots \<and>
   (\<forall>lp \<in> set frozen_addressed_xlist_roots. c_guard lp) \<and>
   (\<forall>lp \<in> set frozen_addressed_xlist_roots.
    \<forall>lq \<in> set frozen_addressed_xlist_roots.
      lp \<noteq> lq \<longrightarrow>
        scheduler_list_region lp \<inter> scheduler_list_region lq = {})"
  using frozen_addressed_xlist_roots_distinct
    frozen_addressed_xlist_roots_guarded
    frozen_addressed_xlist_roots_pairwise_disjoint
  by blast

lemma frozen_p2_static_root_geometry_from_addressed:
  assumes
    "distinct frozen_addressed_xlist_roots \<and>
     (\<forall>lp \<in> set frozen_addressed_xlist_roots. c_guard lp) \<and>
     (\<forall>lp \<in> set frozen_addressed_xlist_roots.
      \<forall>lq \<in> set frozen_addressed_xlist_roots.
        lp \<noteq> lq \<longrightarrow>
          scheduler_list_region lp \<inter> scheduler_list_region lq = {})"
  shows
    "distinct (p2_physical_roots generated_scheduler_roots) \<and>
     (\<forall>lp \<in> set (p2_physical_roots generated_scheduler_roots).
        c_guard lp) \<and>
     (\<forall>lp \<in> set (p2_physical_roots generated_scheduler_roots).
      \<forall>lq \<in> set (p2_physical_roots generated_scheduler_roots).
        lp \<noteq> lq \<longrightarrow>
          scheduler_list_region lp \<inter> scheduler_list_region lq = {})"
proof -
  have subset:
    "set (p2_physical_roots generated_scheduler_roots) \<subseteq>
       set frozen_addressed_xlist_roots"
    by (simp add: frozen_addressed_xlist_roots_def)
  have root_distinct:
    "distinct (p2_physical_roots generated_scheduler_roots)"
    using assms by (simp add: frozen_addressed_xlist_roots_def)
  have root_guards:
    "\<forall>lp \<in> set (p2_physical_roots generated_scheduler_roots).
       c_guard lp"
    using assms subset by blast
  have root_separation:
    "\<forall>lp \<in> set (p2_physical_roots generated_scheduler_roots).
     \<forall>lq \<in> set (p2_physical_roots generated_scheduler_roots).
       lp \<noteq> lq \<longrightarrow>
         scheduler_list_region lp \<inter> scheduler_list_region lq = {}"
    using assms subset by blast
  show ?thesis
    using root_distinct root_guards root_separation by blast
qed

theorem frozen_p2_static_root_geometry:
  "distinct (p2_physical_roots generated_scheduler_roots) \<and>
   (\<forall>lp \<in> set (p2_physical_roots generated_scheduler_roots).
      c_guard lp) \<and>
   (\<forall>lp \<in> set (p2_physical_roots generated_scheduler_roots).
    \<forall>lq \<in> set (p2_physical_roots generated_scheduler_roots).
      lp \<noteq> lq \<longrightarrow>
        scheduler_list_region lp \<inter> scheduler_list_region lq = {})"
  by (rule frozen_p2_static_root_geometry_from_addressed[
        OF frozen_addressed_xlist_geometry])

end
