theory Scheduler_P2_Frozen_Dynamic_Geometry
  imports
    "EAL6_FreeRTOS_V611_Scheduler_P2_Frozen_Static_Layout.Scheduler_P2_Frozen_Static_Layout"
begin

text \<open>
  G3a fixes two fresh, aligned runtime TCB identities.  These addresses are
  logical witness addresses, not ELF objects and not an allocator theorem.
\<close>

fun frozen_p2_tcb_ptr ::
  "p2_tid \<Rightarrow> Scheduler_V611_Parse.tskTaskControlBlock_C ptr"
where
  "frozen_p2_tcb_ptr P2_IDLE = Ptr 0x00200000"
| "frozen_p2_tcb_ptr P2_RUN = Ptr 0x00200100"

definition frozen_p2_tcb_decode ::
  "Scheduler_V611_Parse.tskTaskControlBlock_C ptr \<Rightarrow> p2_tid option"
where
  "frozen_p2_tcb_decode p =
    (if p = frozen_p2_tcb_ptr P2_IDLE then Some P2_IDLE
     else if p = frozen_p2_tcb_ptr P2_RUN then Some P2_RUN
     else None)"

definition frozen_p2_node_decode ::
  "List_V611_Raw_Skip_Translation.xLIST_ITEM_C ptr
     \<Rightarrow> p2_tid node_kind option"
where
  "frozen_p2_node_decode p =
    (if p = abi_generic_list_item_ptr (frozen_p2_tcb_ptr P2_IDLE)
       then Some (Generic P2_IDLE)
     else if p = abi_event_list_item_ptr (frozen_p2_tcb_ptr P2_IDLE)
       then Some (Event P2_IDLE)
     else if p = abi_generic_list_item_ptr (frozen_p2_tcb_ptr P2_RUN)
       then Some (Generic P2_RUN)
     else if p = abi_event_list_item_ptr (frozen_p2_tcb_ptr P2_RUN)
       then Some (Event P2_RUN)
     else None)"

definition frozen_p2_decode :: "p2_tid scheduler_decode" where
  "frozen_p2_decode =
    \<lparr>sd_tcb_ptr = frozen_p2_tcb_ptr,
     sd_tcb_decode = frozen_p2_tcb_decode,
     sd_node_decode = frozen_p2_node_decode\<rparr>"

lemma frozen_p2_embedded_pointer_values [simp]:
  "ptr_val (abi_generic_list_item_ptr (frozen_p2_tcb_ptr P2_IDLE)) =
       0x00200004 \<and>
   ptr_val (abi_event_list_item_ptr (frozen_p2_tcb_ptr P2_IDLE)) =
       0x00200018 \<and>
   ptr_val (abi_generic_list_item_ptr (frozen_p2_tcb_ptr P2_RUN)) =
       0x00200104 \<and>
   ptr_val (abi_event_list_item_ptr (frozen_p2_tcb_ptr P2_RUN)) =
       0x00200118"
  by (simp add: abi_generic_list_item_ptr_def abi_event_list_item_ptr_def
      abi_item_ptr_def field_lvalue_def
      Scheduler_V611_Parse.tskTaskControlBlock_C_xGenericListItem_C_fl
      Scheduler_V611_Parse.tskTaskControlBlock_C_xEventListItem_C_fl)

lemma frozen_p2_decoder_rel:
  "scheduler_decode_rel frozen_p2_decode p2_pre"
  unfolding scheduler_decode_rel_def frozen_p2_decode_def
    frozen_p2_tcb_decode_def frozen_p2_node_decode_def
  by (simp add: p2_pre_def inj_on_def
      abi_generic_list_item_ptr_def abi_event_list_item_ptr_def
      abi_item_ptr_def field_lvalue_def
      Scheduler_V611_Parse.tskTaskControlBlock_C_xGenericListItem_C_fl
      Scheduler_V611_Parse.tskTaskControlBlock_C_xEventListItem_C_fl)

lemma frozen_tcb_guardI:
  fixes a :: addr
  assumes positive: "0 < unat a"
    and no_wrap: "unat a + 68 \<le> addr_card"
    and aligned: "4 dvd unat a"
  shows "c_guard (Ptr a :: Scheduler_V611_Parse.tskTaskControlBlock_C ptr)"
proof -
  have membership:
    "((0 :: addr) \<in> {a..+68}) =
      (unat a \<le> unat (0 :: addr) \<and>
       unat (0 :: addr) < unat a + 68)"
    by (rule intvl_no_overflow_nat[OF no_wrap])
  have no_null: "(0 :: addr) \<notin> {a..+68}"
    using membership positive by simp
  show ?thesis
    using aligned no_null
    by (simp add: c_guard_def c_null_guard_def ptr_aligned_def align_of_def
        size_of_def Scheduler_V611_Parse.tskTaskControlBlock_C_align_of
        Scheduler_V611_Parse.tskTaskControlBlock_C_size)
qed

lemma frozen_item_guardI:
  fixes a :: addr
  assumes positive: "0 < unat a"
    and no_wrap: "unat a + 20 \<le> addr_card"
    and aligned: "4 dvd unat a"
  shows
    "c_guard
      (Ptr a :: List_V611_Raw_Skip_Translation.xLIST_ITEM_C ptr)"
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
        size_of_def
        List_V611_Raw_Skip_Translation.xLIST_ITEM_C_align_of
        List_V611_Raw_Skip_Translation.xLIST_ITEM_C_size_of)
qed

lemma frozen_scheduler_item_guardI:
  fixes a :: addr
  assumes positive: "0 < unat a"
    and no_wrap: "unat a + 20 \<le> addr_card"
    and aligned: "4 dvd unat a"
  shows "c_guard (Ptr a :: Scheduler_V611_Parse.xLIST_ITEM_C ptr)"
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
        size_of_def Scheduler_V611_Parse.xLIST_ITEM_C_align_of
        Scheduler_V611_Parse.xLIST_ITEM_C_size_of)
qed

lemma intvl_offset_subset:
  fixes a :: addr
    and m n total :: nat
  assumes bound: "m + n \<le> total"
  shows "{a + of_nat m..+n} \<subseteq> {a..+total}"
proof
  fix x
  assume member: "x \<in> {a + of_nat m..+n}"
  then obtain k where
      x: "x = (a + of_nat m) + of_nat k"
    and k: "k < n"
    by (blast dest: intvlD)
  have offset: "m + k < total"
    using bound k by linarith
  have "x = a + of_nat (m + k)"
    using x by (simp add: ac_simps)
  then show "x \<in> {a..+total}"
    using offset intvlI by blast
qed

lemma frozen_p2_tcb_ptrs [simp]:
  "p2_tcb_ptrs frozen_p2_decode =
    [Ptr 0x00200000, Ptr 0x00200100]"
  by (simp add: p2_tcb_ptrs_def frozen_p2_decode_def)

lemma frozen_p2_tcb_geometry:
  "distinct (p2_tcb_ptrs frozen_p2_decode) \<and>
   (\<forall>tp \<in> set (p2_tcb_ptrs frozen_p2_decode). c_guard tp) \<and>
   (\<forall>tp \<in> set (p2_tcb_ptrs frozen_p2_decode).
    \<forall>tq \<in> set (p2_tcb_ptrs frozen_p2_decode).
      tp \<noteq> tq \<longrightarrow>
        scheduler_tcb_region tp \<inter> scheduler_tcb_region tq = {})"
proof -
  have idle_guard:
    "c_guard
      (Ptr 0x00200000 :: Scheduler_V611_Parse.tskTaskControlBlock_C ptr)"
    by (rule frozen_tcb_guardI; simp add: addr_card_def card_word)
  have run_guard:
    "c_guard
      (Ptr 0x00200100 :: Scheduler_V611_Parse.tskTaskControlBlock_C ptr)"
    by (rule frozen_tcb_guardI; simp add: addr_card_def card_word)
  have separate:
    "scheduler_tcb_region
        (Ptr 0x00200000 :: Scheduler_V611_Parse.tskTaskControlBlock_C ptr)
       \<inter>
     scheduler_tcb_region
        (Ptr 0x00200100 :: Scheduler_V611_Parse.tskTaskControlBlock_C ptr) = {}"
    unfolding scheduler_tcb_region_size
    by (rule intvl_disjoint1; simp)
  show ?thesis
    using idle_guard run_guard separate
    by (simp add: Int_commute)
qed

lemma frozen_p2_tcb_addressed_xlist_separation:
  "\<forall>tp \<in> set (p2_tcb_ptrs frozen_p2_decode).
   \<forall>lp \<in> set frozen_addressed_xlist_roots.
     scheduler_tcb_region tp \<inter> scheduler_list_region lp = {}"
  apply (simp add: scheduler_tcb_region_size scheduler_list_region_def
    Scheduler_V611_Parse.xLIST_C_size_of)
  apply (intro conjI)
  apply (all \<open>rule intvl_disjoint2; simp\<close>)
  done

lemma frozen_p2_tcb_root_separation:
  "\<forall>tp \<in> set (p2_tcb_ptrs frozen_p2_decode).
   \<forall>lp \<in> set (p2_physical_roots generated_scheduler_roots).
     scheduler_tcb_region tp \<inter> scheduler_list_region lp = {}"
proof -
  have subset:
    "set (p2_physical_roots generated_scheduler_roots) \<subseteq>
       set frozen_addressed_xlist_roots"
    by (auto simp: frozen_addressed_xlist_roots_def)
  show ?thesis
    using frozen_p2_tcb_addressed_xlist_separation subset by blast
qed

lemma frozen_p2_embedded_geometry:
  "\<forall>t \<in> {P2_IDLE, P2_RUN}.
     c_guard (scheduler_generic_item_ptr (sd_tcb_ptr frozen_p2_decode t)) \<and>
     c_guard (scheduler_event_item_ptr (sd_tcb_ptr frozen_p2_decode t)) \<and>
     scheduler_item_region
         (scheduler_generic_item_ptr (sd_tcb_ptr frozen_p2_decode t))
       \<subseteq> scheduler_tcb_region (sd_tcb_ptr frozen_p2_decode t) \<and>
     scheduler_item_region
         (scheduler_event_item_ptr (sd_tcb_ptr frozen_p2_decode t))
       \<subseteq> scheduler_tcb_region (sd_tcb_ptr frozen_p2_decode t) \<and>
     scheduler_item_region
         (scheduler_generic_item_ptr (sd_tcb_ptr frozen_p2_decode t))
       \<inter> scheduler_item_region
         (scheduler_event_item_ptr (sd_tcb_ptr frozen_p2_decode t)) = {}"
  unfolding frozen_p2_decode_def
  apply (simp add: scheduler_generic_item_ptr_def scheduler_event_item_ptr_def
      scheduler_item_region_def scheduler_tcb_region_size
      field_lvalue_def
      Scheduler_V611_Parse.tskTaskControlBlock_C_xGenericListItem_C_fl
      Scheduler_V611_Parse.tskTaskControlBlock_C_xEventListItem_C_fl
      Scheduler_V611_Parse.xLIST_ITEM_C_size_of)
  apply (intro conjI)
  subgoal by (rule frozen_scheduler_item_guardI;
      simp add: addr_card_def card_word)
  subgoal by (rule frozen_scheduler_item_guardI;
      simp add: addr_card_def card_word)
  subgoal
  proof -
    have subset:
      "{(0x00200000 :: addr) + of_nat 4..+20} \<subseteq>
       {(0x00200000 :: addr)..+68}"
      by (rule intvl_offset_subset; simp)
    show ?thesis using subset by simp
  qed
  subgoal
  proof -
    have subset:
      "{(0x00200000 :: addr) + of_nat 24..+20} \<subseteq>
       {(0x00200000 :: addr)..+68}"
      by (rule intvl_offset_subset; simp)
    show ?thesis using subset by simp
  qed
  subgoal by (rule intvl_disjoint1; simp)
  subgoal by (rule frozen_scheduler_item_guardI;
      simp add: addr_card_def card_word)
  subgoal by (rule frozen_scheduler_item_guardI;
      simp add: addr_card_def card_word)
  subgoal
  proof -
    have subset:
      "{(0x00200100 :: addr) + of_nat 4..+20} \<subseteq>
       {(0x00200100 :: addr)..+68}"
      by (rule intvl_offset_subset; simp)
    show ?thesis using subset by simp
  qed
  subgoal
  proof -
    have subset:
      "{(0x00200100 :: addr) + of_nat 24..+20} \<subseteq>
       {(0x00200100 :: addr)..+68}"
      by (rule intvl_offset_subset; simp)
    show ?thesis using subset by simp
  qed
  subgoal by (rule intvl_disjoint1; simp)
  done

theorem frozen_p2_nonheap_geometry:
  "scheduler_decode_rel frozen_p2_decode p2_pre \<and>
   distinct (p2_tcb_ptrs frozen_p2_decode) \<and>
   (\<forall>tp \<in> set (p2_tcb_ptrs frozen_p2_decode). c_guard tp) \<and>
   (\<forall>tp \<in> set (p2_tcb_ptrs frozen_p2_decode).
    \<forall>tq \<in> set (p2_tcb_ptrs frozen_p2_decode).
      tp \<noteq> tq \<longrightarrow>
        scheduler_tcb_region tp \<inter> scheduler_tcb_region tq = {}) \<and>
   (\<forall>tp \<in> set (p2_tcb_ptrs frozen_p2_decode).
    \<forall>lp \<in> set frozen_addressed_xlist_roots.
      scheduler_tcb_region tp \<inter> scheduler_list_region lp = {}) \<and>
   (\<forall>tp \<in> set (p2_tcb_ptrs frozen_p2_decode).
    \<forall>lp \<in> set (p2_physical_roots generated_scheduler_roots).
      scheduler_tcb_region tp \<inter> scheduler_list_region lp = {}) \<and>
   (\<forall>t \<in> {P2_IDLE, P2_RUN}.
      c_guard (scheduler_generic_item_ptr (sd_tcb_ptr frozen_p2_decode t)) \<and>
      c_guard (scheduler_event_item_ptr (sd_tcb_ptr frozen_p2_decode t)) \<and>
      scheduler_item_region
          (scheduler_generic_item_ptr (sd_tcb_ptr frozen_p2_decode t))
        \<subseteq> scheduler_tcb_region (sd_tcb_ptr frozen_p2_decode t) \<and>
      scheduler_item_region
          (scheduler_event_item_ptr (sd_tcb_ptr frozen_p2_decode t))
        \<subseteq> scheduler_tcb_region (sd_tcb_ptr frozen_p2_decode t) \<and>
      scheduler_item_region
          (scheduler_generic_item_ptr (sd_tcb_ptr frozen_p2_decode t))
        \<inter> scheduler_item_region
          (scheduler_event_item_ptr (sd_tcb_ptr frozen_p2_decode t)) = {})"
  using frozen_p2_decoder_rel frozen_p2_tcb_geometry
    frozen_p2_tcb_addressed_xlist_separation
    frozen_p2_tcb_root_separation frozen_p2_embedded_geometry
  by blast

end
