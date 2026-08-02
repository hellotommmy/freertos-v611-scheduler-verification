theory Scheduler_Universal_Geometry
  imports
    "EAL6_FreeRTOS_V611_Scheduler_P2_Raw_Relation.Scheduler_P2_Raw_Relation"
begin

text \<open>
  Generic Gate-H storage geometry.  The development quantifies over an
  arbitrary finite live-task set and never enumerates tasks, fixes their
  addresses, or constrains their priorities.  The existing scheduler decoder
  record is reused, but no P2 state or P2 theorem occurs in any statement.

  Pointer-map injectivity does not by itself make the separately supplied
  decoder an inverse: replacing the decoder by the constant-None function
  leaves the pointer map unchanged.  Therefore storage geometry and decoder
  round-trip laws are recorded as separate, explicit obligations below.
\<close>

definition universal_tcb_region ::
  "Scheduler_V611_Parse.tskTaskControlBlock_C ptr \<Rightarrow> addr set"
where
  "universal_tcb_region p =
     {ptr_val p..+size_of TYPE(Scheduler_V611_Parse.tskTaskControlBlock_C)}"

definition universal_item_region ::
  "List_V611_Raw_Skip_Translation.xLIST_ITEM_C ptr \<Rightarrow> addr set"
where
  "universal_item_region p =
     {ptr_val p..+
       size_of TYPE(List_V611_Raw_Skip_Translation.xLIST_ITEM_C)}"

lemma universal_tcb_region_size:
  "universal_tcb_region p = {ptr_val p..+68}"
  by (simp add: universal_tcb_region_def
      Scheduler_V611_Parse.tskTaskControlBlock_C_size)

lemma universal_item_region_size:
  "universal_item_region p = {ptr_val p..+20}"
  by (simp add: universal_item_region_def
      List_V611_Raw_Skip_Translation.xLIST_ITEM_C_size_of)

lemma universal_generic_item_ptr_val [simp]:
  "ptr_val (abi_generic_list_item_ptr tp) = ptr_val tp + 4"
  by (simp add: abi_generic_list_item_ptr_def abi_item_ptr_def
      field_lvalue_def
      Scheduler_V611_Parse.tskTaskControlBlock_C_xGenericListItem_C_fl)

lemma universal_event_item_ptr_val [simp]:
  "ptr_val (abi_event_list_item_ptr tp) = ptr_val tp + 24"
  by (simp add: abi_event_list_item_ptr_def abi_item_ptr_def
      field_lvalue_def
      Scheduler_V611_Parse.tskTaskControlBlock_C_xEventListItem_C_fl)

lemma universal_intvl_offset_subset:
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

lemma universal_generic_item_region_subset_tcb:
  "universal_item_region (abi_generic_list_item_ptr tp)
     \<subseteq> universal_tcb_region tp"
proof -
  have
    "{ptr_val tp + of_nat 4..+20} \<subseteq>
       {ptr_val tp..+68}"
    by (rule universal_intvl_offset_subset) simp
  then show ?thesis
    by (simp only: universal_item_region_size universal_tcb_region_size
        universal_generic_item_ptr_val of_nat_numeral)
qed

lemma universal_event_item_region_subset_tcb:
  "universal_item_region (abi_event_list_item_ptr tp)
     \<subseteq> universal_tcb_region tp"
proof -
  have
    "{ptr_val tp + of_nat 24..+20} \<subseteq>
       {ptr_val tp..+68}"
    by (rule universal_intvl_offset_subset) simp
  then show ?thesis
    by (simp only: universal_item_region_size universal_tcb_region_size
        universal_event_item_ptr_val of_nat_numeral)
qed

datatype universal_tcb_component =
    WholeTCB
  | GenericItem
  | EventItem

fun universal_component_region ::
  "'tid scheduler_decode \<Rightarrow> 'tid \<Rightarrow>
   universal_tcb_component \<Rightarrow> addr set"
where
  "universal_component_region D t WholeTCB =
     universal_tcb_region (sd_tcb_ptr D t)"
| "universal_component_region D t GenericItem =
     universal_item_region
       (abi_generic_list_item_ptr (sd_tcb_ptr D t))"
| "universal_component_region D t EventItem =
     universal_item_region
       (abi_event_list_item_ptr (sd_tcb_ptr D t))"

fun universal_component_base ::
  "'tid scheduler_decode \<Rightarrow> 'tid \<Rightarrow>
   universal_tcb_component \<Rightarrow> addr"
where
  "universal_component_base D t WholeTCB =
     ptr_val (sd_tcb_ptr D t)"
| "universal_component_base D t GenericItem =
     ptr_val (abi_generic_list_item_ptr (sd_tcb_ptr D t))"
| "universal_component_base D t EventItem =
     ptr_val (abi_event_list_item_ptr (sd_tcb_ptr D t))"

lemma universal_component_region_subset_tcb:
  "universal_component_region D t component
     \<subseteq> universal_tcb_region (sd_tcb_ptr D t)"
  by (cases component)
    (simp_all add: universal_generic_item_region_subset_tcb
      universal_event_item_region_subset_tcb)

lemma universal_component_base_member:
  "universal_component_base D t component
     \<in> universal_component_region D t component"
proof -
  have tcb_base:
    "ptr_val (sd_tcb_ptr D t) \<in>
       universal_tcb_region (sd_tcb_ptr D t)"
    using intvlI[of 0 68 "ptr_val (sd_tcb_ptr D t)"]
    by (simp add: universal_tcb_region_size)
  have generic_base:
    "ptr_val (abi_generic_list_item_ptr (sd_tcb_ptr D t)) \<in>
       universal_item_region
         (abi_generic_list_item_ptr (sd_tcb_ptr D t))"
    using intvlI[of 0 20
      "ptr_val (abi_generic_list_item_ptr (sd_tcb_ptr D t))"]
    by (simp add: universal_item_region_size)
  have event_base:
    "ptr_val (abi_event_list_item_ptr (sd_tcb_ptr D t)) \<in>
       universal_item_region
         (abi_event_list_item_ptr (sd_tcb_ptr D t))"
    using intvlI[of 0 20
      "ptr_val (abi_event_list_item_ptr (sd_tcb_ptr D t))"]
    by (simp add: universal_item_region_size)
  show ?thesis
    using tcb_base generic_base event_base
    by (cases component) simp_all
qed

definition universal_tcb_geometry ::
  "'tid set \<Rightarrow> 'tid scheduler_decode \<Rightarrow> bool"
where
  "universal_tcb_geometry live D \<longleftrightarrow>
     finite live \<and>
     inj_on (sd_tcb_ptr D) live \<and>
     (\<forall>t\<in>live. c_guard (sd_tcb_ptr D t)) \<and>
     (\<forall>t\<in>live. \<forall>u\<in>live. t \<noteq> u \<longrightarrow>
        universal_tcb_region (sd_tcb_ptr D t) \<inter>
          universal_tcb_region (sd_tcb_ptr D u) = {})"

lemma universal_tcb_geometry_finiteD:
  "universal_tcb_geometry live D \<Longrightarrow> finite live"
  by (simp add: universal_tcb_geometry_def)

lemma universal_tcb_geometry_guardD:
  assumes geometry: "universal_tcb_geometry live D"
      and live: "t \<in> live"
  shows "c_guard (sd_tcb_ptr D t)"
  using geometry live by (auto simp: universal_tcb_geometry_def)

lemma universal_different_live_tcb_ptrs:
  assumes geometry: "universal_tcb_geometry live D"
      and t_live: "t \<in> live"
      and u_live: "u \<in> live"
      and distinct: "t \<noteq> u"
  shows "sd_tcb_ptr D t \<noteq> sd_tcb_ptr D u"
  using geometry t_live u_live distinct
  by (auto simp: universal_tcb_geometry_def inj_on_def)

theorem universal_different_live_component_regions_disjoint:
  assumes geometry: "universal_tcb_geometry live D"
      and t_live: "t \<in> live"
      and u_live: "u \<in> live"
      and distinct: "t \<noteq> u"
  shows
    "universal_component_region D t left \<inter>
       universal_component_region D u right = {}"
proof -
  have tcb_disjoint:
    "universal_tcb_region (sd_tcb_ptr D t) \<inter>
       universal_tcb_region (sd_tcb_ptr D u) = {}"
    using geometry t_live u_live distinct
    by (auto simp: universal_tcb_geometry_def)
  have left_subset:
    "universal_component_region D t left \<subseteq>
       universal_tcb_region (sd_tcb_ptr D t)"
    by (rule universal_component_region_subset_tcb)
  have right_subset:
    "universal_component_region D u right \<subseteq>
       universal_tcb_region (sd_tcb_ptr D u)"
    by (rule universal_component_region_subset_tcb)
  show ?thesis
    using left_subset right_subset tcb_disjoint by blast
qed

theorem universal_different_live_component_bases_neq:
  assumes geometry: "universal_tcb_geometry live D"
      and t_live: "t \<in> live"
      and u_live: "u \<in> live"
      and distinct: "t \<noteq> u"
  shows
    "universal_component_base D t left \<noteq>
       universal_component_base D u right"
proof
  assume equal:
    "universal_component_base D t left =
       universal_component_base D u right"
  have left_member:
    "universal_component_base D t left \<in>
       universal_component_region D t left"
    by (rule universal_component_base_member)
  have right_member:
    "universal_component_base D u right \<in>
       universal_component_region D u right"
    by (rule universal_component_base_member)
  have disjoint:
    "universal_component_region D t left \<inter>
       universal_component_region D u right = {}"
    by (rule universal_different_live_component_regions_disjoint[
          OF geometry t_live u_live distinct])
  have common:
    "universal_component_base D t left \<in>
       universal_component_region D t left \<inter>
         universal_component_region D u right"
  proof
    show
      "universal_component_base D t left \<in>
         universal_component_region D t left"
      by (rule left_member)
    show
      "universal_component_base D t left \<in>
         universal_component_region D u right"
      using equal right_member by simp
  qed
  from common disjoint show False
    by simp
qed

definition universal_decoder_laws ::
  "'tid set \<Rightarrow> 'tid scheduler_decode \<Rightarrow> bool"
where
  "universal_decoder_laws live D \<longleftrightarrow>
     (\<forall>t\<in>live.
        sd_tcb_decode D (sd_tcb_ptr D t) = Some t \<and>
        sd_node_decode D
          (abi_generic_list_item_ptr (sd_tcb_ptr D t)) =
            Some (Generic t) \<and>
        sd_node_decode D
          (abi_event_list_item_ptr (sd_tcb_ptr D t)) =
            Some (Event t)) \<and>
     (\<forall>p t. sd_tcb_decode D p = Some t \<longrightarrow>
        t \<in> live \<and> p = sd_tcb_ptr D t) \<and>
     (\<forall>p t. sd_node_decode D p = Some (Generic t) \<longrightarrow>
        t \<in> live \<and>
        p = abi_generic_list_item_ptr (sd_tcb_ptr D t)) \<and>
     (\<forall>p t. sd_node_decode D p = Some (Event t) \<longrightarrow>
        t \<in> live \<and>
        p = abi_event_list_item_ptr (sd_tcb_ptr D t)) \<and>
     (\<forall>p n. sd_node_decode D p = Some n \<longrightarrow>
        node_owner n \<in> live)"

lemma pointer_injectivity_does_not_force_decoder_roundtrip:
  fixes D :: "'tid scheduler_decode"
  defines
    "D0 \<equiv> D\<lparr>sd_tcb_decode := (\<lambda>_. None)\<rparr>"
  shows
    "inj_on (sd_tcb_ptr D0) live = inj_on (sd_tcb_ptr D) live \<and>
     sd_tcb_decode D0 (sd_tcb_ptr D0 t) = None"
  by (simp add: D0_def)

lemma universal_tcb_decode_iff:
  assumes laws: "universal_decoder_laws live D"
  shows
    "sd_tcb_decode D p = Some t \<longleftrightarrow>
       t \<in> live \<and> p = sd_tcb_ptr D t"
proof
  assume decoded: "sd_tcb_decode D p = Some t"
  from laws have inverse:
    "\<forall>q u. sd_tcb_decode D q = Some u \<longrightarrow>
       u \<in> live \<and> q = sd_tcb_ptr D u"
    unfolding universal_decoder_laws_def by blast
  show "t \<in> live \<and> p = sd_tcb_ptr D t"
    using inverse decoded by blast
next
  assume rhs: "t \<in> live \<and> p = sd_tcb_ptr D t"
  from laws have forward:
    "\<forall>u\<in>live. sd_tcb_decode D (sd_tcb_ptr D u) = Some u"
    unfolding universal_decoder_laws_def by blast
  show "sd_tcb_decode D p = Some t"
    using forward rhs by blast
qed

lemma universal_node_decode_Generic_iff:
  assumes laws: "universal_decoder_laws live D"
  shows
    "sd_node_decode D p = Some (Generic t) \<longleftrightarrow>
       t \<in> live \<and>
       p = abi_generic_list_item_ptr (sd_tcb_ptr D t)"
proof
  assume decoded: "sd_node_decode D p = Some (Generic t)"
  from laws have inverse:
    "\<forall>q u. sd_node_decode D q = Some (Generic u) \<longrightarrow>
       u \<in> live \<and>
       q = abi_generic_list_item_ptr (sd_tcb_ptr D u)"
    unfolding universal_decoder_laws_def by blast
  show
    "t \<in> live \<and>
     p = abi_generic_list_item_ptr (sd_tcb_ptr D t)"
    using inverse decoded by blast
next
  assume rhs:
    "t \<in> live \<and>
     p = abi_generic_list_item_ptr (sd_tcb_ptr D t)"
  from laws have forward:
    "\<forall>u\<in>live.
       sd_node_decode D
         (abi_generic_list_item_ptr (sd_tcb_ptr D u)) =
           Some (Generic u)"
    unfolding universal_decoder_laws_def by blast
  show "sd_node_decode D p = Some (Generic t)"
    using forward rhs by blast
qed

lemma universal_node_decode_Event_iff:
  assumes laws: "universal_decoder_laws live D"
  shows
    "sd_node_decode D p = Some (Event t) \<longleftrightarrow>
       t \<in> live \<and>
       p = abi_event_list_item_ptr (sd_tcb_ptr D t)"
proof
  assume decoded: "sd_node_decode D p = Some (Event t)"
  from laws have inverse:
    "\<forall>q u. sd_node_decode D q = Some (Event u) \<longrightarrow>
       u \<in> live \<and>
       q = abi_event_list_item_ptr (sd_tcb_ptr D u)"
    unfolding universal_decoder_laws_def by blast
  show
    "t \<in> live \<and>
     p = abi_event_list_item_ptr (sd_tcb_ptr D t)"
    using inverse decoded by blast
next
  assume rhs:
    "t \<in> live \<and>
     p = abi_event_list_item_ptr (sd_tcb_ptr D t)"
  from laws have forward:
    "\<forall>u\<in>live.
       sd_node_decode D
         (abi_event_list_item_ptr (sd_tcb_ptr D u)) =
           Some (Event u)"
    unfolding universal_decoder_laws_def by blast
  show "sd_node_decode D p = Some (Event t)"
    using forward rhs by blast
qed

definition universal_scheduler_geometry ::
  "'tid set \<Rightarrow> 'tid scheduler_decode \<Rightarrow> bool"
where
  "universal_scheduler_geometry live D \<longleftrightarrow>
     universal_tcb_geometry live D \<and>
     universal_decoder_laws live D"

theorem universal_geometry_scheduler_decode_rel:
  assumes geometry: "universal_scheduler_geometry live D"
      and live_eq: "sa_live a = live"
  shows "scheduler_decode_rel D a"
proof -
  from geometry have storage: "universal_tcb_geometry live D"
    and laws: "universal_decoder_laws live D"
    by (simp_all add: universal_scheduler_geometry_def)
  from storage have injective: "inj_on (sd_tcb_ptr D) live"
    by (simp add: universal_tcb_geometry_def)
  from laws have forward:
    "\<forall>t\<in>live.
       sd_tcb_decode D (sd_tcb_ptr D t) = Some t \<and>
       sd_node_decode D
         (abi_generic_list_item_ptr (sd_tcb_ptr D t)) =
           Some (Generic t) \<and>
       sd_node_decode D
         (abi_event_list_item_ptr (sd_tcb_ptr D t)) =
           Some (Event t)"
    unfolding universal_decoder_laws_def by blast
  from laws have tcb_inverse:
    "\<forall>p t. sd_tcb_decode D p = Some t \<longrightarrow>
       t \<in> live \<and> p = sd_tcb_ptr D t"
    unfolding universal_decoder_laws_def by blast
  from laws have generic_inverse:
    "\<forall>p t. sd_node_decode D p = Some (Generic t) \<longrightarrow>
       p = abi_generic_list_item_ptr (sd_tcb_ptr D t)"
    unfolding universal_decoder_laws_def by blast
  from laws have event_inverse:
    "\<forall>p t. sd_node_decode D p = Some (Event t) \<longrightarrow>
       p = abi_event_list_item_ptr (sd_tcb_ptr D t)"
    unfolding universal_decoder_laws_def by blast
  from laws have owner_live:
    "\<forall>p n. sd_node_decode D p = Some n \<longrightarrow>
       node_owner n \<in> live"
    unfolding universal_decoder_laws_def by blast
  show ?thesis
    unfolding scheduler_decode_rel_def
    apply (intro conjI)
    subgoal using injective live_eq by simp
    subgoal using forward live_eq by simp
    subgoal using tcb_inverse live_eq by blast
    subgoal using generic_inverse by blast
    subgoal using event_inverse by blast
    subgoal using owner_live live_eq by blast
    done
qed

end
