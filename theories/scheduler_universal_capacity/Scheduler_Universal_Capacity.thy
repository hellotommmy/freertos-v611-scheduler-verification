theory Scheduler_Universal_Capacity
  imports
    "EAL6_FreeRTOS_V611_List_Raw_R5_Interface.List_V611_Raw_R5_Interface"
begin

text \<open>
  The insert-count side condition is not an independent environmental
  assumption.  A well-formed raw list already uses pairwise distinct 32-bit
  item pointers for its sentinel and ring, and a fresh item supplies one more
  distinct pointer.  The finite address space therefore leaves the current
  ring strictly below the largest representable 32-bit count.
\<close>

lemma raw_node_id_card:
  "CARD(raw_node_id) = 2 ^ 32"
proof -
  have image_UNIV:
    "(UNIV :: raw_node_id set) =
       (Ptr :: addr \<Rightarrow> raw_node_id) ` (UNIV :: addr set)"
    by auto
  have image_card:
    "card ((Ptr :: addr \<Rightarrow> raw_node_id) ` (UNIV :: addr set)) =
       card (UNIV :: addr set)"
    by (rule card_image) (simp add: inj_on_def)
  have ptr_card: "CARD(raw_node_id) = CARD(addr)"
  proof (subst image_UNIV)
    show "card ((Ptr :: addr \<Rightarrow> raw_node_id) ` UNIV) = CARD(addr)"
      by (rule image_card)
  qed
  show ?thesis
    using ptr_card by (simp add: card_word)
qed

lemma distinct_raw_node_ids_length_bound:
  assumes distinct: "distinct (ps :: raw_node_id list)"
  shows "length ps \<le> 2 ^ 32"
proof -
  have subset: "set ps \<subseteq> (UNIV :: raw_node_id set)"
    by simp
  have finite_nodes: "finite (UNIV :: raw_node_id set)"
    by simp
  have "card (set ps) \<le> card (UNIV :: raw_node_id set)"
    by (rule card_mono[OF finite_nodes subset])
  then show ?thesis
    using distinct
    by (simp add: distinct_card raw_node_id_card)
qed

theorem raw_xlist_rel_fresh_count_can_increment:
  assumes rel: "raw_xlist_rel h lp xs"
    and fresh: "raw_fresh_for_insert lp (ring xs) p"
  shows "raw_count_can_increment xs"
proof -
  have cycle_distinct:
    "distinct (raw_end_item lp # ring xs)"
    by (rule raw_xlist_rel_distinct_cycle_nodes[OF rel])
  have fresh_end: "p \<noteq> raw_end_item lp"
    using fresh by (simp add: raw_fresh_for_insert_def)
  have fresh_ring: "p \<notin> set (ring xs)"
    using fresh by (simp add: raw_fresh_for_insert_def)
  have all_distinct:
    "distinct (p # raw_end_item lp # ring xs)"
    using cycle_distinct fresh_end fresh_ring by simp
  have address_bound:
    "length (p # raw_end_item lp # ring xs) \<le> 2 ^ 32"
    by (rule distinct_raw_node_ids_length_bound[OF all_distinct])
  have one_more_below_address_space:
    "length (ring xs) + 1 < 2 ^ 32"
    using address_bound by simp
  have count_bound:
    "length (ring xs) < 2 ^ 32 - 1"
    using one_more_below_address_space
    by (simp only: less_diff_conv)
  show ?thesis
    using count_bound
    by (simp add: raw_count_can_increment_def unat_minus_one_word)
qed

end
