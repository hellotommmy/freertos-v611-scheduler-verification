theory Scheduler_Universal_Ordered_Insert_Composition
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Universal_Capacity.Scheduler_Universal_Capacity"
    "EAL6_FreeRTOS_V611_Scheduler_Ordered_Insert_General_Refinement.Scheduler_Ordered_Insert_General_Refinement"
begin

text \<open>
  Composition discharges the count-capacity side condition from the raw list
  relation and freshness already required by ordered insertion.  Consequently
  the public transformer theorem has no independent capacity assumption.
\<close>

theorem raw_ordered_insert_general_transformer_refines_unconditionally:
  assumes ordered: "raw_ordered_xlist_rel h lp xs"
    and fresh: "raw_fresh_for_insert lp (ring xs) p"
  shows
    "raw_ordered_xlist_rel
       (raw_ordered_insert_general_heap h lp xs p) lp
       (list_insert_ordered_abs p (raw_key_at h p) xs)"
proof -
  have rel: "raw_xlist_rel h lp xs"
    using ordered by (simp add: raw_ordered_xlist_rel_def)
  have capacity: "raw_count_can_increment xs"
    by (rule raw_xlist_rel_fresh_count_can_increment[OF rel fresh])
  show ?thesis
    by (rule raw_ordered_insert_general_transformer_refines[
          OF ordered fresh capacity])
qed

end
