theory Scheduler_Event_Root_Family_Remove_Physical
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Event_Root_Family_Remove_Payload_Frame.Scheduler_Event_Root_Family_Remove_Payload_Frame"
begin

lemma scheduler_event_root_family_remove_members_empty:
  assumes rel:
      "scheduler_event_root_family_rel
         D h roots pending raw_fam abs_fam live K_E"
    and owner: "owner \<in> roots"
    and removed_live: "t \<in> live"
    and member:
      "event_item_raw_ptr D t \<in> set (ring (raw_fam owner))"
  shows
    "raw_family_members roots
       (event_remove_raw_family raw_fam owner (event_item_raw_ptr D t))
       (event_item_raw_ptr D t) = {}"
proof -
  let ?p = "event_item_raw_ptr D t"
  let ?h' = "raw_remove_concrete_heap h ?p"
  let ?fam' = "event_remove_raw_family raw_fam owner ?p"
  have pre_family: "raw_family_rel h roots raw_fam"
    using scheduler_event_root_family_preD[OF rel]
    by (simp add: scheduler_family_pre_rel_def)
  have unique: "raw_family_members roots raw_fam ?p = {owner}"
    by (rule scheduler_event_root_family_member_singletonD[
          OF rel owner member])
  have post_pre: "scheduler_family_pre_rel ?h' roots ?fam' live D"
    by (rule scheduler_event_root_family_remove_pre_rel[
          OF rel owner removed_live member])
  have target_post:
    "raw_xlist_rel ?h' owner (list_remove_abs ?p (raw_fam owner))"
    using post_pre owner
    by (auto simp: scheduler_family_pre_rel_def raw_family_rel_def
        event_remove_raw_family_def)
  have other_post:
    "\<And>lp. lp \<in> roots \<Longrightarrow> lp \<noteq> owner \<Longrightarrow>
      raw_xlist_rel ?h' lp (raw_fam lp)"
    using post_pre
    by (auto simp: scheduler_family_pre_rel_def raw_family_rel_def
        event_remove_raw_family_def)
  have removed_null:
    "pvContainer_C (h_val ?h' ?p) = NULL"
    using scheduler_event_root_family_remove_item_effect[
      OF rel owner removed_live member] by simp
  have unlinked:
    "raw_family_globally_unlinked ?h' roots ?fam' ?p"
    using raw_family_remove_owner_globally_unlinked[
      OF pre_family owner unique target_post other_post removed_null]
    by (simp add: event_remove_raw_family_def)
  show ?thesis
    using unlinked by (simp add: raw_family_globally_unlinked_def)
qed

end
