theory Scheduler_Event_Root_Family_Remove_Payload_Frame
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Event_Root_Family_Remove_Pre_Rel.Scheduler_Event_Root_Family_Remove_Pre_Rel"
begin

lemma scheduler_event_root_family_remove_other_payload_frame:
  assumes rel:
      "scheduler_event_root_family_rel
         D h roots pending raw_fam abs_fam live K_E"
    and owner: "owner \<in> roots"
    and removed_live: "t \<in> live"
    and other_live: "u \<in> live"
    and different: "u \<noteq> t"
    and member:
      "event_item_raw_ptr D t \<in> set (ring (raw_fam owner))"
  shows
    "raw_key_at
       (raw_remove_concrete_heap h (event_item_raw_ptr D t))
       (event_item_raw_ptr D u) =
       raw_key_at h (event_item_raw_ptr D u) \<and>
     pvContainer_C
       (h_val (raw_remove_concrete_heap h (event_item_raw_ptr D t))
         (event_item_raw_ptr D u)) =
       pvContainer_C (h_val h (event_item_raw_ptr D u))"
proof (cases
    "event_item_raw_ptr D u \<in> set (ring (raw_fam owner))")
  case True
  have new:
    "raw_key_at
       (raw_remove_concrete_heap h (event_item_raw_ptr D t))
       (event_item_raw_ptr D u) = K_E u \<and>
     pvContainer_C
       (h_val (raw_remove_concrete_heap h (event_item_raw_ptr D t))
         (event_item_raw_ptr D u)) =
       PTR_COERCE(xLIST_C \<rightarrow> unit) owner"
    by (rule scheduler_event_root_family_remove_remaining_payload_frame[
          OF rel owner removed_live other_live different member True])
  have old_key: "raw_key_at h (event_item_raw_ptr D u) = K_E u"
    by (rule scheduler_event_root_family_physical_keyD[OF rel other_live])
  have old_container:
    "pvContainer_C (h_val h (event_item_raw_ptr D u)) =
       PTR_COERCE(xLIST_C \<rightarrow> unit) owner"
    using scheduler_event_root_family_container_iff[
      OF rel other_live owner] True by simp
  show ?thesis using new old_key old_container by simp
next
  case False
  have pre: "scheduler_family_pre_rel h roots raw_fam live D"
    by (rule scheduler_event_root_family_preD[OF rel])
  have managed:
    "event_item_raw_ptr D u \<in> universal_managed_nodes live D"
    using other_live
    by (auto simp: event_item_raw_ptr_def universal_managed_nodes_def)
  have byte_frame:
    "\<forall>a\<in>raw_item_region (event_item_raw_ptr D u).
       raw_remove_concrete_heap h (event_item_raw_ptr D t) a = h a"
    using raw_remove_family_sibling_item_priority_byte_frame[
      OF pre owner member managed False other_live] by blast
  have item_same:
    "h_val (raw_remove_concrete_heap h (event_item_raw_ptr D t))
       (event_item_raw_ptr D u) =
     h_val h (event_item_raw_ptr D u)"
  proof (rule delay_h_val_region_cong)
    fix a
    assume address:
      "a \<in> {ptr_val (event_item_raw_ptr D u)
        ..+size_of TYPE(xLIST_ITEM_C)}"
    show "raw_remove_concrete_heap h (event_item_raw_ptr D t) a = h a"
      using byte_frame address by (simp add: raw_item_region_def)
  qed
  show ?thesis using item_same by (simp add: raw_key_at_def)
qed

lemma scheduler_event_root_family_remove_membership_frame:
  assumes rel:
      "scheduler_event_root_family_rel
         D h roots pending raw_fam abs_fam live K_E"
    and removed_live: "t \<in> live"
    and other_live: "u \<in> live"
    and different: "u \<noteq> t"
  shows
    "event_item_raw_ptr D u \<in>
       set (ring (event_remove_raw_family raw_fam owner
         (event_item_raw_ptr D t) lp)) \<longleftrightarrow>
     event_item_raw_ptr D u \<in> set (ring (raw_fam lp))"
proof -
  have pointer_different:
    "event_item_raw_ptr D u \<noteq> event_item_raw_ptr D t"
  proof
    assume equal:
      "event_item_raw_ptr D u = event_item_raw_ptr D t"
    have "u = t"
      by (rule scheduler_event_root_family_event_item_ptr_inj[
            OF rel other_live removed_live equal])
    with different show False by contradiction
  qed
  show ?thesis
    by (rule event_remove_raw_family_membership_frame[OF pointer_different])
qed

end
