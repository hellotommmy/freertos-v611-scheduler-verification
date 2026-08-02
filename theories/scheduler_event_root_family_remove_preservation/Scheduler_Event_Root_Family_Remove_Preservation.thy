theory Scheduler_Event_Root_Family_Remove_Preservation
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Event_Root_Family_Remove_Root_Rep.Scheduler_Event_Root_Family_Remove_Root_Rep"
begin

theorem scheduler_event_root_family_remove_preserved:
  assumes rel:
      "scheduler_event_root_family_rel
         D h roots pending raw_fam abs_fam live K_E"
    and owner: "owner \<in> roots"
    and removed_live: "t \<in> live"
    and member:
      "event_item_raw_ptr D t \<in> set (ring (raw_fam owner))"
  shows
    "scheduler_event_root_family_rel D
       (raw_remove_concrete_heap h (event_item_raw_ptr D t)) roots pending
       (event_remove_raw_family raw_fam owner (event_item_raw_ptr D t))
       (event_remove_abs_family abs_fam owner t) live K_E"
proof (rule scheduler_event_root_family_relI)
  show
    "scheduler_family_pre_rel
       (raw_remove_concrete_heap h (event_item_raw_ptr D t)) roots
       (event_remove_raw_family raw_fam owner (event_item_raw_ptr D t))
       live D"
    by (rule scheduler_event_root_family_remove_pre_rel[
          OF rel owner removed_live member])
next
  show "universal_decoder_laws live D"
    by (rule scheduler_event_root_family_decoder_lawsD[OF rel])
next
  show "pending \<in> roots"
    by (rule scheduler_event_root_family_pending_rootD[OF rel])
next
  fix lp
  assume root: "lp \<in> roots"
  show
    "event_family_root_rep D
       (event_remove_raw_family raw_fam owner (event_item_raw_ptr D t))
       (event_remove_abs_family abs_fam owner t) live lp"
    by (rule scheduler_event_root_family_remove_root_rep[
          OF rel owner removed_live member root])
next
  show
    "event_family_container_rep D
       (raw_remove_concrete_heap h (event_item_raw_ptr D t)) roots
       (event_remove_raw_family raw_fam owner (event_item_raw_ptr D t))
       live"
    by (rule scheduler_event_root_family_remove_container_rep[
          OF rel owner removed_live member])
next
  show
    "event_family_key_rep D
       (raw_remove_concrete_heap h (event_item_raw_ptr D t)) roots
       (event_remove_raw_family raw_fam owner (event_item_raw_ptr D t))
       (event_remove_abs_family abs_fam owner t) live K_E"
    by (rule scheduler_event_root_family_remove_key_rep[
          OF rel owner removed_live member])
qed

corollary scheduler_event_root_family_remove_post_observations:
  assumes rel:
      "scheduler_event_root_family_rel
         D h roots pending raw_fam abs_fam live K_E"
    and owner: "owner \<in> roots"
    and removed_live: "t \<in> live"
    and member:
      "event_item_raw_ptr D t \<in> set (ring (raw_fam owner))"
  defines
    "h' \<equiv> raw_remove_concrete_heap h (event_item_raw_ptr D t)"
    and "raw_fam' \<equiv>
      event_remove_raw_family raw_fam owner (event_item_raw_ptr D t)"
    and "abs_fam' \<equiv> event_remove_abs_family abs_fam owner t"
  shows
    "scheduler_event_root_family_rel
       D h' roots pending raw_fam' abs_fam' live K_E \<and>
     pvContainer_C (h_val h' (event_item_raw_ptr D t)) = NULL \<and>
     raw_key_at h' (event_item_raw_ptr D t) = K_E t \<and>
     raw_family_members roots raw_fam' (event_item_raw_ptr D t) = {}"
proof -
  have post:
    "scheduler_event_root_family_rel
       D h' roots pending raw_fam' abs_fam' live K_E"
    unfolding h'_def raw_fam'_def abs_fam'_def
    by (rule scheduler_event_root_family_remove_preserved[
          OF rel owner removed_live member])
  have null:
    "pvContainer_C (h_val h' (event_item_raw_ptr D t)) = NULL"
    using scheduler_event_root_family_remove_item_effect[
      OF rel owner removed_live member]
    by (simp add: h'_def)
  have key: "raw_key_at h' (event_item_raw_ptr D t) = K_E t"
    using scheduler_event_root_family_remove_item_effect[
      OF rel owner removed_live member]
    by (simp add: h'_def)
  have absent:
    "raw_family_members roots raw_fam' (event_item_raw_ptr D t) = {}"
    unfolding raw_fam'_def
    by (rule scheduler_event_root_family_remove_members_empty[
          OF rel owner removed_live member])
  show ?thesis using post null key absent by simp
qed

end
