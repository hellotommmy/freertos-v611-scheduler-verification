theory Scheduler_Event_Root_Family_Remove_Root_Rep
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Event_Root_Family_Remove_Key_Rep.Scheduler_Event_Root_Family_Remove_Key_Rep"
begin

lemma scheduler_event_root_family_remove_root_rep:
  assumes rel:
      "scheduler_event_root_family_rel
         D h roots pending raw_fam abs_fam live K_E"
    and owner: "owner \<in> roots"
    and removed_live: "t \<in> live"
    and member:
      "event_item_raw_ptr D t \<in> set (ring (raw_fam owner))"
    and root: "lp \<in> roots"
  shows
    "event_family_root_rep D
       (event_remove_raw_family raw_fam owner (event_item_raw_ptr D t))
       (event_remove_abs_family abs_fam owner t) live lp"
proof (cases "lp = owner")
  case True
  have old_root: "event_family_root_rep D raw_fam abs_fam live owner"
    by (rule scheduler_event_root_family_root_repD[OF rel owner])
  have raw_nodes:
    "set (ring (list_remove_abs (event_item_raw_ptr D t)
       (raw_fam owner))) \<subseteq> event_item_raw_set live D"
  proof -
    have removed_subset:
      "set (ring (list_remove_abs (event_item_raw_ptr D t)
         (raw_fam owner))) \<subseteq> set (ring (raw_fam owner))"
      using set_remove1_subset[
        of "event_item_raw_ptr D t" "ring (raw_fam owner)"]
      by (simp add: list_remove_abs_def)
    have old_subset:
      "set (ring (raw_fam owner)) \<subseteq> event_item_raw_set live D"
      using old_root by (simp add: event_family_root_rep_def)
    show ?thesis using removed_subset old_subset by (rule subset_trans)
  qed
  have old_relabel:
    "xlist_relabel (sd_node_decode D) (raw_fam owner) (abs_fam owner)"
    using old_root by (simp add: event_family_root_rep_def)
  have raw_wf: "xlist_wf (raw_fam owner)"
    using scheduler_event_root_family_raw_rootD[OF rel owner]
    by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have abs_wf: "xlist_wf (abs_fam owner)"
    using old_root by (simp add: event_family_root_rep_def)
  have decode:
    "sd_node_decode D (event_item_raw_ptr D t) = Some (Event t)"
    by (rule scheduler_event_root_family_event_decodeD[OF rel removed_live])
  have relabel_post:
    "xlist_relabel (sd_node_decode D)
       (list_remove_abs (event_item_raw_ptr D t) (raw_fam owner))
       (list_remove_abs (Event t) (abs_fam owner))"
    by (rule xlist_relabel_remove_preserved[
          OF old_relabel raw_wf abs_wf member decode])
  have abs_member: "Event t \<in> set (ring (abs_fam owner))"
    using scheduler_event_root_family_member_iff[
      OF rel removed_live owner] member by simp
  have wf_post: "xlist_wf (list_remove_abs (Event t) (abs_fam owner))"
    by (rule list_remove_preserves_wf[OF abs_wf abs_member])
  have event_post: "event_ring (list_remove_abs (Event t) (abs_fam owner))"
    by (rule event_ring_remove_preserved)
       (use old_root in \<open>simp add: event_family_root_rep_def\<close>)
  show ?thesis
    using raw_nodes relabel_post wf_post event_post True
    by (simp add: event_family_root_rep_def event_remove_raw_family_def
        event_remove_abs_family_def)
next
  case False
  have old_root: "event_family_root_rep D raw_fam abs_fam live lp"
    by (rule scheduler_event_root_family_root_repD[OF rel root])
  have raw_frame:
    "event_remove_raw_family raw_fam owner (event_item_raw_ptr D t) lp =
       raw_fam lp"
    using False by (simp add: event_remove_raw_family_def)
  have abs_frame:
    "event_remove_abs_family abs_fam owner t lp = abs_fam lp"
    using False by (simp add: event_remove_abs_family_def)
  show ?thesis
    using old_root raw_frame abs_frame
    by (simp add: event_family_root_rep_def)
qed

end
