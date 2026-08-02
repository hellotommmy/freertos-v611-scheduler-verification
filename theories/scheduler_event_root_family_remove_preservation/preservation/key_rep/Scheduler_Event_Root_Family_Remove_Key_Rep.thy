theory Scheduler_Event_Root_Family_Remove_Key_Rep
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Event_Root_Family_Remove_Container_Rep.Scheduler_Event_Root_Family_Remove_Container_Rep"
begin

lemma scheduler_event_root_family_remove_key_rep:
  assumes rel:
      "scheduler_event_root_family_rel
         D h roots pending raw_fam abs_fam live K_E"
    and owner: "owner \<in> roots"
    and removed_live: "t \<in> live"
    and member:
      "event_item_raw_ptr D t \<in> set (ring (raw_fam owner))"
  shows
    "event_family_key_rep D
       (raw_remove_concrete_heap h (event_item_raw_ptr D t)) roots
       (event_remove_raw_family raw_fam owner (event_item_raw_ptr D t))
       (event_remove_abs_family abs_fam owner t) live K_E"
proof -
  let ?p = "event_item_raw_ptr D t"
  let ?h' = "raw_remove_concrete_heap h ?p"
  let ?raw' = "event_remove_raw_family raw_fam owner ?p"
  let ?abs' = "event_remove_abs_family abs_fam owner t"
  have physical:
    "\<forall>u\<in>live. raw_key_at ?h' (event_item_raw_ptr D u) = K_E u"
  proof (intro ballI)
    fix u
    assume u_live: "u \<in> live"
    show "raw_key_at ?h' (event_item_raw_ptr D u) = K_E u"
    proof (cases "u = t")
      case True
      show ?thesis
        using scheduler_event_root_family_remove_item_effect[
          OF rel owner removed_live member] True by simp
    next
      case False
      have frame:
        "raw_key_at ?h' (event_item_raw_ptr D u) =
         raw_key_at h (event_item_raw_ptr D u)"
        using scheduler_event_root_family_remove_other_payload_frame[
          OF rel owner removed_live u_live False member] by simp
      have old: "raw_key_at h (event_item_raw_ptr D u) = K_E u"
        by (rule scheduler_event_root_family_physical_keyD[OF rel u_live])
      show ?thesis using frame old by simp
    qed
  qed
  have abstract:
    "\<forall>lp\<in>roots. \<forall>u\<in>live.
       Event u \<in> set (ring (?abs' lp)) \<longrightarrow>
       item_key (?abs' lp) (Event u) = K_E u"
  proof (intro ballI impI)
    fix lp
    assume lp_root: "lp \<in> roots"
    fix u
    assume u_live: "u \<in> live"
      and u_member: "Event u \<in> set (ring (?abs' lp))"
    show "item_key (?abs' lp) (Event u) = K_E u"
    proof (cases "lp = owner")
      case True
      have removed_member:
        "Event u \<in> set (remove1 (Event t) (ring (abs_fam owner)))"
        using u_member True
        by (simp add: event_remove_abs_family_def list_remove_abs_def)
      have old_member: "Event u \<in> set (ring (abs_fam owner))"
        by (rule set_remove1_subset[THEN subsetD, OF removed_member])
      have old_key: "item_key (abs_fam owner) (Event u) = K_E u"
        by (rule scheduler_event_root_family_abstract_keyD[
              OF rel u_live owner old_member])
      show ?thesis
        using old_key True
        by (simp add: event_remove_abs_family_def list_remove_abs_def)
    next
      case False
      have old_member: "Event u \<in> set (ring (abs_fam lp))"
        using u_member False by (simp add: event_remove_abs_family_def)
      have old_key: "item_key (abs_fam lp) (Event u) = K_E u"
        by (rule scheduler_event_root_family_abstract_keyD[
              OF rel u_live lp_root old_member])
      show ?thesis using old_key False
        by (simp add: event_remove_abs_family_def)
    qed
  qed
  show ?thesis
    using physical abstract by (simp add: event_family_key_rep_def)
qed

end
