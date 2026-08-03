theory Scheduler_Resume_Generated_Event_Heap_Frame
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Generic_Unlinked_Family.Scheduler_Resume_Generated_Generic_Unlinked_Family"
begin

lemma scheduler_event_root_family_heap_frameI:
  assumes rel:
      "scheduler_event_root_family_rel D h roots pending raw_fam
        abs_fam live K_E"
    and root_frame:
      "\<And>lp address. lp \<in> roots \<Longrightarrow>
        address \<in> raw_xlist_storage lp (raw_fam lp) \<Longrightarrow>
        h' address = h address"
    and item_frame:
      "\<And>t. t \<in> live \<Longrightarrow>
        h_val h' (event_item_raw_ptr D t) =
          h_val h (event_item_raw_ptr D t)"
  shows
    "scheduler_event_root_family_rel D h' roots pending raw_fam
       abs_fam live K_E"
proof (rule scheduler_event_root_family_relI)
  have old_pre: "scheduler_family_pre_rel h roots raw_fam live D"
    by (rule scheduler_event_root_family_preD[OF rel])
  have new_family: "raw_family_rel h' roots raw_fam"
    unfolding raw_family_rel_def
  proof (intro conjI ballI)
    show "finite roots"
      using old_pre
      by (simp add: scheduler_family_pre_rel_def raw_family_rel_def)
  next
    fix lp
    assume root: "lp \<in> roots"
    have old: "raw_xlist_rel h lp (raw_fam lp)"
      by (rule scheduler_event_root_family_raw_rootD[OF rel root])
    show "raw_xlist_rel h' lp (raw_fam lp)"
      by (rule delay_raw_xlist_rel_storage_frame[OF old])
         (use root root_frame in blast)
  qed
  show "scheduler_family_pre_rel h' roots raw_fam live D"
    using old_pre new_family by (simp add: scheduler_family_pre_rel_def)
next
  show "universal_decoder_laws live D"
    by (rule scheduler_event_root_family_decoder_lawsD[OF rel])
next
  show "pending \<in> roots"
    by (rule scheduler_event_root_family_pending_rootD[OF rel])
next
  fix lp
  assume "lp \<in> roots"
  then show "event_family_root_rep D raw_fam abs_fam live lp"
    by (rule scheduler_event_root_family_root_repD[OF rel])
next
  have old:
    "event_family_container_rep D h roots raw_fam live"
    using rel by (simp add: scheduler_event_root_family_rel_def)
  have old_faithful:
    "raw_family_container_faithful_on h roots raw_fam
       (event_item_raw_set live D)"
    using old by (simp add: event_family_container_rep_def)
  have old_members:
    "\<And>t lp. t \<in> live \<Longrightarrow> lp \<in> roots \<Longrightarrow>
      event_item_raw_ptr D t \<in> set (ring (raw_fam lp)) \<longleftrightarrow>
      pvContainer_C (h_val h (event_item_raw_ptr D t)) =
        PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
    using old by (auto simp: event_family_container_rep_def)
  have point_frame:
    "\<And>p. p \<in> event_item_raw_set live D \<Longrightarrow>
      h_val h' p = h_val h p"
  proof -
    fix p
    assume "p \<in> event_item_raw_set live D"
    then obtain t where live: "t \<in> live"
        and p: "p = event_item_raw_ptr D t"
      by (auto simp: event_item_raw_set_def)
    show "h_val h' p = h_val h p"
      using item_frame[OF live] p by simp
  qed
  show "event_family_container_rep D h' roots raw_fam live"
    unfolding event_family_container_rep_def
  proof (intro conjI)
    show
      "raw_family_container_faithful_on h' roots raw_fam
         (event_item_raw_set live D)"
      unfolding raw_family_container_faithful_on_def
    proof (intro conjI)
      show
        "\<forall>p\<in>event_item_raw_set live D.
          (pvContainer_C (h_val h' p) = NULL) =
            (raw_family_members roots raw_fam p = {})"
      proof (intro ballI)
        fix p
        assume managed: "p \<in> event_item_raw_set live D"
        have old_null:
          "(pvContainer_C (h_val h p) = NULL) =
            (raw_family_members roots raw_fam p = {})"
          using old_faithful managed
          by (simp add: raw_family_container_faithful_on_def)
        show
          "(pvContainer_C (h_val h' p) = NULL) =
            (raw_family_members roots raw_fam p = {})"
          using old_null point_frame[OF managed] by simp
      qed
    next
      show
        "\<forall>lp\<in>roots. \<forall>p\<in>event_item_raw_set live D \<inter>
          set (ring (raw_fam lp)).
          pvContainer_C (h_val h' p) =
            PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
      proof (intro ballI)
        fix lp
        assume root: "lp \<in> roots"
        fix p
        assume member:
          "p \<in> event_item_raw_set live D \<inter>
            set (ring (raw_fam lp))"
        have old_container:
          "pvContainer_C (h_val h p) =
            PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
          using old_faithful root member
          by (auto simp: raw_family_container_faithful_on_def)
        show
          "pvContainer_C (h_val h' p) =
            PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
          using old_container point_frame[of p] member by auto
      qed
    qed
  next
    show
      "\<forall>t\<in>live. \<forall>lp\<in>roots.
        (event_item_raw_ptr D t \<in> set (ring (raw_fam lp))) =
          (pvContainer_C (h_val h' (event_item_raw_ptr D t)) =
            PTR_COERCE(xLIST_C \<rightarrow> unit) lp)"
    proof (intro ballI)
      fix t
      assume live: "t \<in> live"
      fix lp
      assume root: "lp \<in> roots"
      show
        "(event_item_raw_ptr D t \<in> set (ring (raw_fam lp))) =
          (pvContainer_C (h_val h' (event_item_raw_ptr D t)) =
            PTR_COERCE(xLIST_C \<rightarrow> unit) lp)"
        using old_members[OF live root] item_frame[OF live] by simp
    qed
  qed
next
  have old: "event_family_key_rep D h roots raw_fam abs_fam live K_E"
    using rel by (simp add: scheduler_event_root_family_rel_def)
  show "event_family_key_rep D h' roots raw_fam abs_fam live K_E"
    unfolding event_family_key_rep_def
  proof (intro conjI)
    show
      "\<forall>t\<in>live. raw_key_at h' (event_item_raw_ptr D t) = K_E t"
    proof (intro ballI)
      fix t
      assume live: "t \<in> live"
      have old_key: "raw_key_at h (event_item_raw_ptr D t) = K_E t"
        using old live by (simp add: event_family_key_rep_def)
      show "raw_key_at h' (event_item_raw_ptr D t) = K_E t"
        using old_key item_frame[OF live]
        by (simp add: raw_key_at_def)
    qed
  next
    show
      "\<forall>lp\<in>roots. \<forall>t\<in>live.
        Event t \<in> set (ring (abs_fam lp)) \<longrightarrow>
          item_key (abs_fam lp) (Event t) = K_E t"
      using old by (simp add: event_family_key_rep_def)
  qed
qed

end
