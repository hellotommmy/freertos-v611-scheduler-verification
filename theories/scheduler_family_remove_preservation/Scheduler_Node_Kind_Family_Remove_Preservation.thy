theory Scheduler_Node_Kind_Family_Remove_Preservation
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Family_Remove_Core.Scheduler_Family_Remove_Core"
begin

definition scheduler_node_kind_family_remove_post ::
  "'tid scheduler_decode \<Rightarrow> heap_mem \<Rightarrow> heap_mem \<Rightarrow>
   xLIST_C ptr set \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow>
   'tid set \<Rightarrow> xLIST_C ptr \<Rightarrow> raw_node_id \<Rightarrow>
   'tid node_kind \<Rightarrow> bool"
where
  "scheduler_node_kind_family_remove_post
      D h h' roots raw_fam abs_fam live owner p n \<longleftrightarrow>
     (let raw_fam' = scheduler_family_remove_raw raw_fam owner p;
          abs_fam' = scheduler_family_remove_abs abs_fam owner n
      in scheduler_family_pre_rel h' roots raw_fam' live D \<and>
         raw_xlist_rel h' owner (list_remove_abs p (raw_fam owner)) \<and>
         (\<forall>lp\<in>roots.
            xlist_relabel (sd_node_decode D) (raw_fam' lp) (abs_fam' lp)) \<and>
         (\<forall>lp\<in>roots. xlist_wf (abs_fam' lp)) \<and>
         raw_family_globally_unlinked h' roots raw_fam' p \<and>
         raw_key_at h' p = raw_key_at h p \<and>
         pvContainer_C (h_val h' p) = NULL \<and>
         xLIST_ITEM_C.pxNext_C (h_val h' p) =
           xLIST_ITEM_C.pxNext_C (h_val h p) \<and>
         xLIST_ITEM_C.pxPrevious_C (h_val h' p) =
           xLIST_ITEM_C.pxPrevious_C (h_val h p) \<and>
         (\<forall>q\<in>universal_managed_nodes live D. q \<noteq> p \<longrightarrow>
            raw_key_at h' q = raw_key_at h q \<and>
            pvContainer_C (h_val h' q) = pvContainer_C (h_val h q)) \<and>
         (\<forall>q\<in>universal_managed_nodes live D.
            q \<notin> set (ring (raw_fam owner)) \<longrightarrow>
            (\<forall>a\<in>raw_item_region q. h' a = h a)) \<and>
         (\<forall>u\<in>live.
            (\<forall>a\<in>universal_priority_field_region (sd_tcb_ptr D u).
               h' a = h a)) \<and>
         (\<forall>lp\<in>roots. lp \<noteq> owner \<longrightarrow>
            (\<forall>a\<in>raw_xlist_storage lp (raw_fam lp). h' a = h a)))"

lemma scheduler_family_remove_relabel_preserved:
  assumes pre: "scheduler_family_pre_rel h roots raw_fam live D"
    and owner: "owner \<in> roots"
    and member: "p \<in> set (ring (raw_fam owner))"
    and relabels:
      "\<And>lp. lp \<in> roots \<Longrightarrow>
        xlist_relabel (sd_node_decode D) (raw_fam lp) (abs_fam lp)"
    and abs_wf:
      "\<And>lp. lp \<in> roots \<Longrightarrow> xlist_wf (abs_fam lp)"
    and decode: "sd_node_decode D p = Some n"
  shows
    "\<And>lp. lp \<in> roots \<Longrightarrow>
      xlist_relabel (sd_node_decode D)
        (scheduler_family_remove_raw raw_fam owner p lp)
        (scheduler_family_remove_abs abs_fam owner n lp)"
proof -
  fix lp
  assume lp_root: "lp \<in> roots"
  show
    "xlist_relabel (sd_node_decode D)
       (scheduler_family_remove_raw raw_fam owner p lp)
       (scheduler_family_remove_abs abs_fam owner n lp)"
  proof (cases "lp = owner")
    case True
    have raw: "raw_xlist_rel h owner (raw_fam owner)"
      using pre owner
      by (auto simp: scheduler_family_pre_rel_def raw_family_rel_def)
    have raw_wf: "xlist_wf (raw_fam owner)"
      using raw by (simp add: raw_xlist_rel_def raw_xlist_view_def)
    have post:
      "xlist_relabel (sd_node_decode D)
         (list_remove_abs p (raw_fam owner))
         (list_remove_abs n (abs_fam owner))"
      by (rule xlist_relabel_remove_preserved[
            OF relabels[OF owner] raw_wf abs_wf[OF owner] member decode])
    show ?thesis
      using post True
      by (simp add: scheduler_family_remove_raw_def
          scheduler_family_remove_abs_def)
  next
    case False
    show ?thesis
      using relabels[OF lp_root] False
      by (simp add: scheduler_family_remove_raw_def
          scheduler_family_remove_abs_def)
  qed
qed

lemma scheduler_family_remove_abs_wf_preserved:
  assumes owner: "owner \<in> roots"
    and member: "p \<in> set (ring (raw_fam owner))"
    and relabels:
      "\<And>lp. lp \<in> roots \<Longrightarrow>
        xlist_relabel decode_fn (raw_fam lp) (abs_fam lp)"
    and abs_wf:
      "\<And>lp. lp \<in> roots \<Longrightarrow> xlist_wf (abs_fam lp)"
    and decode: "decode_fn p = Some n"
  shows
    "\<And>lp. lp \<in> roots \<Longrightarrow>
      xlist_wf (scheduler_family_remove_abs abs_fam owner n lp)"
proof -
  have decoded_member:
    "\<exists>m\<in>set (ring (abs_fam owner)). decode_fn p = Some m"
    by (rule xlist_relabel_decoder_left_closed[
          OF relabels[OF owner] member])
  obtain m where m_member: "m \<in> set (ring (abs_fam owner))"
    and m_decode: "decode_fn p = Some m"
    using decoded_member by blast
  have m_eq: "m = n" using m_decode decode by simp
  have n_member: "n \<in> set (ring (abs_fam owner))"
    using m_member m_eq by simp
  have owner_post: "xlist_wf (list_remove_abs n (abs_fam owner))"
    by (rule list_remove_preserves_wf[OF abs_wf[OF owner] n_member])
  fix lp
  assume lp_root: "lp \<in> roots"
  show "xlist_wf (scheduler_family_remove_abs abs_fam owner n lp)"
  proof (cases "lp = owner")
    case True
    show ?thesis
      using owner_post True by (simp add: scheduler_family_remove_abs_def)
  next
    case False
    show ?thesis
      using abs_wf[OF lp_root] False
      by (simp add: scheduler_family_remove_abs_def)
  qed
qed

theorem scheduler_node_kind_family_remove_preserved:
  assumes pre: "scheduler_family_pre_rel h roots raw_fam live D"
    and owner: "owner \<in> roots"
    and member: "p \<in> set (ring (raw_fam owner))"
    and relabels:
      "\<And>lp. lp \<in> roots \<Longrightarrow>
        xlist_relabel (sd_node_decode D) (raw_fam lp) (abs_fam lp)"
    and abs_wf:
      "\<And>lp. lp \<in> roots \<Longrightarrow> xlist_wf (abs_fam lp)"
    and decode: "sd_node_decode D p = Some n"
  shows
    "scheduler_node_kind_family_remove_post
       D h (raw_remove_concrete_heap h p) roots raw_fam abs_fam live
       owner p n"
proof -
  let ?h' = "raw_remove_concrete_heap h p"
  let ?raw' = "scheduler_family_remove_raw raw_fam owner p"
  let ?abs' = "scheduler_family_remove_abs abs_fam owner n"
  have physical:
    "scheduler_family_pre_rel ?h' roots ?raw' live D \<and>
     raw_family_globally_unlinked ?h' roots ?raw' p"
    by (rule scheduler_family_remove_pre_rel_and_unlinked[
          OF pre owner member])
  have target:
    "raw_xlist_rel ?h' owner (list_remove_abs p (raw_fam owner))"
    by (rule scheduler_family_remove_owner_raw_rel[OF pre owner member])
  have labels:
    "\<forall>lp\<in>roots.
       xlist_relabel (sd_node_decode D) (?raw' lp) (?abs' lp)"
  proof (intro ballI)
    fix lp
    assume lp_root: "lp \<in> roots"
    show "xlist_relabel (sd_node_decode D) (?raw' lp) (?abs' lp)"
      apply (rule scheduler_family_remove_relabel_preserved[
          where h=h and roots=roots and raw_fam=raw_fam and live=live
            and D=D and owner=owner and p=p and abs_fam=abs_fam and n=n])
      subgoal using pre by assumption
      subgoal using owner by assumption
      subgoal using member by assumption
      subgoal using relabels by assumption
      subgoal using abs_wf by assumption
      subgoal using decode by assumption
      subgoal using lp_root by assumption
      done
  qed
  have wf:
    "\<forall>lp\<in>roots. xlist_wf (?abs' lp)"
  proof (intro ballI)
    fix lp
    assume lp_root: "lp \<in> roots"
    show "xlist_wf (?abs' lp)"
      apply (rule scheduler_family_remove_abs_wf_preserved[
          where roots=roots and raw_fam=raw_fam and owner=owner and p=p
            and decode_fn="sd_node_decode D" and abs_fam=abs_fam and n=n])
      subgoal using owner by assumption
      subgoal using member by assumption
      subgoal using relabels by assumption
      subgoal using abs_wf by assumption
      subgoal using decode by assumption
      subgoal using lp_root by assumption
      done
  qed
  have removed:
    "raw_key_at ?h' p = raw_key_at h p \<and>
     pvContainer_C (h_val ?h' p) = NULL \<and>
     xLIST_ITEM_C.pxNext_C (h_val ?h' p) =
       xLIST_ITEM_C.pxNext_C (h_val h p) \<and>
     xLIST_ITEM_C.pxPrevious_C (h_val ?h' p) =
       xLIST_ITEM_C.pxPrevious_C (h_val h p)"
    using scheduler_family_remove_item_effect[OF pre owner member]
    by simp
  have payloads:
    "\<forall>q\<in>universal_managed_nodes live D. q \<noteq> p \<longrightarrow>
       raw_key_at ?h' q = raw_key_at h q \<and>
       pvContainer_C (h_val ?h' q) = pvContainer_C (h_val h q)"
  proof (intro ballI impI)
    fix q
    assume q_managed: "q \<in> universal_managed_nodes live D"
      and q_ne: "q \<noteq> p"
    show
      "raw_key_at ?h' q = raw_key_at h q \<and>
       pvContainer_C (h_val ?h' q) = pvContainer_C (h_val h q)"
      using scheduler_family_remove_managed_payload_frame[
        OF pre owner member q_managed q_ne]
      by simp
  qed
  have nonmember_items:
    "\<forall>q\<in>universal_managed_nodes live D.
       q \<notin> set (ring (raw_fam owner)) \<longrightarrow>
       (\<forall>a\<in>raw_item_region q. ?h' a = h a)"
  proof (intro ballI impI)
    fix q a
    assume q_managed: "q \<in> universal_managed_nodes live D"
      and q_nonmember: "q \<notin> set (ring (raw_fam owner))"
      and address: "a \<in> raw_item_region q"
    show "?h' a = h a"
      using scheduler_family_remove_nonmember_item_byte_frame[
          OF pre owner member q_managed q_nonmember]
        address
      by blast
  qed
  have priorities:
    "\<forall>u\<in>live.
       (\<forall>a\<in>universal_priority_field_region (sd_tcb_ptr D u).
          ?h' a = h a)"
  proof (intro ballI)
    fix u a
    assume u_live: "u \<in> live"
      and address:
        "a \<in> universal_priority_field_region (sd_tcb_ptr D u)"
    show "?h' a = h a"
      using scheduler_family_remove_priority_byte_frame[
          OF pre owner member u_live]
        address
      by blast
  qed
  have non_targets:
    "\<forall>lp\<in>roots. lp \<noteq> owner \<longrightarrow>
       (\<forall>a\<in>raw_xlist_storage lp (raw_fam lp). ?h' a = h a)"
  proof (intro ballI impI)
    fix lp a
    assume lp_root: "lp \<in> roots" and different: "lp \<noteq> owner"
      and address: "a \<in> raw_xlist_storage lp (raw_fam lp)"
    show "?h' a = h a"
      by (rule raw_remove_family_non_target_byte_frame[
            OF pre owner lp_root _ member address])
         (use different in auto)
  qed
  show ?thesis
    using physical target labels wf removed payloads nonmember_items
      priorities non_targets
    by (simp add: scheduler_node_kind_family_remove_post_def Let_def)
qed

theorem scheduler_node_kind_family_remove_container_faithful:
  assumes pre: "scheduler_family_pre_rel h roots raw_fam live D"
    and faithful:
      "raw_family_container_faithful_on h roots raw_fam
         (universal_managed_nodes live D)"
    and owner: "owner \<in> roots"
    and member: "p \<in> set (ring (raw_fam owner))"
  shows
    "raw_family_container_faithful_on (raw_remove_concrete_heap h p) roots
       (scheduler_family_remove_raw raw_fam owner p)
       (universal_managed_nodes live D)"
  by (rule scheduler_family_remove_container_faithful_on_preserved[
        OF pre faithful owner member])

text \<open>
  This is the Gate-L bridge: the generated C body is symbolically executed by
  raw_vListRemove_general_heap_effect, while every family-wide fact is a pure
  projection of the kind-agnostic theorem above.
\<close>

theorem scheduler_vListRemove_node_kind_family_preserved:
  assumes pre:
      "scheduler_family_pre_rel (hrs_mem (t_hrs_' s)) roots
         raw_fam live D"
    and owner: "owner \<in> roots"
    and member: "p \<in> set (ring (raw_fam owner))"
    and relabels:
      "\<And>lp. lp \<in> roots \<Longrightarrow>
        xlist_relabel (sd_node_decode D) (raw_fam lp) (abs_fam lp)"
    and abs_wf:
      "\<And>lp. lp \<in> roots \<Longrightarrow> xlist_wf (abs_fam lp)"
    and decode: "sd_node_decode D p = Some n"
  shows
    "vListRemove' p \<bullet> s
     \<lbrace>\<lambda>r t. r = Result () \<and>
       scheduler_node_kind_family_remove_post D
         (hrs_mem (t_hrs_' s)) (hrs_mem (t_hrs_' t)) roots
         raw_fam abs_fam live owner p n
     \<rbrace>"
proof -
  have raw: "raw_xlist_rel (hrs_mem (t_hrs_' s)) owner (raw_fam owner)"
    using pre owner
    by (auto simp: scheduler_family_pre_rel_def raw_family_rel_def)
  note heap = raw_vListRemove_general_heap_effect[OF raw member]
  have pure:
    "scheduler_node_kind_family_remove_post D
       (hrs_mem (t_hrs_' s))
       (raw_remove_concrete_heap (hrs_mem (t_hrs_' s)) p) roots
       raw_fam abs_fam live owner p n"
    by (rule scheduler_node_kind_family_remove_preserved[
          OF pre owner member relabels abs_wf decode])
  show ?thesis
    apply (rule runs_to_weaken[OF heap])
    using pure by auto
qed

definition scheduler_family_generic_raw_ptr ::
  "'tid scheduler_decode \<Rightarrow> 'tid \<Rightarrow> raw_node_id"
where
  "scheduler_family_generic_raw_ptr D t =
     abi_generic_list_item_ptr (sd_tcb_ptr D t)"

definition scheduler_family_generic_raw_set ::
  "'tid set \<Rightarrow> 'tid scheduler_decode \<Rightarrow> raw_node_id set"
where
  "scheduler_family_generic_raw_set live D =
     scheduler_family_generic_raw_ptr D ` live"

theorem scheduler_generic_task_family_remove_interface:
  assumes pre: "scheduler_family_pre_rel h roots raw_fam live D"
    and laws: "universal_decoder_laws live D"
    and owner: "owner \<in> roots"
    and removed_live: "t \<in> live"
    and member:
      "scheduler_family_generic_raw_ptr D t
         \<in> set (ring (raw_fam owner))"
    and generic_only:
      "\<And>lp. lp \<in> roots \<Longrightarrow>
        set (ring (raw_fam lp))
          \<subseteq> scheduler_family_generic_raw_set live D"
    and relabels:
      "\<And>lp. lp \<in> roots \<Longrightarrow>
        xlist_relabel (sd_node_decode D) (raw_fam lp) (abs_fam lp)"
    and abs_wf:
      "\<And>lp. lp \<in> roots \<Longrightarrow> xlist_wf (abs_fam lp)"
    and keys:
      "\<And>u. u \<in> live \<Longrightarrow>
        raw_key_at h (scheduler_family_generic_raw_ptr D u) = key_of u"
  defines
    "p \<equiv> scheduler_family_generic_raw_ptr D t"
    and "raw_fam' \<equiv> scheduler_family_remove_raw raw_fam owner
      (scheduler_family_generic_raw_ptr D t)"
    and "abs_fam' \<equiv>
      scheduler_family_remove_abs abs_fam owner (Generic t)"
  shows
    "scheduler_node_kind_family_remove_post
       D h (raw_remove_concrete_heap h p) roots raw_fam abs_fam live
       owner p (Generic t) \<and>
     (\<forall>lp\<in>roots.
        set (ring (raw_fam' lp))
          \<subseteq> scheduler_family_generic_raw_set live D) \<and>
     (\<forall>lp\<in>roots.
        xlist_relabel (sd_node_decode D) (raw_fam' lp) (abs_fam' lp)) \<and>
     (\<forall>u\<in>live.
        raw_key_at (raw_remove_concrete_heap h p)
          (scheduler_family_generic_raw_ptr D u) = key_of u)"
proof -
  have decode:
    "sd_node_decode D p = Some (Generic t)"
    using universal_node_decode_Generic_iff[
        OF laws, where p=p and t=t]
      removed_live
    by (simp add: p_def scheduler_family_generic_raw_ptr_def)
  have member_p: "p \<in> set (ring (raw_fam owner))"
    using member by (simp add: p_def)
  have post:
    "scheduler_node_kind_family_remove_post
       D h (raw_remove_concrete_heap h p) roots raw_fam abs_fam live
       owner p (Generic t)"
    by (rule scheduler_node_kind_family_remove_preserved[
          OF pre owner member_p relabels abs_wf decode])
  have subset_base:
    "\<forall>lp\<in>roots.
       set (ring (scheduler_family_remove_raw raw_fam owner p lp))
         \<subseteq> scheduler_family_generic_raw_set live D"
  proof (intro ballI)
    fix lp
    assume lp_root: "lp \<in> roots"
    show
      "set (ring (scheduler_family_remove_raw raw_fam owner p lp))
         \<subseteq> scheduler_family_generic_raw_set live D"
      by (rule scheduler_family_remove_specific_subset_preserved[
            OF generic_only lp_root])
  qed
  have subset_post:
    "\<forall>lp\<in>roots.
       set (ring (raw_fam' lp))
         \<subseteq> scheduler_family_generic_raw_set live D"
    using subset_base unfolding raw_fam'_def p_def by simp
  have labels_base:
    "\<forall>lp\<in>roots.
       xlist_relabel (sd_node_decode D)
         (scheduler_family_remove_raw raw_fam owner p lp)
         (scheduler_family_remove_abs abs_fam owner (Generic t) lp)"
  proof (intro ballI)
    fix lp
    assume lp_root: "lp \<in> roots"
    show
      "xlist_relabel (sd_node_decode D)
         (scheduler_family_remove_raw raw_fam owner p lp)
         (scheduler_family_remove_abs abs_fam owner (Generic t) lp)"
      apply (rule scheduler_family_remove_relabel_preserved[
          where h=h and roots=roots and raw_fam=raw_fam and live=live
            and D=D and owner=owner and p=p and abs_fam=abs_fam
            and n="Generic t"])
      subgoal using pre by assumption
      subgoal using owner by assumption
      subgoal using member_p by assumption
      subgoal using relabels by assumption
      subgoal using abs_wf by assumption
      subgoal using decode by assumption
      subgoal using lp_root by assumption
      done
  qed
  have labels_post:
    "\<forall>lp\<in>roots.
       xlist_relabel (sd_node_decode D) (raw_fam' lp) (abs_fam' lp)"
    using labels_base
    unfolding raw_fam'_def abs_fam'_def p_def by simp
  have key_post:
    "\<forall>u\<in>live.
       raw_key_at (raw_remove_concrete_heap h p)
         (scheduler_family_generic_raw_ptr D u) = key_of u"
  proof (intro ballI)
    fix u
    assume u_live: "u \<in> live"
    let ?q = "scheduler_family_generic_raw_ptr D u"
    have q_managed: "?q \<in> universal_managed_nodes live D"
      using u_live
      by (auto simp: scheduler_family_generic_raw_ptr_def
          universal_managed_nodes_def)
    show "raw_key_at (raw_remove_concrete_heap h p) ?q = key_of u"
    proof (cases "?q = p")
      case True
      show ?thesis
        using scheduler_family_remove_item_effect[OF pre owner member_p]
          keys[OF u_live] True
        by simp
    next
      case False
      show ?thesis
        using scheduler_family_remove_managed_payload_frame[
            OF pre owner member_p q_managed False]
          keys[OF u_live]
        by simp
    qed
  qed
  show ?thesis using post subset_post labels_post key_post by simp
qed

theorem scheduler_vListRemove_generic_task_family_interface:
  assumes pre:
      "scheduler_family_pre_rel (hrs_mem (t_hrs_' s)) roots
         raw_fam live D"
    and laws: "universal_decoder_laws live D"
    and owner: "owner \<in> roots"
    and removed_live: "t \<in> live"
    and member:
      "scheduler_family_generic_raw_ptr D t
         \<in> set (ring (raw_fam owner))"
    and generic_only:
      "\<And>lp. lp \<in> roots \<Longrightarrow>
        set (ring (raw_fam lp))
          \<subseteq> scheduler_family_generic_raw_set live D"
    and relabels:
      "\<And>lp. lp \<in> roots \<Longrightarrow>
        xlist_relabel (sd_node_decode D) (raw_fam lp) (abs_fam lp)"
    and abs_wf:
      "\<And>lp. lp \<in> roots \<Longrightarrow> xlist_wf (abs_fam lp)"
    and keys:
      "\<And>u. u \<in> live \<Longrightarrow>
        raw_key_at (hrs_mem (t_hrs_' s))
          (scheduler_family_generic_raw_ptr D u) = key_of u"
  shows
    "vListRemove' (scheduler_family_generic_raw_ptr D t) \<bullet> s
     \<lbrace>\<lambda>r s'. r = Result () \<and>
       (let p = scheduler_family_generic_raw_ptr D t;
            raw_fam' = scheduler_family_remove_raw raw_fam owner p;
            abs_fam' = scheduler_family_remove_abs abs_fam owner (Generic t)
        in scheduler_node_kind_family_remove_post D
             (hrs_mem (t_hrs_' s)) (hrs_mem (t_hrs_' s')) roots
             raw_fam abs_fam live owner p (Generic t) \<and>
           (\<forall>lp\<in>roots.
              set (ring (raw_fam' lp))
                \<subseteq> scheduler_family_generic_raw_set live D) \<and>
           (\<forall>lp\<in>roots.
              xlist_relabel (sd_node_decode D)
                (raw_fam' lp) (abs_fam' lp)) \<and>
           (\<forall>u\<in>live.
              raw_key_at (hrs_mem (t_hrs_' s'))
                (scheduler_family_generic_raw_ptr D u) = key_of u))
     \<rbrace>"
proof -
  let ?p = "scheduler_family_generic_raw_ptr D t"
  have raw:
    "raw_xlist_rel (hrs_mem (t_hrs_' s)) owner (raw_fam owner)"
    using pre owner
    by (auto simp: scheduler_family_pre_rel_def raw_family_rel_def)
  note heap = raw_vListRemove_general_heap_effect[OF raw member]
  have pure:
    "let raw_fam' = scheduler_family_remove_raw raw_fam owner ?p;
         abs_fam' = scheduler_family_remove_abs abs_fam owner (Generic t)
     in scheduler_node_kind_family_remove_post D
          (hrs_mem (t_hrs_' s))
          (raw_remove_concrete_heap (hrs_mem (t_hrs_' s)) ?p) roots
          raw_fam abs_fam live owner ?p (Generic t) \<and>
        (\<forall>lp\<in>roots.
           set (ring (raw_fam' lp))
             \<subseteq> scheduler_family_generic_raw_set live D) \<and>
        (\<forall>lp\<in>roots.
           xlist_relabel (sd_node_decode D)
             (raw_fam' lp) (abs_fam' lp)) \<and>
        (\<forall>u\<in>live.
           raw_key_at
             (raw_remove_concrete_heap (hrs_mem (t_hrs_' s)) ?p)
             (scheduler_family_generic_raw_ptr D u) = key_of u)"
    using scheduler_generic_task_family_remove_interface[
      OF pre laws owner removed_live member generic_only relabels abs_wf keys]
    by (simp add: Let_def)
  show ?thesis
    apply (rule runs_to_weaken[OF heap])
    using pure by (auto simp: Let_def)
qed

end
