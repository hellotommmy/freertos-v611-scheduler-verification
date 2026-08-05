theory Scheduler_One_Due_Task_Phases_Reentry_Pure
  imports
    "EAL6_FreeRTOS_V611_Scheduler_One_Due_Task_Phases_Delayed_Head.Scheduler_One_Due_Task_Phases_Delayed_Head"
begin

text \<open>
  Pure re-entry witnesses for the next due task.  After one completed
  tick-body iteration the context advances to the decoded head of the
  shrunk delayed ring with the raised top, and the snapshot is the
  completed five-phase state with the capture and check registers
  cleared.  The lemmas below give the component facts of the pure entry
  relation at those witnesses; root-membership side conditions that the
  pure layer cannot re-establish stay explicit premises for the gate
  layer.
\<close>

definition one_due_reentry_context ::
  "('tid, 'root) one_due_context \<Rightarrow> 'tid \<Rightarrow>
   ('tid, 'root) one_due_context"
where
  "one_due_reentry_context C u =
     C\<lparr>odc_task := u,
       odc_entry_top :=
         max (odc_entry_top C) (odc_priority C (odc_task C))\<rparr>"

definition one_due_reentry_snapshot ::
  "('tid, 'root) one_due_context \<Rightarrow>
   'root one_due_event_branch \<Rightarrow>
   ('tid, 'root) one_due_snapshot \<Rightarrow>
   ('tid, 'root) one_due_snapshot"
where
  "one_due_reentry_snapshot C branch S =
     (one_due_ready_state C
       (one_due_raise_top_state C
         (one_due_event_unlink_state C branch
           (one_due_event_check_state branch
             (one_due_generic_unlink_state C S)))))
     \<lparr>ods_captured_generic_key := None,
      ods_checked_event := None\<rparr>"

lemma one_due_reentry_context_components:
  "odc_live (one_due_reentry_context C u) = odc_live C"
  "odc_task (one_due_reentry_context C u) = u"
  "odc_generic_roots (one_due_reentry_context C u) =
     odc_generic_roots C"
  "odc_event_roots (one_due_reentry_context C u) =
     odc_event_roots C"
  "odc_delayed_root (one_due_reentry_context C u) =
     odc_delayed_root C"
  "odc_ready_root (one_due_reentry_context C u) = odc_ready_root C"
  "odc_pending_root (one_due_reentry_context C u) =
     odc_pending_root C"
  "odc_priority (one_due_reentry_context C u) = odc_priority C"
  "odc_tick (one_due_reentry_context C u) = odc_tick C"
  "odc_entry_top (one_due_reentry_context C u) =
     max (odc_entry_top C) (odc_priority C (odc_task C))"
  "odc_K_E (one_due_reentry_context C u) = odc_K_E C"
  by (simp_all add: one_due_reentry_context_def)

lemma one_due_reentry_snapshot_registers:
  "ods_captured_generic_key
     (one_due_reentry_snapshot C branch S) = None"
  "ods_checked_event (one_due_reentry_snapshot C branch S) = None"
  by (simp_all add: one_due_reentry_snapshot_def)

lemma one_due_reentry_snapshot_top:
  "ods_top (one_due_reentry_snapshot C branch S) =
     max (ods_top S) (odc_priority C (odc_task C))"
  by (cases branch)
     (simp_all add: one_due_reentry_snapshot_def
       one_due_ready_state_def one_due_raise_top_state_def
       one_due_event_unlink_state_def one_due_event_check_state_def
       one_due_generic_unlink_state_def Let_def)

lemma one_due_reentry_snapshot_payloads:
  "ods_generic_payload (one_due_reentry_snapshot C branch S) =
     ods_generic_payload S"
  "ods_event_payload (one_due_reentry_snapshot C branch S) =
     ods_event_payload S"
  by (cases branch;
      simp add: one_due_reentry_snapshot_def
        one_due_ready_state_def one_due_raise_top_state_def
        one_due_event_unlink_state_def one_due_event_check_state_def
        one_due_generic_unlink_state_def Let_def)+

lemma one_due_reentry_snapshot_generic_at:
  "ods_generic_family (one_due_reentry_snapshot C branch S) r =
     (let target = one_due_target_root C;
          removed =
            (ods_generic_family S)
              (odc_delayed_root C :=
                list_remove_abs (Generic (odc_task C))
                  (ods_generic_family S (odc_delayed_root C)))
      in if r = target
         then list_insert_end_abs (Generic (odc_task C))
                (ods_generic_payload S (odc_task C))
                (removed target)
         else removed r)"
  by (cases branch)
     (simp_all add: one_due_reentry_snapshot_def
       one_due_ready_state_def one_due_raise_top_state_def
       one_due_event_unlink_state_def one_due_event_check_state_def
       one_due_generic_unlink_state_def Let_def fun_upd_def)

lemma one_due_reentry_snapshot_event_at:
  "ods_event_family (one_due_reentry_snapshot C branch S) r =
     (case branch of
        DueEventLinked owner \<Rightarrow>
          if r = owner
          then list_remove_abs (Event (odc_task C))
                 (ods_event_family S owner)
          else ods_event_family S r
      | DueEventNull \<Rightarrow> ods_event_family S r)"
  by (cases branch)
     (simp_all add: one_due_reentry_snapshot_def
       one_due_ready_state_def one_due_raise_top_state_def
       one_due_event_unlink_state_def one_due_event_check_state_def
       one_due_generic_unlink_state_def Let_def fun_upd_def)

lemma list_remove_abs_item_key:
  "item_key (list_remove_abs x xs) = item_key xs"
  by (simp add: list_remove_abs_def)

lemma list_insert_end_abs_item_key:
  "item_key (list_insert_end_abs x k xs) =
     (item_key xs)(x := k)"
  by (simp add: list_insert_end_abs_def)

lemma list_remove_abs_ring_subset:
  "set (ring (list_remove_abs x xs)) \<subseteq> set (ring xs)"
  by (auto simp: list_remove_abs_def
      dest!: subsetD[OF set_remove1_subset])

lemma list_insert_end_abs_ring_set:
  assumes wf: "xlist_wf xs"
  shows
    "set (ring (list_insert_end_abs x k xs)) =
       insert x (set (ring xs))"
proof (cases "cursor xs")
  case None
  then show ?thesis
    by (simp add: list_insert_end_abs_def)
next
  case (Some c)
  have c_in: "c \<in> set (ring xs)"
    using wf Some by (simp add: xlist_wf_def)
  show ?thesis
    using Some set_insert_after[OF c_in]
    by (simp add: list_insert_end_abs_def)
qed

lemma one_due_reentry_family_shape:
  assumes entry: "one_due_entry_rel C branch S"
  shows
    "one_due_family_shape (one_due_reentry_context C u)
       (one_due_reentry_snapshot C branch S)"
proof -
  let ?C' = "one_due_reentry_context C u"
  let ?S' = "one_due_reentry_snapshot C branch S"
  let ?source = "odc_delayed_root C"
  let ?target = "one_due_target_root C"
  let ?task = "odc_task C"
  let ?k = "ods_generic_payload S ?task"
  have wf: "one_due_context_wf C"
    and shape: "one_due_family_shape C S"
    and task_in0: "Generic ?task \<in>
      set (ring (ods_generic_family S ?source))"
    and branch_at0: "one_due_event_branch_at C S branch"
    using entry by (simp_all add: one_due_entry_rel_def)
  have source_root: "?source \<in> odc_generic_roots C"
    and target_root: "?target \<in> odc_generic_roots C"
    and source_target_ne: "?source \<noteq> ?target"
    and task_live: "?task \<in> odc_live C"
    using wf by (simp_all add: one_due_context_wf_def)
  have task_notin_target:
    "Generic ?task \<notin> set (ring (ods_generic_family S ?target))"
  proof
    assume mem:
      "Generic ?task \<in> set (ring (ods_generic_family S ?target))"
    have disj:
      "set (ring (ods_generic_family S ?source)) \<inter>
         set (ring (ods_generic_family S ?target)) = {}"
      using shape source_root target_root source_target_ne
      by (auto simp: one_due_family_shape_def)
    show False using task_in0 mem disj by blast
  qed
  have gen_at:
    "\<And>r. ods_generic_family ?S' r =
       (if r = ?target
        then list_insert_end_abs (Generic ?task) ?k
               (ods_generic_family S ?target)
        else if r = ?source
        then list_remove_abs (Generic ?task)
               (ods_generic_family S ?source)
        else ods_generic_family S r)"
    using source_target_ne
    by (simp add: one_due_reentry_snapshot_generic_at Let_def
        fun_upd_def)
  have gen_set:
    "\<And>r. r \<in> odc_generic_roots C \<Longrightarrow>
       set (ring (ods_generic_family ?S' r)) \<subseteq>
         insert (Generic ?task)
           (set (ring (ods_generic_family S r)))"
  proof -
    fix r assume r_root: "r \<in> odc_generic_roots C"
    have wf_r: "xlist_wf (ods_generic_family S r)"
      using shape r_root by (auto simp: one_due_family_shape_def)
    show "set (ring (ods_generic_family ?S' r)) \<subseteq>
       insert (Generic ?task)
         (set (ring (ods_generic_family S r)))"
    proof (cases "r = ?target")
      case True
      then show ?thesis
        using list_insert_end_abs_ring_set[OF wf_r]
        by (simp add: gen_at)
    next
      case False
      then show ?thesis
        using list_remove_abs_ring_subset[of "Generic ?task"
          "ods_generic_family S ?source"]
        by (auto simp: gen_at)
    qed
  qed
  have gen_clause:
    "\<forall>r\<in>odc_generic_roots C.
       xlist_wf (ods_generic_family ?S' r) \<and>
       generic_ring (ods_generic_family ?S' r) \<and>
       set (ring (ods_generic_family ?S' r)) \<subseteq>
         Generic ` odc_live C"
  proof (intro ballI conjI)
    fix r assume r_root: "r \<in> odc_generic_roots C"
    have wf_r: "xlist_wf (ods_generic_family S r)"
      and kind_r: "generic_ring (ods_generic_family S r)"
      and sub_r: "set (ring (ods_generic_family S r)) \<subseteq>
        Generic ` odc_live C"
      using shape r_root by (auto simp: one_due_family_shape_def)
    show "xlist_wf (ods_generic_family ?S' r)"
    proof (cases "r = ?target")
      case True
      show ?thesis
        using True list_insert_end_preserves_wf[OF wf_r]
          task_notin_target
        by (simp add: gen_at)
    next
      case False
      show ?thesis
      proof (cases "r = ?source")
        case True
        show ?thesis
          using True False list_remove_preserves_wf[OF wf_r]
            task_in0
          by (simp add: gen_at)
      next
        case False'': False
        show ?thesis
          using \<open>r \<noteq> ?target\<close> False'' wf_r
          by (simp add: gen_at)
      qed
    qed
    show "generic_ring (ods_generic_family ?S' r)"
      using gen_set[OF r_root] kind_r
      by (fastforce simp: generic_ring_def)
    show "set (ring (ods_generic_family ?S' r)) \<subseteq>
       Generic ` odc_live C"
      using gen_set[OF r_root] sub_r task_live by auto
  qed
  have ev_at:
    "\<And>r. ods_event_family ?S' r =
       (case branch of
          DueEventLinked owner \<Rightarrow>
            if r = owner
            then list_remove_abs (Event ?task)
                   (ods_event_family S owner)
            else ods_event_family S r
        | DueEventNull \<Rightarrow> ods_event_family S r)"
    by (simp add: one_due_reentry_snapshot_event_at)
  have ev_sub:
    "\<And>r. set (ring (ods_event_family ?S' r)) \<subseteq>
       set (ring (ods_event_family S r))"
    by (auto simp: ev_at
        split: one_due_event_branch.splits if_splits
        dest!: subsetD[OF list_remove_abs_ring_subset])
  have ev_clause:
    "\<forall>r\<in>odc_event_roots C.
       xlist_wf (ods_event_family ?S' r) \<and>
       event_ring (ods_event_family ?S' r) \<and>
       set (ring (ods_event_family ?S' r)) \<subseteq>
         Event ` odc_live C"
  proof (intro ballI conjI)
    fix r assume r_root: "r \<in> odc_event_roots C"
    have wf_r: "xlist_wf (ods_event_family S r)"
      and kind_r: "event_ring (ods_event_family S r)"
      and sub_r: "set (ring (ods_event_family S r)) \<subseteq>
        Event ` odc_live C"
      using shape r_root by (auto simp: one_due_family_shape_def)
    show "xlist_wf (ods_event_family ?S' r)"
    proof (cases branch)
      case DueEventNull
      then show ?thesis
        using wf_r
        by (simp add: one_due_reentry_snapshot_event_at)
    next
      case (DueEventLinked owner)
      show ?thesis
      proof (cases "r = owner")
        case True
        have member: "Event ?task \<in>
          set (ring (ods_event_family S owner))"
          using branch_at0 DueEventLinked by simp
        show ?thesis
          using DueEventLinked True
            list_remove_preserves_wf[OF wf_r] member
          by (simp add: one_due_reentry_snapshot_event_at)
      next
        case False
        then show ?thesis
          using DueEventLinked wf_r
          by (simp add: one_due_reentry_snapshot_event_at)
      qed
    qed
    show "event_ring (ods_event_family ?S' r)"
      using ev_sub[of r] kind_r
      by (fastforce simp: event_ring_def)
    show "set (ring (ods_event_family ?S' r)) \<subseteq>
       Event ` odc_live C"
      using ev_sub[of r] sub_r by blast
  qed
  have gen_pairwise:
    "\<forall>r\<in>odc_generic_roots C. \<forall>s\<in>odc_generic_roots C.
       r \<noteq> s \<longrightarrow>
       set (ring (ods_generic_family ?S' r)) \<inter>
         set (ring (ods_generic_family ?S' s)) = {}"
  proof (intro ballI impI)
    fix r s
    assume r_root: "r \<in> odc_generic_roots C"
      and s_root: "s \<in> odc_generic_roots C"
      and ne: "r \<noteq> s"
    have base:
      "set (ring (ods_generic_family S r)) \<inter>
         set (ring (ods_generic_family S s)) = {}"
      using shape r_root s_root ne
      by (auto simp: one_due_family_shape_def)
    have wf_r: "xlist_wf (ods_generic_family S r)"
      and wf_s: "xlist_wf (ods_generic_family S s)"
      using shape r_root s_root
      by (auto simp: one_due_family_shape_def)
    have dist_source:
      "distinct (ring (ods_generic_family S ?source))"
      using shape source_root
      by (auto simp: one_due_family_shape_def xlist_wf_def)
    have task_from_source:
      "\<And>x. x \<in> odc_generic_roots C \<Longrightarrow>
         Generic ?task \<in> set (ring (ods_generic_family S x))
         \<Longrightarrow> x = ?source"
    proof -
      fix x
      assume x_root: "x \<in> odc_generic_roots C"
        and x_mem:
          "Generic ?task \<in> set (ring (ods_generic_family S x))"
      show "x = ?source"
      proof (rule ccontr)
        assume ne: "x \<noteq> ?source"
        have "set (ring (ods_generic_family S x)) \<inter>
           set (ring (ods_generic_family S ?source)) = {}"
          using shape x_root source_root ne
          by (auto simp: one_due_family_shape_def)
        then show False using x_mem task_in0 by blast
      qed
    qed
    have dist_src: "distinct (ring (ods_generic_family S ?source))"
      using shape source_root
      by (auto simp: one_due_family_shape_def xlist_wf_def)
    have task_notin_removed:
      "Generic ?task \<notin> set (ring (list_remove_abs
         (Generic ?task) (ods_generic_family S ?source)))"
      using dist_src by (simp add: list_remove_abs_def)
    have mem_task':
      "\<And>x. x \<in> odc_generic_roots C \<Longrightarrow>
         Generic ?task \<in>
           set (ring (ods_generic_family ?S' x)) \<Longrightarrow>
         x = ?target"
    proof -
      fix x
      assume x_root: "x \<in> odc_generic_roots C"
        and mem': "Generic ?task \<in>
          set (ring (ods_generic_family ?S' x))"
      show "x = ?target"
      proof (rule ccontr)
        assume ne': "x \<noteq> ?target"
        show False
        proof (cases "x = ?source")
          case True
          then show False
            using mem' ne' task_notin_removed
            by (simp add: gen_at)
        next
          case False
          have "Generic ?task \<in>
            set (ring (ods_generic_family S x))"
            using mem' ne' False by (simp add: gen_at)
          then show False
            using task_from_source[OF x_root] False by simp
        qed
      qed
    qed
    show "set (ring (ods_generic_family ?S' r)) \<inter>
       set (ring (ods_generic_family ?S' s)) = {}"
    proof -
      have gr: "set (ring (ods_generic_family ?S' r)) \<subseteq>
        insert (Generic ?task)
          (set (ring (ods_generic_family S r)))"
        by (rule gen_set[OF r_root])
      have gs: "set (ring (ods_generic_family ?S' s)) \<subseteq>
        insert (Generic ?task)
          (set (ring (ods_generic_family S s)))"
        by (rule gen_set[OF s_root])
      { fix n
        assume nr: "n \<in> set (ring (ods_generic_family ?S' r))"
          and ns: "n \<in> set (ring (ods_generic_family ?S' s))"
        have False
        proof (cases "n = Generic ?task")
          case True
          have "r = ?target"
            using mem_task'[OF r_root] nr True by simp
          moreover have "s = ?target"
            using mem_task'[OF s_root] ns True by simp
          ultimately show False using ne by simp
        next
          case False
          have "n \<in> set (ring (ods_generic_family S r))"
            using gr nr False by blast
          moreover have "n \<in> set (ring (ods_generic_family S s))"
            using gs ns False by blast
          ultimately show False using base by blast
        qed }
      then show ?thesis by blast
    qed
  qed
  have ev_pairwise:
    "\<forall>r\<in>odc_event_roots C. \<forall>s\<in>odc_event_roots C.
       r \<noteq> s \<longrightarrow>
       set (ring (ods_event_family ?S' r)) \<inter>
         set (ring (ods_event_family ?S' s)) = {}"
  proof (intro ballI impI)
    fix r s
    assume "r \<in> odc_event_roots C" "s \<in> odc_event_roots C"
      and ne: "r \<noteq> s"
    then have base:
      "set (ring (ods_event_family S r)) \<inter>
         set (ring (ods_event_family S s)) = {}"
      using shape ne by (auto simp: one_due_family_shape_def)
    show "set (ring (ods_event_family ?S' r)) \<inter>
       set (ring (ods_event_family ?S' s)) = {}"
      using base ev_sub[of r] ev_sub[of s] by blast
  qed
  have gen_keys:
    "\<forall>r\<in>odc_generic_roots C. \<forall>t\<in>odc_live C.
       Generic t \<in> set (ring (ods_generic_family ?S' r)) \<longrightarrow>
       item_key (ods_generic_family ?S' r) (Generic t) =
         ods_generic_payload ?S' t"
  proof (intro ballI impI)
    fix r t
    assume r_root: "r \<in> odc_generic_roots C"
      and t_live: "t \<in> odc_live C"
      and t_in: "Generic t \<in>
        set (ring (ods_generic_family ?S' r))"
    have wf_r: "xlist_wf (ods_generic_family S r)"
      using shape r_root by (auto simp: one_due_family_shape_def)
    have old_key:
      "\<And>x. x \<in> odc_generic_roots C \<Longrightarrow>
         Generic t \<in> set (ring (ods_generic_family S x)) \<Longrightarrow>
         item_key (ods_generic_family S x) (Generic t) =
           ods_generic_payload S t"
      using shape t_live by (auto simp: one_due_family_shape_def)
    show "item_key (ods_generic_family ?S' r) (Generic t) =
       ods_generic_payload ?S' t"
    proof (cases "r = ?target")
      case True
      have t_cases:
        "Generic t = Generic ?task \<or>
         Generic t \<in> set (ring (ods_generic_family S ?target))"
        using t_in True list_insert_end_abs_ring_set[OF wf_r[
          unfolded True]]
        by (auto simp: gen_at)
      note rT = True
      show ?thesis
      proof (cases "Generic t = Generic ?task")
        case True
        then show ?thesis
          using rT
          by (simp add: gen_at list_insert_end_abs_item_key
              one_due_reentry_snapshot_payloads)
      next
        case False
        have t_in_old:
          "Generic t \<in> set (ring (ods_generic_family S ?target))"
          using t_cases False by simp
        show ?thesis
          using rT False old_key[OF target_root t_in_old]
          by (simp add: gen_at list_insert_end_abs_item_key
              one_due_reentry_snapshot_payloads)
      qed
    next
      case False
      have t_in_old:
        "Generic t \<in> set (ring (ods_generic_family S r))"
        using t_in False
        by (auto simp: gen_at split: if_splits
            dest!: subsetD[OF list_remove_abs_ring_subset])
      note rF = False
      show ?thesis
      proof (cases "r = ?source")
        case True
        then show ?thesis
          using rF old_key[OF r_root t_in_old]
          by (simp add: gen_at list_remove_abs_item_key
              one_due_reentry_snapshot_payloads)
      next
        case False
        then show ?thesis
          using rF old_key[OF r_root t_in_old]
          by (simp add: gen_at one_due_reentry_snapshot_payloads)
      qed
    qed
  qed
  have ev_keys:
    "\<forall>r\<in>odc_event_roots C. \<forall>t\<in>odc_live C.
       Event t \<in> set (ring (ods_event_family ?S' r)) \<longrightarrow>
       item_key (ods_event_family ?S' r) (Event t) =
         ods_event_payload ?S' t"
  proof (intro ballI impI)
    fix r t
    assume r_root: "r \<in> odc_event_roots C"
      and t_live: "t \<in> odc_live C"
      and t_in: "Event t \<in> set (ring (ods_event_family ?S' r))"
    have t_in_old:
      "Event t \<in> set (ring (ods_event_family S r))"
      using t_in ev_sub[of r] by blast
    have old_key:
      "item_key (ods_event_family S r) (Event t) =
         ods_event_payload S t"
      using shape r_root t_live t_in_old
      by (auto simp: one_due_family_shape_def)
    show "item_key (ods_event_family ?S' r) (Event t) =
       ods_event_payload ?S' t"
    proof (cases branch)
      case DueEventNull
      then show ?thesis
        using old_key
        by (simp add: one_due_reentry_snapshot_event_at
            one_due_reentry_snapshot_payloads)
    next
      case (DueEventLinked owner)
      show ?thesis
      proof (cases "r = owner")
        case True
        then show ?thesis
          using old_key DueEventLinked
          by (simp add: one_due_reentry_snapshot_event_at
              list_remove_abs_item_key
              one_due_reentry_snapshot_payloads)
      next
        case False
        then show ?thesis
          using old_key DueEventLinked
          by (simp add: one_due_reentry_snapshot_event_at
              one_due_reentry_snapshot_payloads)
      qed
    qed
  qed
  have ke:
    "\<forall>t\<in>odc_live C.
       ods_event_payload ?S' t = odc_K_E ?C' t"
    using shape
    by (simp add: one_due_reentry_snapshot_payloads
        one_due_reentry_context_components
        one_due_family_shape_def)
  show ?thesis
    using gen_clause ev_clause gen_pairwise ev_pairwise gen_keys
      ev_keys ke
    by (simp add: one_due_family_shape_def
        one_due_reentry_context_components)
qed

theorem one_due_reentry_entry_rel:
  assumes entry: "one_due_entry_rel C branch S"
    and u_live: "u \<in> odc_live C"
    and head_shape:
      "\<exists>rest. ring (list_remove_abs (Generic (odc_task C))
         (ods_generic_family S (odc_delayed_root C))) =
       Generic u # rest"
    and u_due:
      "ods_generic_payload S u \<le> odc_tick C"
    and target'_root:
      "odc_ready_root C (odc_priority C u) \<in> odc_generic_roots C"
    and target'_ne:
      "odc_delayed_root C \<noteq> odc_ready_root C (odc_priority C u)"
    and branch':
      "one_due_event_branch_at (one_due_reentry_context C u)
         (one_due_reentry_snapshot C branch S) branch'"
  shows
    "one_due_entry_rel (one_due_reentry_context C u) branch'
       (one_due_reentry_snapshot C branch S)"
proof -
  let ?C' = "one_due_reentry_context C u"
  let ?S' = "one_due_reentry_snapshot C branch S"
  let ?source = "odc_delayed_root C"
  let ?target = "one_due_target_root C"
  let ?task = "odc_task C"
  have wf: "one_due_context_wf C"
    and shape: "one_due_family_shape C S"
    and head0: "\<exists>rest. ring (ods_generic_family S ?source) =
      Generic ?task # rest"
    and task_in0: "Generic ?task \<in>
      set (ring (ods_generic_family S ?source))"
    and top0: "ods_top S = odc_entry_top C"
    using entry by (simp_all add: one_due_entry_rel_def)
  have source_root: "?source \<in> odc_generic_roots C"
    and target_root: "?target \<in> odc_generic_roots C"
    and source_target_ne: "?source \<noteq> ?target"
    using wf by (simp_all add: one_due_context_wf_def)
  have task_notin_target:
    "Generic ?task \<notin> set (ring (ods_generic_family S ?target))"
  proof
    assume mem:
      "Generic ?task \<in> set (ring (ods_generic_family S ?target))"
    have disj:
      "set (ring (ods_generic_family S ?source)) \<inter>
         set (ring (ods_generic_family S ?target)) = {}"
      using shape source_root target_root source_target_ne
      by (auto simp: one_due_family_shape_def)
    show False using task_in0 mem disj by blast
  qed
  have wf_source:
    "xlist_wf (ods_generic_family S ?source)"
    and wf_target:
    "xlist_wf (ods_generic_family S ?target)"
    using shape source_root target_root
    by (auto simp: one_due_family_shape_def)
  have context_wf': "one_due_context_wf ?C'"
    using wf u_live target'_root target'_ne
    by (simp add: one_due_context_wf_def
        one_due_reentry_context_components one_due_target_root_def)
  have head':
    "\<exists>rest. ring (ods_generic_family ?S'
       (odc_delayed_root ?C')) = Generic u # rest"
    using head_shape source_target_ne
    by (simp add: one_due_reentry_snapshot_generic_at
        one_due_reentry_context_components Let_def fun_upd_def)
  have u_in':
    "Generic u \<in> set (ring (ods_generic_family ?S'
       (odc_delayed_root ?C')))"
  proof -
    obtain rest where
      "ring (ods_generic_family ?S' (odc_delayed_root ?C')) =
         Generic u # rest"
      using head' by blast
    then show ?thesis by simp
  qed
  have u_in_removed:
    "Generic u \<in> set (ring (list_remove_abs (Generic ?task)
       (ods_generic_family S ?source)))"
  proof -
    obtain rest where
      "ring (list_remove_abs (Generic ?task)
         (ods_generic_family S ?source)) = Generic u # rest"
      using head_shape by blast
    then show ?thesis by simp
  qed
  have u_in0:
    "Generic u \<in> set (ring (ods_generic_family S ?source))"
    using u_in_removed
    by (rule rev_subsetD[OF _ list_remove_abs_ring_subset])
  have key0:
    "item_key (ods_generic_family S ?source) (Generic u) =
       ods_generic_payload S u"
    using shape source_root u_live u_in0
    by (auto simp: one_due_family_shape_def)
  have key':
    "item_key (ods_generic_family ?S' (odc_delayed_root ?C'))
       (Generic u) = ods_generic_payload ?S' u"
    using key0 source_target_ne
    by (simp add: one_due_reentry_snapshot_generic_at
        one_due_reentry_context_components
        one_due_reentry_snapshot_payloads Let_def fun_upd_def
        list_remove_abs_item_key)
  have due':
    "ods_generic_payload ?S' u \<le> odc_tick ?C'"
    using u_due
    by (simp add: one_due_reentry_snapshot_payloads
        one_due_reentry_context_components)
  have top':
    "ods_top ?S' = odc_entry_top ?C'"
    using top0
    by (simp add: one_due_reentry_snapshot_top
        one_due_reentry_context_components)
  have shape': "one_due_family_shape ?C' ?S'"
    by (rule one_due_reentry_family_shape[OF entry])
  show ?thesis
    using context_wf' shape' head' u_in' key' due' branch' top'
    by (simp add: one_due_entry_rel_def
        one_due_reentry_snapshot_registers
        one_due_reentry_context_components)
qed

end
