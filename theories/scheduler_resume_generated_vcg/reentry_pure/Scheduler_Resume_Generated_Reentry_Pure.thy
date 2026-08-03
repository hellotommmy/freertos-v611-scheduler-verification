theory Scheduler_Resume_Generated_Reentry_Pure
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Abs_Preservation.Scheduler_Resume_Abs_Preservation"
begin

text \<open>
  The pure half of loop re-entry.  After one drain iteration the tail
  context -- the remaining pending tasks, with the entry top raised to the
  awakened priority -- and the four-phase drained snapshot satisfy the pure
  entry relation again.  The four-phase snapshot deliberately excludes the
  yield phase: its local-yield flag is untouched and therefore still false,
  which is exactly what re-entry needs; the yield outcome lives in the
  loop-carried word, not in the snapshot.
\<close>

definition resume_pending_drained_context ::
  "('tid, xLIST_C ptr) resume_pending_context \<Rightarrow> 'tid \<Rightarrow> 'tid list \<Rightarrow>
   ('tid, xLIST_C ptr) resume_pending_context"
where
  "resume_pending_drained_context C t rest =
     C\<lparr>rpc_tasks := rest,
        rpc_entry_top := max (rpc_entry_top C) (rpc_priority C t)\<rparr>"

definition resume_pending_drained_snapshot ::
  "('tid, xLIST_C ptr) resume_pending_context \<Rightarrow> 'tid \<Rightarrow>
   ('tid, xLIST_C ptr) resume_pending_snapshot \<Rightarrow>
   ('tid, xLIST_C ptr) resume_pending_snapshot"
where
  "resume_pending_drained_snapshot C t S =
     resume_pending_ready_insert_state C t
       (resume_pending_raise_top_state C t
         (resume_pending_generic_unlink_state C t
           (resume_pending_event_unlink_state C t S)))"

section \<open>Component values of the drained context and snapshot\<close>

lemma resume_pending_drained_context_components:
  "rpc_live (resume_pending_drained_context C t rest) = rpc_live C \<and>
   rpc_tasks (resume_pending_drained_context C t rest) = rest \<and>
   rpc_generic_roots (resume_pending_drained_context C t rest) =
     rpc_generic_roots C \<and>
   rpc_event_roots (resume_pending_drained_context C t rest) =
     rpc_event_roots C \<and>
   rpc_pending_root (resume_pending_drained_context C t rest) =
     rpc_pending_root C \<and>
   rpc_generic_owner (resume_pending_drained_context C t rest) =
     rpc_generic_owner C \<and>
   rpc_ready_root (resume_pending_drained_context C t rest) =
     rpc_ready_root C \<and>
   rpc_priority (resume_pending_drained_context C t rest) =
     rpc_priority C \<and>
   rpc_current_priority (resume_pending_drained_context C t rest) =
     rpc_current_priority C \<and>
   rpc_K_G (resume_pending_drained_context C t rest) = rpc_K_G C \<and>
   rpc_K_E (resume_pending_drained_context C t rest) = rpc_K_E C \<and>
   rpc_entry_top (resume_pending_drained_context C t rest) =
     max (rpc_entry_top C) (rpc_priority C t)"
  by (simp add: resume_pending_drained_context_def)

lemma resume_pending_drained_generic_at:
  assumes ne:
    "rpc_generic_owner C t \<noteq> rpc_ready_root C (rpc_priority C t)"
  shows
    "rps_generic_family (resume_pending_drained_snapshot C t S) g =
       (if g = rpc_ready_root C (rpc_priority C t)
        then list_insert_end_abs (Generic t) (rpc_K_G C t)
               (rps_generic_family S g)
        else if g = rpc_generic_owner C t
        then list_remove_abs (Generic t) (rps_generic_family S g)
        else rps_generic_family S g)"
  using ne
  by (simp add: resume_pending_drained_snapshot_def
      resume_pending_ready_insert_state_def
      resume_pending_raise_top_state_def
      resume_pending_generic_unlink_state_def
      resume_pending_event_unlink_state_def Let_def)

lemma resume_pending_drained_event_at:
  "rps_event_family (resume_pending_drained_snapshot C t S) e =
     (if e = rpc_pending_root C
      then list_remove_abs (Event t) (rps_event_family S e)
      else rps_event_family S e)"
  by (simp add: resume_pending_drained_snapshot_def
      resume_pending_ready_insert_state_def
      resume_pending_raise_top_state_def
      resume_pending_generic_unlink_state_def
      resume_pending_event_unlink_state_def Let_def)

lemma resume_pending_drained_snapshot_scalars:
  "rps_generic_payload (resume_pending_drained_snapshot C t S) =
     rps_generic_payload S \<and>
   rps_event_payload (resume_pending_drained_snapshot C t S) =
     rps_event_payload S \<and>
   rps_top (resume_pending_drained_snapshot C t S) =
     max (rps_top S) (rpc_priority C t) \<and>
   rps_local_yield (resume_pending_drained_snapshot C t S) =
     rps_local_yield S"
  by (simp add: resume_pending_drained_snapshot_def
      resume_pending_ready_insert_state_def
      resume_pending_raise_top_state_def
      resume_pending_generic_unlink_state_def
      resume_pending_event_unlink_state_def Let_def)

section \<open>Facts the entry relation supplies about the head task\<close>

lemma resume_pending_entry_head_facts:
  assumes pure: "resume_pending_entry_rel C S"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "t \<in> rpc_live C \<and>
     rpc_priority C t < 4 \<and>
     rpc_generic_owner C t \<in> rpc_generic_roots C \<and>
     rpc_ready_root C (rpc_priority C t) \<in> rpc_generic_roots C \<and>
     rpc_generic_owner C t \<noteq> rpc_ready_root C (rpc_priority C t)"
proof -
  have wf: "resume_pending_context_wf C"
    using pure by (simp add: resume_pending_entry_rel_def)
  have t_pending: "t \<in> set (rpc_tasks C)"
    using tasks by simp
  have live: "t \<in> rpc_live C"
    using wf t_pending
    by (auto simp: resume_pending_context_wf_def)
  show ?thesis
    using wf t_pending live
    by (auto simp: resume_pending_context_wf_def)
qed

lemma resume_pending_drained_context_wf:
  assumes wf: "resume_pending_context_wf C"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "resume_pending_context_wf
       (resume_pending_drained_context C t rest)"
proof -
  have t_live: "t \<in> rpc_live C"
    using wf tasks by (auto simp: resume_pending_context_wf_def)
  have pri: "rpc_priority C t < 4"
    using wf t_live by (auto simp: resume_pending_context_wf_def)
  show ?thesis
    using wf tasks pri
    by (auto simp: resume_pending_context_wf_def
        resume_pending_drained_context_def)
qed

lemma resume_pending_entry_uniqueD:
  assumes pure: "resume_pending_entry_rel C S"
    and tasks: "rpc_tasks C = t # rest"
    and root: "g \<in> rpc_generic_roots C"
  shows
    "Generic t \<in> set (ring (rps_generic_family S g)) \<longleftrightarrow>
       g = rpc_generic_owner C t"
  using pure tasks root
  by (auto simp: resume_pending_entry_rel_def)

lemma resume_pending_entry_wf_atD:
  assumes pure: "resume_pending_entry_rel C S"
    and root: "g \<in> rpc_generic_roots C"
  shows "xlist_wf (rps_generic_family S g)"
  using pure root
  by (simp add: resume_pending_entry_rel_def
      resume_pending_family_shape_def)

lemma resume_pending_entry_event_wf_atD:
  assumes pure: "resume_pending_entry_rel C S"
    and root: "e \<in> rpc_event_roots C"
  shows "xlist_wf (rps_event_family S e)"
  using pure root
  by (simp add: resume_pending_entry_rel_def
      resume_pending_family_shape_def)

lemma resume_pending_entry_fresh_targetD:
  assumes pure: "resume_pending_entry_rel C S"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "Generic t \<notin>
       set (ring (rps_generic_family S
         (rpc_ready_root C (rpc_priority C t))))"
proof -
  have target_root:
    "rpc_ready_root C (rpc_priority C t) \<in> rpc_generic_roots C"
    using resume_pending_entry_head_facts[OF pure tasks] by blast
  have ne:
    "rpc_generic_owner C t \<noteq> rpc_ready_root C (rpc_priority C t)"
    using resume_pending_entry_head_facts[OF pure tasks] by blast
  show ?thesis
    using resume_pending_entry_uniqueD[OF pure tasks target_root] ne
    by simp
qed

section \<open>Ring sets of the drained families\<close>

lemma resume_pending_drained_generic_ring_set:
  assumes pure: "resume_pending_entry_rel C S"
    and tasks: "rpc_tasks C = t # rest"
    and root: "g \<in> rpc_generic_roots C"
  shows
    "set (ring (rps_generic_family
       (resume_pending_drained_snapshot C t S) g)) =
       (if g = rpc_ready_root C (rpc_priority C t)
        then insert (Generic t)
               (set (ring (rps_generic_family S g)))
        else if g = rpc_generic_owner C t
        then set (ring (rps_generic_family S g)) - {Generic t}
        else set (ring (rps_generic_family S g)))"
proof -
  have ne:
    "rpc_generic_owner C t \<noteq> rpc_ready_root C (rpc_priority C t)"
    using resume_pending_entry_head_facts[OF pure tasks] by blast
  show ?thesis
  proof (cases "g = rpc_ready_root C (rpc_priority C t)")
    case True
    show ?thesis
      using resume_pending_drained_generic_at[OF ne, of S g] True
        ring_set_insert_end[OF resume_pending_entry_wf_atD[OF pure root]]
      by simp
  next
    case False
    have distinct: "distinct (ring (rps_generic_family S g))"
      using resume_pending_entry_wf_atD[OF pure root]
      by (simp add: xlist_wf_def)
    show ?thesis
    proof (cases "g = rpc_generic_owner C t")
      case True_owner: True
      have sets:
        "set (remove1 (Generic t) (ring (rps_generic_family S g))) =
           set (ring (rps_generic_family S g)) - {Generic t}"
        by (rule set_remove1_eq[OF distinct])
      show ?thesis
        using resume_pending_drained_generic_at[OF ne, of S g] False
          True_owner sets
        by (simp add: list_remove_abs_def)
    next
      case False_owner: False
      show ?thesis
        using resume_pending_drained_generic_at[OF ne, of S g] False
          False_owner
        by simp
    qed
  qed
qed

lemma resume_pending_drained_event_ring_set:
  assumes pure: "resume_pending_entry_rel C S"
    and root: "e \<in> rpc_event_roots C"
  shows
    "set (ring (rps_event_family
       (resume_pending_drained_snapshot C t S) e)) =
       (if e = rpc_pending_root C
        then set (ring (rps_event_family S e)) - {Event t}
        else set (ring (rps_event_family S e)))"
proof -
  have distinct: "distinct (ring (rps_event_family S e))"
    using resume_pending_entry_event_wf_atD[OF pure root]
    by (simp add: xlist_wf_def)
  show ?thesis
  proof (cases "e = rpc_pending_root C")
    case True
    have sets:
      "set (remove1 (Event t) (ring (rps_event_family S e))) =
         set (ring (rps_event_family S e)) - {Event t}"
      by (rule set_remove1_eq[OF distinct])
    show ?thesis
      using resume_pending_drained_event_at[of C t S e] True sets
      by (simp add: list_remove_abs_def)
  next
    case False
    show ?thesis
      using resume_pending_drained_event_at[of C t S e] False
      by simp
  qed
qed

section \<open>Old per-task and key facts from the entry relation\<close>

lemma resume_pending_entry_taskD:
  assumes pure: "resume_pending_entry_rel C S"
    and pending_u: "u \<in> set (rpc_tasks C)"
  shows
    "Generic u \<in>
       set (ring (rps_generic_family S (rpc_generic_owner C u))) \<and>
     (\<forall>g\<in>rpc_generic_roots C.
        Generic u \<in> set (ring (rps_generic_family S g)) \<longleftrightarrow>
          g = rpc_generic_owner C u) \<and>
     item_key (rps_generic_family S (rpc_generic_owner C u))
       (Generic u) = rpc_K_G C u"
  using pure pending_u
  by (auto simp: resume_pending_entry_rel_def)

lemma resume_pending_entry_generic_keyD:
  assumes pure: "resume_pending_entry_rel C S"
    and root: "g \<in> rpc_generic_roots C"
    and member: "Generic u \<in> set (ring (rps_generic_family S g))"
  shows "item_key (rps_generic_family S g) (Generic u) = rpc_K_G C u"
proof -
  have u_live: "u \<in> rpc_live C"
    using pure root member
    by (auto simp: resume_pending_entry_rel_def
        resume_pending_family_shape_def)
  show ?thesis
    using pure root member u_live
    by (auto simp: resume_pending_entry_rel_def
        resume_pending_family_shape_def)
qed

lemma resume_pending_entry_event_keyD:
  assumes pure: "resume_pending_entry_rel C S"
    and root: "e \<in> rpc_event_roots C"
    and member: "Event u \<in> set (ring (rps_event_family S e))"
  shows "item_key (rps_event_family S e) (Event u) = rpc_K_E C u"
proof -
  have u_live: "u \<in> rpc_live C"
    using pure root member
    by (auto simp: resume_pending_entry_rel_def
        resume_pending_family_shape_def)
  show ?thesis
    using pure root member u_live
    by (auto simp: resume_pending_entry_rel_def
        resume_pending_family_shape_def)
qed

section \<open>Keys of the drained generic family\<close>

lemma resume_pending_drained_generic_keyD:
  assumes pure: "resume_pending_entry_rel C S"
    and tasks: "rpc_tasks C = t # rest"
    and root: "g \<in> rpc_generic_roots C"
    and member:
      "Generic u \<in> set (ring (rps_generic_family
        (resume_pending_drained_snapshot C t S) g))"
  shows
    "item_key (rps_generic_family
       (resume_pending_drained_snapshot C t S) g) (Generic u) =
     rpc_K_G C u"
proof -
  have ne:
    "rpc_generic_owner C t \<noteq> rpc_ready_root C (rpc_priority C t)"
    using resume_pending_entry_head_facts[OF pure tasks] by blast
  show ?thesis
  proof (cases "g = rpc_ready_root C (rpc_priority C t)")
    case True
    have expand:
      "rps_generic_family (resume_pending_drained_snapshot C t S) g =
         list_insert_end_abs (Generic t) (rpc_K_G C t)
           (rps_generic_family S g)"
      using resume_pending_drained_generic_at[OF ne, of S g] True
      by simp
    show ?thesis
    proof (cases "u = t")
      case True_u: True
      show ?thesis
        using expand True_u by (simp add: list_insert_end_abs_def)
    next
      case False_u: False
      have old_member:
        "Generic u \<in> set (ring (rps_generic_family S g))"
        using member
          resume_pending_drained_generic_ring_set[OF pure tasks root]
          True False_u by auto
      show ?thesis
        using expand False_u
          resume_pending_entry_generic_keyD[OF pure root old_member]
        by (simp add: list_insert_end_abs_def)
    qed
  next
    case False
    have expand:
      "rps_generic_family (resume_pending_drained_snapshot C t S) g =
         (if g = rpc_generic_owner C t
          then list_remove_abs (Generic t) (rps_generic_family S g)
          else rps_generic_family S g)"
      using resume_pending_drained_generic_at[OF ne, of S g] False
      by simp
    have old_member:
      "Generic u \<in> set (ring (rps_generic_family S g))"
      using member
        resume_pending_drained_generic_ring_set[OF pure tasks root]
        False by (auto split: if_splits)
    note old_key =
      resume_pending_entry_generic_keyD[OF pure root old_member]
    show ?thesis
    proof (cases "g = rpc_generic_owner C t")
      case True_owner: True
      show ?thesis
        using expand True_owner old_key
        by (simp add: item_key_remove)
    next
      case False_owner: False
      show ?thesis
        using expand False_owner old_key by simp
    qed
  qed
qed

section \<open>The pure entry relation re-established after one drain\<close>

theorem resume_pending_drained_entry_rel:
  assumes pure: "resume_pending_entry_rel C S"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "resume_pending_entry_rel
       (resume_pending_drained_context C t rest)
       (resume_pending_drained_snapshot C t S)"
proof -
  note head = resume_pending_entry_head_facts[OF pure tasks]
  have ne:
    "rpc_generic_owner C t \<noteq> rpc_ready_root C (rpc_priority C t)"
    using head by blast
  have t_live: "t \<in> rpc_live C" using head by blast
  have wf: "resume_pending_context_wf C"
    using pure by (simp add: resume_pending_entry_rel_def)
  have shape: "resume_pending_family_shape C S"
    using pure by (simp add: resume_pending_entry_rel_def)
  have distinct_tasks: "distinct (t # rest)"
    using wf tasks by (simp add: resume_pending_context_wf_def)

  have wf': "resume_pending_context_wf
      (resume_pending_drained_context C t rest)"
    by (rule resume_pending_drained_context_wf[OF wf tasks])

  have generic_wf':
    "\<And>g. g \<in> rpc_generic_roots C \<Longrightarrow>
       xlist_wf (rps_generic_family
         (resume_pending_drained_snapshot C t S) g) \<and>
       generic_ring (rps_generic_family
         (resume_pending_drained_snapshot C t S) g) \<and>
       set (ring (rps_generic_family
         (resume_pending_drained_snapshot C t S) g)) \<subseteq>
         Generic ` rpc_live C"
  proof -
    fix g assume root: "g \<in> rpc_generic_roots C"
    have old_wf: "xlist_wf (rps_generic_family S g)"
      by (rule resume_pending_entry_wf_atD[OF pure root])
    have old_kind: "generic_ring (rps_generic_family S g)"
      using shape root by (simp add: resume_pending_family_shape_def)
    have old_sub:
      "set (ring (rps_generic_family S g)) \<subseteq> Generic ` rpc_live C"
      using shape root by (simp add: resume_pending_family_shape_def)
    show "?thesis g"
    proof (cases "g = rpc_ready_root C (rpc_priority C t)")
      case True
      have fresh:
        "Generic t \<notin> set (ring (rps_generic_family S g))"
        using resume_pending_entry_fresh_targetD[OF pure tasks] True
        by simp
      show ?thesis
        using resume_pending_drained_generic_at[OF ne, of S g] True
          xlist_wf_insert_end[OF old_wf fresh]
          generic_ring_insert_end[OF old_wf old_kind]
          ring_set_insert_end[OF old_wf] old_sub t_live
        by simp
    next
      case False
      have removed_ring:
        "ring (list_remove_abs (Generic t) (rps_generic_family S g)) =
           remove1 (Generic t) (ring (rps_generic_family S g))"
        by (simp add: list_remove_abs_def)
      have removed_sub:
        "set (ring (list_remove_abs (Generic t)
           (rps_generic_family S g))) \<subseteq> Generic ` rpc_live C"
        using removed_ring
          set_remove1_subset[of "Generic t"
            "ring (rps_generic_family S g)"] old_sub
        by auto
      show ?thesis
      proof (cases "g = rpc_generic_owner C t")
        case True_owner: True
        show ?thesis
          using resume_pending_drained_generic_at[OF ne, of S g]
            False True_owner xlist_wf_remove[OF old_wf]
            generic_ring_remove[OF old_kind] removed_sub
          by simp
      next
        case False_owner: False
        show ?thesis
          using resume_pending_drained_generic_at[OF ne, of S g]
            False False_owner old_wf old_kind old_sub
          by simp
      qed
    qed
  qed

  have event_wf':
    "\<And>e. e \<in> rpc_event_roots C \<Longrightarrow>
       xlist_wf (rps_event_family
         (resume_pending_drained_snapshot C t S) e) \<and>
       event_ring (rps_event_family
         (resume_pending_drained_snapshot C t S) e) \<and>
       set (ring (rps_event_family
         (resume_pending_drained_snapshot C t S) e)) \<subseteq>
         Event ` rpc_live C"
  proof -
    fix e assume root: "e \<in> rpc_event_roots C"
    have old_wf: "xlist_wf (rps_event_family S e)"
      by (rule resume_pending_entry_event_wf_atD[OF pure root])
    have old_kind: "event_ring (rps_event_family S e)"
      using shape root by (simp add: resume_pending_family_shape_def)
    have old_sub:
      "set (ring (rps_event_family S e)) \<subseteq> Event ` rpc_live C"
      using shape root by (simp add: resume_pending_family_shape_def)
    have removed_ring:
      "ring (list_remove_abs (Event t) (rps_event_family S e)) =
         remove1 (Event t) (ring (rps_event_family S e))"
      by (simp add: list_remove_abs_def)
    have removed_sub:
      "set (ring (list_remove_abs (Event t)
         (rps_event_family S e))) \<subseteq> Event ` rpc_live C"
      using removed_ring
        set_remove1_subset[of "Event t" "ring (rps_event_family S e)"]
        old_sub
      by auto
    show "?thesis e"
    proof (cases "e = rpc_pending_root C")
      case True
      show ?thesis
        using resume_pending_drained_event_at[of C t S e] True
          xlist_wf_remove[OF old_wf] event_ring_remove[OF old_kind]
          removed_sub
        by simp
    next
      case False
      show ?thesis
        using resume_pending_drained_event_at[of C t S e] False
          old_wf old_kind old_sub
        by simp
    qed
  qed

  have generic_pairwise':
    "\<And>g g'. g \<in> rpc_generic_roots C \<Longrightarrow>
       g' \<in> rpc_generic_roots C \<Longrightarrow> g \<noteq> g' \<Longrightarrow>
       set (ring (rps_generic_family
         (resume_pending_drained_snapshot C t S) g)) \<inter>
       set (ring (rps_generic_family
         (resume_pending_drained_snapshot C t S) g')) = {}"
  proof -
    fix g g'
    assume root: "g \<in> rpc_generic_roots C"
      and root': "g' \<in> rpc_generic_roots C"
      and distinct_roots: "g \<noteq> g'"
    have old:
      "set (ring (rps_generic_family S g)) \<inter>
         set (ring (rps_generic_family S g')) = {}"
      using shape root root' distinct_roots
      by (simp add: resume_pending_family_shape_def)
    show "?thesis g g'"
      using resume_pending_drained_generic_ring_set[OF pure tasks root]
        resume_pending_drained_generic_ring_set[OF pure tasks root']
        resume_pending_entry_uniqueD[OF pure tasks root]
        resume_pending_entry_uniqueD[OF pure tasks root']
        old distinct_roots ne
      by (auto split: if_splits)
  qed

  have event_pairwise':
    "\<And>e e'. e \<in> rpc_event_roots C \<Longrightarrow>
       e' \<in> rpc_event_roots C \<Longrightarrow> e \<noteq> e' \<Longrightarrow>
       set (ring (rps_event_family
         (resume_pending_drained_snapshot C t S) e)) \<inter>
       set (ring (rps_event_family
         (resume_pending_drained_snapshot C t S) e')) = {}"
  proof -
    fix e e'
    assume root: "e \<in> rpc_event_roots C"
      and root': "e' \<in> rpc_event_roots C"
      and distinct_roots: "e \<noteq> e'"
    have old:
      "set (ring (rps_event_family S e)) \<inter>
         set (ring (rps_event_family S e')) = {}"
      using shape root root' distinct_roots
      by (simp add: resume_pending_family_shape_def)
    show "?thesis e e'"
      using resume_pending_drained_event_ring_set[OF pure root, of t]
        resume_pending_drained_event_ring_set[OF pure root', of t]
        old
      by (auto split: if_splits)
  qed

  have event_key':
    "\<And>e u. e \<in> rpc_event_roots C \<Longrightarrow>
       Event u \<in> set (ring (rps_event_family
         (resume_pending_drained_snapshot C t S) e)) \<Longrightarrow>
       item_key (rps_event_family
         (resume_pending_drained_snapshot C t S) e) (Event u) =
       rpc_K_E C u"
  proof -
    fix e u
    assume root: "e \<in> rpc_event_roots C"
      and member:
        "Event u \<in> set (ring (rps_event_family
          (resume_pending_drained_snapshot C t S) e))"
    have old_member:
      "Event u \<in> set (ring (rps_event_family S e))"
      using member resume_pending_drained_event_ring_set[OF pure root]
      by (auto split: if_splits)
    note old_key =
      resume_pending_entry_event_keyD[OF pure root old_member]
    show "?thesis e u"
    proof (cases "e = rpc_pending_root C")
      case True
      show ?thesis
        using resume_pending_drained_event_at[of C t S e] True old_key
        by (simp add: item_key_remove)
    next
      case False
      show ?thesis
        using resume_pending_drained_event_at[of C t S e] False old_key
        by simp
    qed
  qed

  have payload':
    "\<And>u. u \<in> rpc_live C \<Longrightarrow>
       rps_generic_payload (resume_pending_drained_snapshot C t S) u =
         rpc_K_G C u \<and>
       rps_event_payload (resume_pending_drained_snapshot C t S) u =
         rpc_K_E C u"
  proof -
    fix u assume u_live: "u \<in> rpc_live C"
    have old:
      "rps_generic_payload S u = rpc_K_G C u \<and>
       rps_event_payload S u = rpc_K_E C u"
      using shape u_live
      by (simp add: resume_pending_family_shape_def)
    show "?thesis u"
      using resume_pending_drained_snapshot_scalars[of C t S] old
      by simp
  qed
  have shape':
    "resume_pending_family_shape
       (resume_pending_drained_context C t rest)
       (resume_pending_drained_snapshot C t S)"
    unfolding resume_pending_family_shape_def
    using generic_wf' event_wf' generic_pairwise' event_pairwise'
      resume_pending_drained_generic_keyD[OF pure tasks] event_key'
      payload'
    by (auto simp: resume_pending_drained_context_def)

  have pending_ring':
    "ring (rps_event_family (resume_pending_drained_snapshot C t S)
       (rpc_pending_root C)) = map Event rest"
  proof -
    have entry_ring:
      "ring (rps_event_family S (rpc_pending_root C)) =
         Event t # map Event rest"
      using pure tasks by (simp add: resume_pending_entry_rel_def)
    show ?thesis
      using resume_pending_drained_event_at[of C t S
          "rpc_pending_root C"] entry_ring
      by (simp add: list_remove_abs_def)
  qed

  have per_task':
    "\<And>u. u \<in> set rest \<Longrightarrow>
       Generic u \<in> set (ring (rps_generic_family
         (resume_pending_drained_snapshot C t S)
         (rpc_generic_owner C u))) \<and>
       (\<forall>g\<in>rpc_generic_roots C.
          Generic u \<in> set (ring (rps_generic_family
            (resume_pending_drained_snapshot C t S) g)) \<longleftrightarrow>
            g = rpc_generic_owner C u) \<and>
       item_key (rps_generic_family
         (resume_pending_drained_snapshot C t S)
         (rpc_generic_owner C u)) (Generic u) = rpc_K_G C u"
  proof -
    fix u assume u_rest: "u \<in> set rest"
    have u_pending: "u \<in> set (rpc_tasks C)"
      using tasks u_rest by simp
    have u_ne_t: "u \<noteq> t"
      using distinct_tasks u_rest by auto
    note old = resume_pending_entry_taskD[OF pure u_pending]
    have owner_root: "rpc_generic_owner C u \<in> rpc_generic_roots C"
      using wf u_pending
      by (auto simp: resume_pending_context_wf_def)
    have owner_ne_target:
      "rpc_generic_owner C u \<noteq>
         rpc_ready_root C (rpc_priority C t)"
      using wf u_pending t_live
      by (auto simp: resume_pending_context_wf_def)
    have membership:
      "Generic u \<in> set (ring (rps_generic_family
         (resume_pending_drained_snapshot C t S)
         (rpc_generic_owner C u)))"
      using resume_pending_drained_generic_ring_set[OF pure tasks
          owner_root] old u_ne_t owner_ne_target
      by (auto split: if_splits)
    have uniqueness:
      "\<forall>g\<in>rpc_generic_roots C.
         Generic u \<in> set (ring (rps_generic_family
           (resume_pending_drained_snapshot C t S) g)) \<longleftrightarrow>
           g = rpc_generic_owner C u"
    proof
      fix g assume root: "g \<in> rpc_generic_roots C"
      show "Generic u \<in> set (ring (rps_generic_family
          (resume_pending_drained_snapshot C t S) g)) \<longleftrightarrow>
          g = rpc_generic_owner C u"
        using resume_pending_drained_generic_ring_set[OF pure tasks
            root] old root u_ne_t
        by (auto split: if_splits)
    qed
    have key:
      "item_key (rps_generic_family
         (resume_pending_drained_snapshot C t S)
         (rpc_generic_owner C u)) (Generic u) = rpc_K_G C u"
      by (rule resume_pending_drained_generic_keyD[OF pure tasks
          owner_root membership])
    show "?thesis u"
      using membership uniqueness key by blast
  qed

  have top':
    "rps_top (resume_pending_drained_snapshot C t S) =
       rpc_entry_top (resume_pending_drained_context C t rest)"
  proof -
    have entry_top: "rps_top S = rpc_entry_top C"
      using pure by (simp add: resume_pending_entry_rel_def)
    show ?thesis
      using resume_pending_drained_snapshot_scalars[of C t S] entry_top
      by (simp add: resume_pending_drained_context_components)
  qed

  have yield':
    "\<not> rps_local_yield (resume_pending_drained_snapshot C t S)"
    using resume_pending_drained_snapshot_scalars[of C t S] pure
    by (simp add: resume_pending_entry_rel_def)

  show ?thesis
    unfolding resume_pending_entry_rel_def
    using wf' shape' pending_ring' per_task' top' yield'
    by (simp add: resume_pending_drained_context_components)
qed

end
