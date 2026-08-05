theory Scheduler_One_Due_Task_Phases_Reentry_GateH
  imports
    "EAL6_FreeRTOS_V611_Scheduler_One_Due_Task_Phases_Reentry_Pure.Scheduler_One_Due_Task_Phases_Reentry_Pure"
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Insert_Owner_Frame.Scheduler_Resume_Generated_Insert_Owner_Frame"
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Insert_Key_Frame.Scheduler_Resume_Generated_Insert_Key_Frame"
begin

text \<open>
  Concrete re-entry clauses at the insert heap.  The raw generic family
  after one completed tick-body iteration is the insert-end family over
  the after-remove family; this file re-establishes the gate-level
  clauses of the entry relation at that family and heap, one clause per
  lemma, so the loop-invariant assembly can consume them without
  re-proving heap facts.
\<close>

lemma set_insert_after_subset:
  "set (insert_after c x ys) \<subseteq> insert x (set ys)"
  by (induction ys) auto

lemma list_insert_end_abs_ring_subset:
  "set (ring (list_insert_end_abs x k xs)) \<subseteq>
     insert x (set (ring xs))"
  by (cases "cursor xs")
     (auto simp: list_insert_end_abs_def
       dest!: subsetD[OF set_insert_after_subset])

definition one_due_reentry_generic_raw ::
  "'tid scheduler_decode \<Rightarrow>
   ('tid, xLIST_C ptr) one_due_context \<Rightarrow>
   heap_mem \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs)"
where
  "one_due_reentry_generic_raw D C h fam =
     scheduler_family_insert_end_raw h
       (one_due_generic_raw_after_remove D C fam)
       (one_due_target_root C)
       (one_due_generic_raw_ptr D (odc_task C))"

lemma one_due_reentry_generic_pre_rel:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
  shows
    "scheduler_family_pre_rel
       (one_due_ready_insert_heap D C generic_raw
         (one_due_event_remove_heap D C branch
           (one_due_generic_remove_heap D C
             (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))))
       (odc_generic_roots C)
       (one_due_reentry_generic_raw D C
         (one_due_event_remove_heap D C branch
           (one_due_generic_remove_heap D C
             (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))))
         generic_raw)
       (odc_live C) D"
  using one_due_insert_family_pre_rel[OF rel]
  by (simp add: one_due_reentry_generic_raw_def)

lemma one_due_gateH_generic_ring_subsetD:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
  shows
    "\<forall>r\<in>odc_generic_roots C.
       set (ring (generic_raw r)) \<subseteq>
         one_due_generic_raw_set (odc_live C) D"
  using rel
  unfolding one_due_gateH_entry_rel_def Let_def
  by blast

lemma one_due_reentry_generic_ring_subset:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
  shows
    "\<forall>r\<in>odc_generic_roots C.
       set (ring (one_due_reentry_generic_raw D C h generic_raw r))
         \<subseteq> one_due_generic_raw_set (odc_live C) D"
proof
  fix r
  assume r_root: "r \<in> odc_generic_roots C"
  note base = one_due_gateH_generic_ring_subsetD[OF rel]
  have task_live: "odc_task C \<in> odc_live C"
    by (rule one_due_gateH_task_liveD[OF rel])
  have p_in:
    "one_due_generic_raw_ptr D (odc_task C) \<in>
       one_due_generic_raw_set (odc_live C) D"
    using task_live by (auto simp: one_due_generic_raw_set_def)
  have source_root: "odc_delayed_root C \<in> odc_generic_roots C"
    and target_ne: "one_due_target_root C \<noteq> odc_delayed_root C"
    using one_due_gateH_pure_entryD[OF rel]
    by (auto simp: one_due_entry_rel_def one_due_context_wf_def)
  have base_r: "set (ring (generic_raw r)) \<subseteq>
    one_due_generic_raw_set (odc_live C) D"
    using base r_root by blast
  have base_src: "set (ring (generic_raw (odc_delayed_root C))) \<subseteq>
    one_due_generic_raw_set (odc_live C) D"
    using base source_root by blast
  show "set (ring (one_due_reentry_generic_raw D C h generic_raw r))
      \<subseteq> one_due_generic_raw_set (odc_live C) D"
  proof (cases "r = one_due_target_root C")
    case True
    then show ?thesis
      using base_r p_in target_ne
      by (auto simp: one_due_reentry_generic_raw_def
          scheduler_family_insert_end_raw_def
          one_due_generic_raw_after_remove_def
          dest!: subsetD[OF list_insert_end_abs_ring_subset])
  next
    case False
    then show ?thesis
      using base_r base_src
      by (auto simp: one_due_reentry_generic_raw_def
          scheduler_family_insert_end_raw_def
          one_due_generic_raw_after_remove_def
          dest!: subsetD[OF list_remove_abs_ring_subset])
  qed
qed

text \<open>
  Relabel transport through the model-level remove and insert-end
  operations.  Decode injectivity on the ring extended by the moved
  node aligns the two removals positionally; the cursor branch is
  matched through the predecessor walk.
\<close>

lemma list_all2_decode_remove1:
  fixes dec :: "'a \<Rightarrow> 'b option"
  assumes all2: "list_all2 (\<lambda>u w. dec u = Some w) xs ys"
    and pn: "dec p = Some n"
    and uniq: "\<And>u. u \<in> set xs \<Longrightarrow> dec u = Some n \<Longrightarrow> u = p"
  shows "list_all2 (\<lambda>u w. dec u = Some w)
     (remove1 p xs) (remove1 n ys)"
  using all2 uniq
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  obtain y ys' where ys_eq: "ys = y # ys'"
    and hx: "dec x = Some y"
    and rest: "list_all2 (\<lambda>u w. dec u = Some w) xs ys'"
    using Cons.prems(1) by (auto simp: list_all2_Cons1)
  show ?case
  proof (cases "x = p")
    case True
    have "y = n" using hx pn True by simp
    then show ?thesis using rest ys_eq True by simp
  next
    case False
    have y_ne: "y \<noteq> n"
    proof
      assume "y = n"
      then have "dec x = Some n" using hx by simp
      then have "x = p" using Cons.prems(2) by simp
      then show False using False by simp
    qed
    have uniq': "\<And>u. u \<in> set xs \<Longrightarrow> dec u = Some n \<Longrightarrow>
       u = p"
      using Cons.prems(2) by simp
    have ih: "list_all2 (\<lambda>u w. dec u = Some w)
       (remove1 p xs) (remove1 n ys')"
      by (rule Cons.IH[OF rest uniq'])
    then show ?thesis using ys_eq hx False y_ne by simp
  qed
qed

lemma predecessor_aux_decode:
  fixes dec :: "'a \<Rightarrow> 'b option"
  assumes all2: "list_all2 (\<lambda>u w. dec u = Some w) xs ys"
    and pn: "dec p = Some n"
    and uniq: "\<And>u. u \<in> set xs \<Longrightarrow> dec u = Some n \<Longrightarrow> u = p"
    and prev: "dec u0 = Some w0"
  shows "rel_option (\<lambda>u w. dec u = Some w)
     (predecessor_aux u0 p xs) (predecessor_aux w0 n ys)"
  using all2 uniq prev
proof (induction xs arbitrary: ys u0 w0)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  obtain y ys' where ys_eq: "ys = y # ys'"
    and hx: "dec x = Some y"
    and rest: "list_all2 (\<lambda>u w. dec u = Some w) xs ys'"
    using Cons.prems(1) by (auto simp: list_all2_Cons1)
  show ?case
  proof (cases "x = p")
    case True
    have "y = n" using hx pn True by simp
    then show ?thesis
      using ys_eq True Cons.prems(3) by simp
  next
    case False
    have y_ne: "y \<noteq> n"
    proof
      assume "y = n"
      then have "x = p" using hx Cons.prems(2) by simp
      then show False using False by simp
    qed
    have uniq': "\<And>u. u \<in> set xs \<Longrightarrow> dec u = Some n \<Longrightarrow>
       u = p"
      using Cons.prems(2) by simp
    show ?thesis
      using ys_eq False y_ne Cons.IH[OF rest uniq' hx]
      by simp
  qed
qed

lemma predecessor_decode:
  fixes dec :: "'a \<Rightarrow> 'b option"
  assumes all2: "list_all2 (\<lambda>u w. dec u = Some w) xs ys"
    and pn: "dec p = Some n"
    and uniq: "\<And>u. u \<in> set xs \<Longrightarrow> dec u = Some n \<Longrightarrow> u = p"
  shows "rel_option (\<lambda>u w. dec u = Some w)
     (predecessor p xs) (predecessor n ys)"
proof (cases xs)
  case Nil
  then have "ys = []" using all2 by simp
  then show ?thesis using Nil by simp
next
  case (Cons x xs')
  obtain y ys' where ys_eq: "ys = y # ys'"
    and hx: "dec x = Some y"
    and rest: "list_all2 (\<lambda>u w. dec u = Some w) xs' ys'"
    using all2 Cons by (auto simp: list_all2_Cons1)
  show ?thesis
  proof (cases "x = p")
    case True
    have "y = n" using hx pn True by simp
    then show ?thesis using Cons ys_eq True by simp
  next
    case False
    have y_ne: "y \<noteq> n"
    proof
      assume "y = n"
      then have "x = p" using hx uniq Cons by simp
      then show False using False by simp
    qed
    have uniq': "\<And>u. u \<in> set xs' \<Longrightarrow> dec u = Some n \<Longrightarrow> u = p"
      using uniq Cons by simp
    show ?thesis
      using Cons ys_eq False y_ne
        predecessor_aux_decode[OF rest pn uniq' hx]
      by simp
  qed
qed

lemma insert_after_decode:
  fixes dec :: "'a \<Rightarrow> 'b option"
  assumes all2: "list_all2 (\<lambda>u w. dec u = Some w) xs ys"
    and pn: "dec p = Some n"
    and cm: "dec c = Some m"
    and uniq_c: "\<And>u. u \<in> set xs \<Longrightarrow> dec u = Some m \<Longrightarrow> u = c"
  shows "list_all2 (\<lambda>u w. dec u = Some w)
     (insert_after c p xs) (insert_after m n ys)"
  using all2 uniq_c
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  obtain y ys' where ys_eq: "ys = y # ys'"
    and hx: "dec x = Some y"
    and rest: "list_all2 (\<lambda>u w. dec u = Some w) xs ys'"
    using Cons.prems(1) by (auto simp: list_all2_Cons1)
  show ?case
  proof (cases "x = c")
    case True
    have "y = m" using hx cm True by simp
    then show ?thesis using ys_eq True hx pn rest by simp
  next
    case False
    have y_ne: "y \<noteq> m"
    proof
      assume "y = m"
      then have "x = c" using hx Cons.prems(2) by simp
      then show False using False by simp
    qed
    have uniq': "\<And>u. u \<in> set xs \<Longrightarrow> dec u = Some m \<Longrightarrow>
       u = c"
      using Cons.prems(2) by simp
    show ?thesis
      using ys_eq False y_ne hx Cons.IH[OF rest uniq']
      by simp
  qed
qed

theorem xlist_relabel_remove:
  assumes rel: "xlist_relabel dec rx q"
    and wf_rx: "xlist_wf rx"
    and pn: "dec p = Some n"
    and inj: "\<And>u u'. u \<in> insert p (set (ring rx)) \<Longrightarrow>
       u' \<in> insert p (set (ring rx)) \<Longrightarrow> dec u = dec u' \<Longrightarrow>
       u = u'"
  shows "xlist_relabel dec
     (list_remove_abs p rx) (list_remove_abs n q)"
proof -
  have ring2: "list_all2 (\<lambda>u w. dec u = Some w) (ring rx) (ring q)"
    and cur2: "rel_option (\<lambda>u w. dec u = Some w)
      (cursor rx) (cursor q)"
    and keys: "\<forall>u\<in>set (ring rx). \<forall>w. dec u = Some w \<longrightarrow>
      item_key rx u = item_key q w"
    using rel by (simp_all add: xlist_relabel_def)
  have uniq: "\<And>u. u \<in> set (ring rx) \<Longrightarrow> dec u = Some n \<Longrightarrow> u = p"
  proof -
    fix u
    assume u_in: "u \<in> set (ring rx)" and un: "dec u = Some n"
    show "u = p"
      by (rule inj) (use u_in un pn in auto)
  qed
  have ring2': "list_all2 (\<lambda>u w. dec u = Some w)
     (remove1 p (ring rx)) (remove1 n (ring q))"
    by (rule list_all2_decode_remove1[OF ring2 pn uniq])
  have cur_iff: "(cursor rx = Some p) = (cursor q = Some n)"
  proof
    assume cp: "cursor rx = Some p"
    obtain w where "cursor q = Some w" and "dec p = Some w"
      using cur2 cp by (cases "cursor q") auto
    then show "cursor q = Some n" using pn by simp
  next
    assume cq: "cursor q = Some n"
    obtain u where cu: "cursor rx = Some u" and un: "dec u = Some n"
      using cur2 cq by (cases "cursor rx") auto
    have "u \<in> set (ring rx)"
      using wf_rx cu by (simp add: xlist_wf_def)
    then have "u = p" using uniq un by simp
    then show "cursor rx = Some p" using cu by simp
  qed
  have cur2': "rel_option (\<lambda>u w. dec u = Some w)
     (if cursor rx = Some p then predecessor p (ring rx)
      else cursor rx)
     (if cursor q = Some n then predecessor n (ring q)
      else cursor q)"
    using cur_iff cur2 predecessor_decode[OF ring2 pn uniq]
    by simp
  show ?thesis
    unfolding xlist_relabel_def
  proof (intro conjI)
    show "list_all2 (\<lambda>u w. dec u = Some w)
       (ring (list_remove_abs p rx)) (ring (list_remove_abs n q))"
      using ring2' by (simp add: list_remove_abs_def)
  next
    show "rel_option (\<lambda>u w. dec u = Some w)
       (cursor (list_remove_abs p rx))
       (cursor (list_remove_abs n q))"
      using cur2' by (simp add: list_remove_abs_def)
  next
    show "\<forall>u\<in>set (ring (list_remove_abs p rx)). \<forall>w.
       dec u = Some w \<longrightarrow>
       item_key (list_remove_abs p rx) u =
         item_key (list_remove_abs n q) w"
    proof (intro ballI allI impI)
      fix u w
      assume u_in: "u \<in> set (ring (list_remove_abs p rx))"
        and uw: "dec u = Some w"
      have u_ring: "u \<in> set (ring rx)"
        using u_in
        by (auto simp: list_remove_abs_def
            dest!: subsetD[OF set_remove1_subset])
      have "item_key rx u = item_key q w"
        by (rule keys[rule_format, OF u_ring uw])
      then show "item_key (list_remove_abs p rx) u =
         item_key (list_remove_abs n q) w"
        by (simp add: list_remove_abs_def)
    qed
  qed
qed

lemma list_all2_decode_image:
  fixes dec :: "'a \<Rightarrow> 'b option"
  assumes all2: "list_all2 (\<lambda>u w. dec u = Some w) xs ys"
    and u_in: "u \<in> set xs"
    and uw: "dec u = Some w"
  shows "w \<in> set ys"
proof -
  obtain i where i_lt: "i < length xs" and u_eq: "xs ! i = u"
    using u_in unfolding in_set_conv_nth by blast
  have pair: "dec (xs ! i) = Some (ys ! i)"
    using all2 i_lt by (simp add: list_all2_conv_all_nth)
  have "w = ys ! i" using pair u_eq uw by simp
  moreover have "ys ! i \<in> set ys"
    using all2 i_lt by (simp add: list_all2_conv_all_nth)
  ultimately show ?thesis by simp
qed

lemma list_all2_decode_preimage:
  fixes dec :: "'a \<Rightarrow> 'b option"
  assumes all2: "list_all2 (\<lambda>u w. dec u = Some w) xs ys"
    and w_in: "w \<in> set ys"
  shows "\<exists>u\<in>set xs. dec u = Some w"
proof -
  obtain j where j_lt: "j < length ys" and w_eq: "ys ! j = w"
    using w_in unfolding in_set_conv_nth by blast
  have len: "length xs = length ys"
    using all2 by (simp add: list_all2_conv_all_nth)
  have pair: "dec (xs ! j) = Some (ys ! j)"
    using all2 j_lt len by (simp add: list_all2_conv_all_nth)
  have "xs ! j \<in> set xs" using j_lt len by simp
  then show ?thesis using pair w_eq by auto
qed

theorem xlist_relabel_insert_end:
  assumes rel: "xlist_relabel dec rx q"
    and wf_rx: "xlist_wf rx"
    and pn: "dec p = Some n"
    and fresh: "p \<notin> set (ring rx)"
    and inj: "\<And>u u'. u \<in> insert p (set (ring rx)) \<Longrightarrow>
       u' \<in> insert p (set (ring rx)) \<Longrightarrow> dec u = dec u' \<Longrightarrow>
       u = u'"
  shows "xlist_relabel dec
     (list_insert_end_abs p k rx) (list_insert_end_abs n k q)"
proof -
  have ring2: "list_all2 (\<lambda>u w. dec u = Some w) (ring rx) (ring q)"
    and cur2: "rel_option (\<lambda>u w. dec u = Some w)
      (cursor rx) (cursor q)"
    and keys: "\<forall>u\<in>set (ring rx). \<forall>w. dec u = Some w \<longrightarrow>
      item_key rx u = item_key q w"
    using rel by (simp_all add: xlist_relabel_def)
  have uniq_n: "\<And>u. u \<in> set (ring rx) \<Longrightarrow> dec u = Some n \<Longrightarrow>
     u = p"
  proof -
    fix u
    assume u_in: "u \<in> set (ring rx)" and un: "dec u = Some n"
    show "u = p"
      by (rule inj) (use u_in un pn in auto)
  qed
  have n_absent: "\<And>w. w \<in> set (ring q) \<Longrightarrow> w \<noteq> n"
  proof
    fix w
    assume w_in: "w \<in> set (ring q)" and wn: "w = n"
    obtain u where u_in: "u \<in> set (ring rx)"
      and uw: "dec u = Some w"
      using list_all2_decode_preimage[OF ring2 w_in] by blast
    have "u = p" using uniq_n u_in uw wn by simp
    then show False using fresh u_in by simp
  qed
  have ring2': "list_all2 (\<lambda>u w. dec u = Some w)
     (case cursor rx of
        None \<Rightarrow> p # ring rx
      | Some c \<Rightarrow> insert_after c p (ring rx))
     (case cursor q of
        None \<Rightarrow> n # ring q
      | Some m \<Rightarrow> insert_after m n (ring q))"
  proof (cases "cursor rx")
    case None
    then have "cursor q = None"
      using cur2 by (cases "cursor q") auto
    then show ?thesis using None pn ring2 by simp
  next
    case (Some c)
    obtain m where cq: "cursor q = Some m" and cm: "dec c = Some m"
      using cur2 Some by (cases "cursor q") auto
    have c_in: "c \<in> set (ring rx)"
      using wf_rx Some by (simp add: xlist_wf_def)
    have uniq_c: "\<And>u. u \<in> set (ring rx) \<Longrightarrow> dec u = Some m \<Longrightarrow>
       u = c"
    proof -
      fix u
      assume u_in: "u \<in> set (ring rx)" and um: "dec u = Some m"
      show "u = c"
        by (rule inj) (use u_in um cm c_in in auto)
    qed
    show ?thesis
      using Some cq insert_after_decode[OF ring2 pn cm uniq_c]
      by simp
  qed
  have keys': "\<forall>u\<in>set (case cursor rx of
        None \<Rightarrow> p # ring rx
      | Some c \<Rightarrow> insert_after c p (ring rx)).
     \<forall>w. dec u = Some w \<longrightarrow>
       ((item_key rx)(p := k)) u = ((item_key q)(n := k)) w"
  proof (intro ballI allI impI)
    fix u w
    assume u_in: "u \<in> set (case cursor rx of
        None \<Rightarrow> p # ring rx
      | Some c \<Rightarrow> insert_after c p (ring rx))"
      and uw: "dec u = Some w"
    have u_cases: "u = p \<or> u \<in> set (ring rx)"
      using u_in
      by (cases "cursor rx")
        (auto dest!: subsetD[OF set_insert_after_subset])
    show "((item_key rx)(p := k)) u = ((item_key q)(n := k)) w"
    proof (cases "u = p")
      case True
      then have "w = n" using uw pn by simp
      then show ?thesis using True by simp
    next
      case False
      have u_ring: "u \<in> set (ring rx)" using u_cases False by simp
      have w_in: "w \<in> set (ring q)"
        by (rule list_all2_decode_image[OF ring2 u_ring uw])
      have "w \<noteq> n" using n_absent w_in by simp
      then show ?thesis
        using False u_ring uw keys by simp
    qed
  qed
  show ?thesis
    unfolding xlist_relabel_def
  proof (intro conjI)
    show "list_all2 (\<lambda>u w. dec u = Some w)
       (ring (list_insert_end_abs p k rx))
       (ring (list_insert_end_abs n k q))"
      using ring2' by (simp add: list_insert_end_abs_def)
  next
    show "rel_option (\<lambda>u w. dec u = Some w)
       (cursor (list_insert_end_abs p k rx))
       (cursor (list_insert_end_abs n k q))"
      using pn by (simp add: list_insert_end_abs_def)
  next
    show "\<forall>u\<in>set (ring (list_insert_end_abs p k rx)). \<forall>w.
       dec u = Some w \<longrightarrow>
       item_key (list_insert_end_abs p k rx) u =
         item_key (list_insert_end_abs n k q) w"
    proof (intro ballI allI impI)
      fix u w
      assume u_in: "u \<in> set (ring (list_insert_end_abs p k rx))"
        and uw: "dec u = Some w"
      have u_in': "u \<in> set (case cursor rx of
          None \<Rightarrow> p # ring rx
        | Some c \<Rightarrow> insert_after c p (ring rx))"
        using u_in by (simp add: list_insert_end_abs_def)
      have "((item_key rx)(p := k)) u = ((item_key q)(n := k)) w"
        by (rule keys'[rule_format, OF u_in' uw])
      then show "item_key (list_insert_end_abs p k rx) u =
         item_key (list_insert_end_abs n k q) w"
        by (simp add: list_insert_end_abs_def)
    qed
  qed
qed

lemma raw_xlist_rel_wf:
  "raw_xlist_rel h lp xs \<Longrightarrow> xlist_wf xs"
  by (simp add: raw_xlist_rel_def raw_xlist_view_def)

lemma one_due_generic_raw_set_decode:
  assumes laws: "universal_decoder_laws live D"
    and mem: "u \<in> one_due_generic_raw_set live D"
  shows "\<exists>t\<in>live. u = one_due_generic_raw_ptr D t \<and>
     sd_node_decode D u = Some (Generic t)"
  using laws mem
  by (auto simp: one_due_generic_raw_set_def
      one_due_generic_raw_ptr_def universal_decoder_laws_def)

lemma one_due_generic_decode_inj:
  assumes laws: "universal_decoder_laws live D"
    and u: "sd_node_decode D u = Some (Generic t)"
    and u': "sd_node_decode D u' = Some (Generic t)"
  shows "u = u'"
proof -
  have gen_law:
    "\<forall>p t. sd_node_decode D p = Some (Generic t) \<longrightarrow>
       t \<in> live \<and>
       p = abi_generic_list_item_ptr (sd_tcb_ptr D t)"
    using laws by (simp add: universal_decoder_laws_def)
  have "u = abi_generic_list_item_ptr (sd_tcb_ptr D t)"
    using gen_law u by blast
  moreover have
    "u' = abi_generic_list_item_ptr (sd_tcb_ptr D t)"
    using gen_law u' by blast
  ultimately show ?thesis by simp
qed

text \<open>
  Per-root relabel at the insert heap.  The moved node's raw key at the
  after-event heap equal to its abstract payload is taken as an explicit
  premise here; the field-region frame chain that discharges it is a
  separate rung.
\<close>

lemma one_due_gateH_relabelD:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and r_root: "r \<in> odc_generic_roots C"
  shows
    "xlist_relabel (sd_node_decode D) (generic_raw r)
       (ods_generic_family S r)"
  using rel r_root
  unfolding one_due_gateH_entry_rel_def Let_def
  by blast

lemma one_due_gateH_raw_xlist_relD:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and r_root: "r \<in> odc_generic_roots C"
  shows
    "raw_xlist_rel (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       r (generic_raw r)"
  using one_due_gateH_generic_preD[OF rel] r_root
  by (auto simp: scheduler_family_pre_rel_def raw_family_rel_def)

lemma one_due_gateH_task_ptr_decode:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
  shows
    "sd_node_decode D (one_due_generic_raw_ptr D (odc_task C)) =
       Some (Generic (odc_task C))"
proof -
  have laws: "universal_decoder_laws (odc_live C) D"
    by (rule one_due_gateH_decoder_lawsD[OF rel])
  have task_live: "odc_task C \<in> odc_live C"
    by (rule one_due_gateH_task_liveD[OF rel])
  have bullets:
    "\<forall>t\<in>odc_live C.
       sd_tcb_decode D (sd_tcb_ptr D t) = Some t \<and>
       sd_node_decode D
         (abi_generic_list_item_ptr (sd_tcb_ptr D t)) =
         Some (Generic t) \<and>
       sd_node_decode D
         (abi_event_list_item_ptr (sd_tcb_ptr D t)) =
         Some (Event t)"
    using laws by (simp add: universal_decoder_laws_def)
  show ?thesis
    using bspec[OF bullets task_live]
    by (simp add: one_due_generic_raw_ptr_def)
qed

lemma one_due_gateH_ring_decode_inj:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and r_root: "r \<in> odc_generic_roots C"
    and u_in: "u \<in> insert (one_due_generic_raw_ptr D (odc_task C))
      (set (ring (generic_raw r)))"
    and u'_in: "u' \<in> insert (one_due_generic_raw_ptr D (odc_task C))
      (set (ring (generic_raw r)))"
    and eq: "sd_node_decode D u = sd_node_decode D u'"
  shows "u = u'"
proof -
  have laws: "universal_decoder_laws (odc_live C) D"
    by (rule one_due_gateH_decoder_lawsD[OF rel])
  have task_live: "odc_task C \<in> odc_live C"
    by (rule one_due_gateH_task_liveD[OF rel])
  have p_set:
    "one_due_generic_raw_ptr D (odc_task C) \<in>
       one_due_generic_raw_set (odc_live C) D"
    using task_live by (auto simp: one_due_generic_raw_set_def)
  have ring_sub:
    "set (ring (generic_raw r)) \<subseteq>
       one_due_generic_raw_set (odc_live C) D"
    using one_due_gateH_generic_ring_subsetD[OF rel] r_root by blast
  have u_set: "u \<in> one_due_generic_raw_set (odc_live C) D"
    using u_in p_set ring_sub by blast
  have u'_set: "u' \<in> one_due_generic_raw_set (odc_live C) D"
    using u'_in p_set ring_sub by blast
  obtain t where du: "sd_node_decode D u = Some (Generic t)"
    using one_due_generic_raw_set_decode[OF laws u_set] by blast
  have du': "sd_node_decode D u' = Some (Generic t)"
    using eq du by simp
  show ?thesis
    by (rule one_due_generic_decode_inj[OF laws du du'])
qed

text \<open>
  The moved node's key chain.  Through its own removal the key field
  survives: the unlink writes touch neighbour link fields, the suffix
  writes touch the list header and only the container field of the
  node itself.  Through the branch's Event removal the whole Generic
  item is outside the exact write footprint by storage separation.
\<close>

lemma one_due_gateH_generic_keysD:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and live: "t \<in> odc_live C"
  shows
    "raw_key_at (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (one_due_generic_raw_ptr D t) = ods_generic_payload S t"
  using rel live
  unfolding one_due_gateH_entry_rel_def Let_def
  by blast

lemma raw_remove_container_heap_key_at_removed:
  "raw_key_at (raw_remove_container_heap h p) p = raw_key_at h p"
  by (simp add: raw_remove_container_heap_def raw_key_at_def
      h_val_heap_update)

lemma raw_remove_taken_suffix_heap_key_at_removed:
  assumes layout: "raw_xlist_layout lp rs"
    and removed: "p \<in> set rs"
  shows
    "raw_key_at (raw_remove_taken_suffix_heap h lp p) p =
       raw_key_at h p"
proof -
  let ?hi = "raw_remove_taken_index_heap h lp p"
  let ?hc = "raw_remove_container_heap ?hi p"
  have index_same: "h_val ?hi p = h_val h p"
    by (rule raw_remove_taken_index_heap_preserves_live_item[
        OF layout removed])
  have container_key: "raw_key_at ?hc p = raw_key_at ?hi p"
    by (rule raw_remove_container_heap_key_at_removed)
  have count_same:
    "h_val (raw_remove_count_heap ?hc lp) p = h_val ?hc p"
    by (rule raw_remove_count_heap_preserves_live_item[
        OF layout removed])
  show ?thesis
    using index_same container_key count_same
    by (simp add: raw_remove_taken_suffix_heap_def raw_key_at_def)
qed

lemma raw_remove_plain_suffix_heap_key_at_removed:
  assumes layout: "raw_xlist_layout lp rs"
    and removed: "p \<in> set rs"
  shows
    "raw_key_at (raw_remove_plain_suffix_heap h lp p) p =
       raw_key_at h p"
proof -
  let ?hc = "raw_remove_container_heap h p"
  have container_key: "raw_key_at ?hc p = raw_key_at h p"
    by (rule raw_remove_container_heap_key_at_removed)
  have count_same:
    "h_val (raw_remove_count_heap ?hc lp) p = h_val ?hc p"
    by (rule raw_remove_count_heap_preserves_live_item[
        OF layout removed])
  show ?thesis
    using container_key count_same
    by (simp add: raw_remove_plain_suffix_heap_def raw_key_at_def)
qed

lemma raw_remove_concrete_heap_key_at_removed:
  assumes rel: "raw_xlist_rel h lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "raw_key_at (raw_remove_concrete_heap h p) p = raw_key_at h p"
proof -
  have layout: "raw_xlist_layout lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def)
  have unlink_key:
    "raw_key_at (raw_source_unlink_two h p) p = raw_key_at h p"
    using raw_source_unlink_two_preserves_live_payload[
        OF rel member member]
    by blast
  show ?thesis
  proof (cases
      "pxIndex_C (h_val (raw_source_unlink_two h p) lp) = p")
    case True
    have cast:
      "PTR_COERCE(unit \<rightarrow> xLIST_C)
         (pvContainer_C (h_val (raw_source_unlink_two h p) p)) = lp"
      by (rule raw_source_unlink_two_container_cast[OF rel member])
    have heap_eq:
      "raw_remove_concrete_heap h p =
         raw_remove_taken_suffix_heap
           (raw_source_unlink_two h p) lp p"
      using True cast
      by (simp add: raw_remove_concrete_heap_def
          raw_remove_suffix_heap_def raw_remove_index_heap_def
          raw_remove_taken_index_heap_def
          raw_remove_taken_suffix_heap_def Let_def)
    show ?thesis
      using heap_eq unlink_key
        raw_remove_taken_suffix_heap_key_at_removed[
          OF layout member]
      by simp
  next
    case False
    have cast:
      "PTR_COERCE(unit \<rightarrow> xLIST_C)
         (pvContainer_C (h_val (raw_source_unlink_two h p) p)) = lp"
      by (rule raw_source_unlink_two_container_cast[OF rel member])
    have heap_eq:
      "raw_remove_concrete_heap h p =
         raw_remove_plain_suffix_heap
           (raw_source_unlink_two h p) lp p"
      using False cast
      by (simp add: raw_remove_concrete_heap_def
          raw_remove_suffix_heap_def raw_remove_index_heap_def
          raw_remove_plain_suffix_heap_def Let_def)
    show ?thesis
      using heap_eq unlink_key
        raw_remove_plain_suffix_heap_key_at_removed[
          OF layout member]
      by simp
  qed
qed

lemma one_due_event_remove_source_item_bytes_frame:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and q_member:
      "q \<in> set (ring (generic_raw (odc_delayed_root C)))"
    and addr: "addr \<in> raw_item_region q"
  shows
    "one_due_event_remove_heap D C branch
       (one_due_generic_remove_heap D C
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))) addr =
     one_due_generic_remove_heap D C
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) addr"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  let ?hg = "one_due_generic_remove_heap D C ?h"
  let ?source = "odc_delayed_root C"
  have source_root: "?source \<in> odc_generic_roots C"
    by (rule one_due_gateH_source_in_rootsD[OF rel])
  have q_in_source_storage:
    "addr \<in> raw_xlist_storage ?source (generic_raw ?source)"
    using addr q_member
    by (auto simp: raw_xlist_storage_def)
  show ?thesis
  proof (cases branch)
    case DueEventNull
    then show ?thesis
      by (simp add: one_due_event_remove_heap_def)
  next
    case (DueEventLinked owner)
    have rel_linked:
      "one_due_gateH_entry_rel D R c a C (DueEventLinked owner) S
         generic_raw event_raw"
      using rel DueEventLinked by simp
    have owner_facts:
      "raw_xlist_rel ?hg owner (event_raw owner) \<and>
       event_item_raw_ptr D (odc_task C) \<in>
         set (ring (event_raw owner))"
      by (rule one_due_gateH_linked_event_after_genericD[
          OF rel_linked])
    have owner_root: "owner \<in> odc_event_roots C"
      by (rule one_due_gateH_linked_ownerD[OF rel_linked])
    have footprint:
      "raw_remove_exact_write_footprint ?hg owner
         (event_item_raw_ptr D (odc_task C)) \<subseteq>
       raw_xlist_storage owner (event_raw owner)"
      using owner_facts
      by (intro raw_remove_exact_footprint_subset_storage) blast+
    have disj:
      "raw_xlist_storage ?source (generic_raw ?source) \<inter>
         raw_xlist_storage owner (event_raw owner) = {}"
      by (rule one_due_gateH_storage_disjointD[OF rel source_root
        owner_root])
    have outside:
      "addr \<notin> raw_remove_exact_write_footprint ?hg owner
         (event_item_raw_ptr D (odc_task C))"
      using footprint disj q_in_source_storage by blast
    show ?thesis
      using owner_facts DueEventLinked
      by (auto simp: one_due_event_remove_heap_def
          intro: raw_remove_concrete_heap_exact_external_frame[
            OF _ _ outside])
  qed
qed

lemma one_due_event_remove_key_at_source_member:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and q_member:
      "q \<in> set (ring (generic_raw (odc_delayed_root C)))"
  shows
    "raw_key_at
       (one_due_event_remove_heap D C branch
         (one_due_generic_remove_heap D C
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))) q =
     raw_key_at
       (one_due_generic_remove_heap D C
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))) q"
proof -
  have item_same:
    "h_val
       (one_due_event_remove_heap D C branch
         (one_due_generic_remove_heap D C
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))) q =
     h_val
       (one_due_generic_remove_heap D C
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))) q"
  proof (rule delay_h_val_region_cong)
    fix a
    assume "a \<in> {ptr_val q..+size_of TYPE(xLIST_ITEM_C)}"
    then show
      "one_due_event_remove_heap D C branch
         (one_due_generic_remove_heap D C
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))) a =
       one_due_generic_remove_heap D C
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) a"
      using one_due_event_remove_source_item_bytes_frame[
          OF rel q_member]
      by (simp add: raw_item_region_def)
  qed
  then show ?thesis by (simp add: raw_key_at_def)
qed

theorem one_due_reentry_key_he:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
  shows
    "raw_key_at
       (one_due_event_remove_heap D C branch
         (one_due_generic_remove_heap D C
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))))
       (one_due_generic_raw_ptr D (odc_task C)) =
     ods_generic_payload S (odc_task C)"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  let ?p = "one_due_generic_raw_ptr D (odc_task C)"
  let ?source = "odc_delayed_root C"
  have task_live: "odc_task C \<in> odc_live C"
    by (rule one_due_gateH_task_liveD[OF rel])
  have key_h: "raw_key_at ?h ?p = ods_generic_payload S (odc_task C)"
    by (rule one_due_gateH_generic_keysD[OF rel task_live])
  have source_root: "?source \<in> odc_generic_roots C"
    by (rule one_due_gateH_source_in_rootsD[OF rel])
  have source_rel: "raw_xlist_rel ?h ?source (generic_raw ?source)"
    by (rule one_due_gateH_raw_xlist_relD[OF rel source_root])
  have p_member: "?p \<in> set (ring (generic_raw ?source))"
    by (rule one_due_gateH_source_memberD[OF rel])
  have key_hg:
    "raw_key_at (one_due_generic_remove_heap D C ?h) ?p =
       raw_key_at ?h ?p"
    unfolding one_due_generic_remove_heap_def
    by (rule raw_remove_concrete_heap_key_at_removed[
        OF source_rel p_member])
  have key_he:
    "raw_key_at
       (one_due_event_remove_heap D C branch
         (one_due_generic_remove_heap D C ?h)) ?p =
     raw_key_at (one_due_generic_remove_heap D C ?h) ?p"
    by (rule one_due_event_remove_key_at_source_member[
        OF rel p_member])
  show ?thesis using key_h key_hg key_he by simp
qed

theorem one_due_reentry_relabel:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and key_he:
      "raw_key_at
         (one_due_event_remove_heap D C branch
           (one_due_generic_remove_heap D C
             (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))))
         (one_due_generic_raw_ptr D (odc_task C)) =
       ods_generic_payload S (odc_task C)"
    and r_root: "r \<in> odc_generic_roots C"
  shows
    "xlist_relabel (sd_node_decode D)
       (one_due_reentry_generic_raw D C
         (one_due_event_remove_heap D C branch
           (one_due_generic_remove_heap D C
             (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))))
         generic_raw r)
       (ods_generic_family
         (one_due_reentry_snapshot C branch S) r)"
proof -
  let ?p = "one_due_generic_raw_ptr D (odc_task C)"
  let ?task = "odc_task C"
  let ?source = "odc_delayed_root C"
  let ?target = "one_due_target_root C"
  let ?he = "one_due_event_remove_heap D C branch
    (one_due_generic_remove_heap D C
      (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))"
  have pn: "sd_node_decode D ?p = Some (Generic ?task)"
    by (rule one_due_gateH_task_ptr_decode[OF rel])
  have source_root: "?source \<in> odc_generic_roots C"
    and target_root: "?target \<in> odc_generic_roots C"
    and source_target_ne: "?source \<noteq> ?target"
    using one_due_gateH_pure_entryD[OF rel]
    by (auto simp: one_due_entry_rel_def one_due_context_wf_def)
  have shape: "one_due_family_shape C S"
    using one_due_gateH_pure_entryD[OF rel]
    by (simp add: one_due_entry_rel_def)
  consider (T) "r = ?target"
    | (S) "r \<noteq> ?target" "r = ?source"
    | (O) "r \<noteq> ?target" "r \<noteq> ?source"
    by blast
  then show ?thesis
  proof cases
    case T
    have base: "xlist_relabel (sd_node_decode D)
       (generic_raw ?target) (ods_generic_family S ?target)"
      by (rule one_due_gateH_relabelD[OF rel target_root])
    have wf_raw: "xlist_wf (generic_raw ?target)"
      by (rule raw_xlist_rel_wf[OF
          one_due_gateH_raw_xlist_relD[OF rel target_root]])
    note after_event = one_due_gateH_after_event_obligations[OF rel]
    have fam_target:
      "one_due_generic_raw_after_remove D C generic_raw ?target =
         generic_raw ?target"
      using source_target_ne
      by (simp add: one_due_generic_raw_after_remove_def)
    have fresh0:
      "raw_fresh_for_insert ?target (ring (generic_raw ?target)) ?p"
      using after_event fam_target
      by (simp add: one_due_after_event_obligations_def Let_def)
    have fresh: "?p \<notin> set (ring (generic_raw ?target))"
      using fresh0 by (simp add: raw_fresh_for_insert_def)
    have step: "xlist_relabel (sd_node_decode D)
       (list_insert_end_abs ?p (ods_generic_payload S ?task)
         (generic_raw ?target))
       (list_insert_end_abs (Generic ?task)
         (ods_generic_payload S ?task)
         (ods_generic_family S ?target))"
      by (rule xlist_relabel_insert_end[OF base wf_raw pn fresh
          one_due_gateH_ring_decode_inj[OF rel target_root]])
    show ?thesis
      using step T source_target_ne key_he
      by (simp add: one_due_reentry_generic_raw_def
          scheduler_family_insert_end_raw_def
          one_due_generic_raw_after_remove_def
          one_due_reentry_snapshot_generic_at Let_def)
  next
    case S
    have base: "xlist_relabel (sd_node_decode D)
       (generic_raw ?source) (ods_generic_family S ?source)"
      by (rule one_due_gateH_relabelD[OF rel source_root])
    have wf_raw: "xlist_wf (generic_raw ?source)"
      by (rule raw_xlist_rel_wf[OF
          one_due_gateH_raw_xlist_relD[OF rel source_root]])
    have step: "xlist_relabel (sd_node_decode D)
       (list_remove_abs ?p (generic_raw ?source))
       (list_remove_abs (Generic ?task)
         (ods_generic_family S ?source))"
      by (rule xlist_relabel_remove[OF base wf_raw pn
          one_due_gateH_ring_decode_inj[OF rel source_root]])
    show ?thesis
      using step S
      by (simp add: one_due_reentry_generic_raw_def
          scheduler_family_insert_end_raw_def
          one_due_generic_raw_after_remove_def
          one_due_reentry_snapshot_generic_at Let_def)
  next
    case O
    have base: "xlist_relabel (sd_node_decode D)
       (generic_raw r) (ods_generic_family S r)"
      by (rule one_due_gateH_relabelD[OF rel r_root])
    show ?thesis
      using base O
      by (simp add: one_due_reentry_generic_raw_def
          scheduler_family_insert_end_raw_def
          one_due_generic_raw_after_remove_def
          one_due_reentry_snapshot_generic_at Let_def)
  qed
qed


corollary one_due_reentry_relabel_closed:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and r_root: "r \<in> odc_generic_roots C"
  shows
    "xlist_relabel (sd_node_decode D)
       (one_due_reentry_generic_raw D C
         (one_due_event_remove_heap D C branch
           (one_due_generic_remove_heap D C
             (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))))
         generic_raw r)
       (ods_generic_family
         (one_due_reentry_snapshot C branch S) r)"
  by (rule one_due_reentry_relabel[OF rel
      one_due_reentry_key_he[OF rel] r_root])

text \<open>
  Task observation at the insert heap.  Guards and abstract priorities
  are heap-independent; priority words and both embedded owner
  projections survive the two removals and the insertion through the
  field-region frames.
\<close>

lemma raw_owner_bytes_to_projection:
  assumes bytes: "\<forall>a\<in>raw_owner_field_region q. h' a = h a"
  shows
    "List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
       (h_val h' q) =
     List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
       (h_val h q)"
proof -
  have field_same:
    "h_val h' (raw_owner_field_ptr q) =
       h_val h (raw_owner_field_ptr q)"
  proof (rule delay_h_val_region_cong)
    fix address
    assume "address \<in>
      {ptr_val (raw_owner_field_ptr q)..+size_of TYPE(unit ptr)}"
    then show "h' address = h address"
      using bytes by (simp add: raw_owner_field_region_def)
  qed
  show ?thesis
    using field_same
    unfolding raw_owner_field_ptr_def
    by (simp only:
      List_V611_Raw_Skip_Translation.xLIST_ITEM_C_h_val_fields(4))
qed

lemma one_due_event_owner_projection_transport:
  assumes proj:
    "List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
       (h_val h' (event_item_raw_ptr D u)) =
     List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
       (h_val h (event_item_raw_ptr D u))"
  shows
    "Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val h' (scheduler_event_item_ptr (sd_tcb_ptr D u))) =
     Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val h (scheduler_event_item_ptr (sd_tcb_ptr D u)))"
  using proj
  by (simp add: event_item_raw_ptr_def abi_event_list_item_ptr_def
      scheduler_event_item_ptr_def flip: abi_item_owner_h_val)

lemma one_due_generic_owner_projection_transport:
  assumes proj:
    "List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
       (h_val h' (one_due_generic_raw_ptr D u)) =
     List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
       (h_val h (one_due_generic_raw_ptr D u))"
  shows
    "Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val h' (scheduler_generic_item_ptr (sd_tcb_ptr D u))) =
     Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val h (scheduler_generic_item_ptr (sd_tcb_ptr D u)))"
  using proj
  by (simp add: one_due_generic_raw_ptr_def
      abi_generic_list_item_ptr_def scheduler_generic_item_ptr_def
      flip: abi_item_owner_h_val)

lemma one_due_gateH_generic_notin_event_ringD:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and generic_live: "u \<in> odc_live C"
    and root: "e \<in> odc_event_roots C"
  shows
    "one_due_generic_raw_ptr D u \<notin> set (ring (event_raw e))"
proof
  assume member:
    "one_due_generic_raw_ptr D u \<in> set (ring (event_raw e))"
  have subset:
    "set (ring (event_raw e)) \<subseteq>
       event_item_raw_set (odc_live C) D"
    using one_due_gateH_event_relD[OF rel] root
    by (auto simp: scheduler_event_root_family_rel_def
        event_family_root_rep_def)
  then obtain t where t_live: "t \<in> odc_live C"
    and equal:
      "one_due_generic_raw_ptr D u = event_item_raw_ptr D t"
    using member
    by (auto simp: event_item_raw_set_def event_item_raw_ptr_def)
  have distinct:
    "one_due_generic_raw_ptr D u \<noteq> event_item_raw_ptr D t"
    by (rule one_due_gateH_generic_event_ptr_distinct[
      OF rel generic_live t_live])
  show False using equal distinct by simp
qed

lemma one_due_generic_remove_generic_owner_live:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and live: "u \<in> odc_live C"
  shows
    "Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val
         (one_due_generic_remove_heap D C
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))
         (scheduler_generic_item_ptr (sd_tcb_ptr D u))) =
     Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
         (scheduler_generic_item_ptr (sd_tcb_ptr D u)))"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  let ?source = "odc_delayed_root C"
  let ?p = "one_due_generic_raw_ptr D (odc_task C)"
  let ?q = "one_due_generic_raw_ptr D u"
  have source_root: "?source \<in> odc_generic_roots C"
    by (rule one_due_gateH_source_in_rootsD[OF rel])
  have source_rel: "raw_xlist_rel ?h ?source (generic_raw ?source)"
    by (rule one_due_gateH_raw_xlist_relD[OF rel source_root])
  have p_member: "?p \<in> set (ring (generic_raw ?source))"
    by (rule one_due_gateH_source_memberD[OF rel])
  have bytes:
    "\<forall>a\<in>raw_owner_field_region ?q.
       raw_remove_concrete_heap ?h ?p a = ?h a"
  proof (cases "?q \<in> set (ring (generic_raw ?source))")
    case True
    show ?thesis
      by (rule raw_remove_member_owner_byte_frame[
        OF source_rel p_member True])
  next
    case False
    have q_managed: "?q \<in> universal_managed_nodes (odc_live C) D"
      using live
      by (auto simp: one_due_generic_raw_ptr_def
          universal_managed_nodes_def)
    have item_bytes:
      "\<forall>a\<in>raw_item_region ?q.
         raw_remove_concrete_heap ?h ?p a = ?h a"
      using raw_remove_family_sibling_item_priority_byte_frame[
        OF one_due_gateH_generic_preD[OF rel] source_root p_member
          q_managed False live]
      by blast
    show ?thesis
      using item_bytes raw_owner_field_region_subset_item[where p="?q"]
      by blast
  qed
  show ?thesis
    unfolding one_due_generic_remove_heap_def
    by (rule one_due_generic_owner_projection_transport[
      OF raw_owner_bytes_to_projection[OF bytes]])
qed

lemma one_due_generic_remove_event_owner_live:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and live: "u \<in> odc_live C"
  shows
    "Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val
         (one_due_generic_remove_heap D C
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))
         (scheduler_event_item_ptr (sd_tcb_ptr D u))) =
     Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
         (scheduler_event_item_ptr (sd_tcb_ptr D u)))"
proof -
  have whole:
    "h_val
       (one_due_generic_remove_heap D C
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))
       (event_item_raw_ptr D u) =
     h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (event_item_raw_ptr D u)"
    by (rule one_due_gateH_generic_remove_event_item_frameD[
      OF rel live])
  show ?thesis
    by (rule one_due_event_owner_projection_transport)
       (simp add: whole)
qed

lemma one_due_gateH_event_pre_after_genericD:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
  shows
    "scheduler_family_pre_rel
       (one_due_generic_remove_heap D C
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))
       (odc_event_roots C) event_raw (odc_live C) D"
proof -
  have base:
    "scheduler_family_pre_rel
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (odc_event_roots C) event_raw (odc_live C) D"
    by (rule one_due_gateH_event_preD[OF rel])
  have fam_hg:
    "raw_family_rel
       (one_due_generic_remove_heap D C
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))
       (odc_event_roots C) event_raw"
    using base one_due_gateH_event_root_after_genericD[OF rel]
    by (auto simp: scheduler_family_pre_rel_def raw_family_rel_def)
  show ?thesis
    using base fam_hg
    by (simp add: scheduler_family_pre_rel_def raw_family_rel_def)
qed

lemma one_due_event_remove_event_owner_live:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and live: "u \<in> odc_live C"
  shows
    "Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val
         (one_due_event_remove_heap D C branch
           (one_due_generic_remove_heap D C
             (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))))
         (scheduler_event_item_ptr (sd_tcb_ptr D u))) =
     Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val
         (one_due_generic_remove_heap D C
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))
         (scheduler_event_item_ptr (sd_tcb_ptr D u)))"
proof (cases branch)
  case DueEventNull
  then show ?thesis by (simp add: one_due_event_remove_heap_def)
next
  case (DueEventLinked owner)
  let ?hg = "one_due_generic_remove_heap D C
    (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))"
  let ?pt = "event_item_raw_ptr D (odc_task C)"
  let ?q = "event_item_raw_ptr D u"
  have rel_linked:
    "one_due_gateH_entry_rel D R c a C (DueEventLinked owner) S
       generic_raw event_raw"
    using rel DueEventLinked by simp
  have owner_facts:
    "raw_xlist_rel ?hg owner (event_raw owner) \<and>
     ?pt \<in> set (ring (event_raw owner))"
    by (rule one_due_gateH_linked_event_after_genericD[
        OF rel_linked])
  have owner_root: "owner \<in> odc_event_roots C"
    by (rule one_due_gateH_linked_ownerD[OF rel_linked])
  have bytes:
    "\<forall>a\<in>raw_owner_field_region ?q.
       raw_remove_concrete_heap ?hg ?pt a = ?hg a"
  proof (cases "?q \<in> set (ring (event_raw owner))")
    case True
    show ?thesis
      using owner_facts
      by (intro raw_remove_member_owner_byte_frame[of ?hg owner
          "event_raw owner" ?pt ?q] True) blast+
  next
    case False
    have pre_hg:
      "scheduler_family_pre_rel ?hg (odc_event_roots C) event_raw
         (odc_live C) D"
      by (rule one_due_gateH_event_pre_after_genericD[OF rel])
    have q_managed: "?q \<in> universal_managed_nodes (odc_live C) D"
      using live
      by (auto simp: event_item_raw_ptr_def
          universal_managed_nodes_def)
    have pt_member: "?pt \<in> set (ring (event_raw owner))"
      using owner_facts by blast
    have item_bytes:
      "\<forall>a\<in>raw_item_region ?q.
         raw_remove_concrete_heap ?hg ?pt a = ?hg a"
      using raw_remove_family_sibling_item_priority_byte_frame[
        OF pre_hg owner_root pt_member q_managed False live]
      by blast
    show ?thesis
      using item_bytes
        raw_owner_field_region_subset_item[where p="?q"]
      by blast
  qed
  show ?thesis
    using DueEventLinked
      one_due_event_owner_projection_transport[
        OF raw_owner_bytes_to_projection[OF bytes]]
    by (simp add: one_due_event_remove_heap_def)
qed

lemma one_due_event_remove_generic_owner_live:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and live: "u \<in> odc_live C"
  shows
    "Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val
         (one_due_event_remove_heap D C branch
           (one_due_generic_remove_heap D C
             (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))))
         (scheduler_generic_item_ptr (sd_tcb_ptr D u))) =
     Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val
         (one_due_generic_remove_heap D C
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))
         (scheduler_generic_item_ptr (sd_tcb_ptr D u)))"
proof (cases branch)
  case DueEventNull
  then show ?thesis by (simp add: one_due_event_remove_heap_def)
next
  case (DueEventLinked owner)
  let ?hg = "one_due_generic_remove_heap D C
    (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))"
  let ?pt = "event_item_raw_ptr D (odc_task C)"
  let ?q = "one_due_generic_raw_ptr D u"
  have rel_linked:
    "one_due_gateH_entry_rel D R c a C (DueEventLinked owner) S
       generic_raw event_raw"
    using rel DueEventLinked by simp
  have owner_facts:
    "raw_xlist_rel ?hg owner (event_raw owner) \<and>
     ?pt \<in> set (ring (event_raw owner))"
    by (rule one_due_gateH_linked_event_after_genericD[
        OF rel_linked])
  have owner_root: "owner \<in> odc_event_roots C"
    by (rule one_due_gateH_linked_ownerD[OF rel_linked])
  have pre_hg:
    "scheduler_family_pre_rel ?hg (odc_event_roots C) event_raw
       (odc_live C) D"
    by (rule one_due_gateH_event_pre_after_genericD[OF rel])
  have q_managed: "?q \<in> universal_managed_nodes (odc_live C) D"
    using live
    by (auto simp: one_due_generic_raw_ptr_def
        universal_managed_nodes_def)
  have pt_member: "?pt \<in> set (ring (event_raw owner))"
    using owner_facts by blast
  have nonmember: "?q \<notin> set (ring (event_raw owner))"
    by (rule one_due_gateH_generic_notin_event_ringD[
        OF rel live owner_root])
  have item_bytes:
    "\<forall>a\<in>raw_item_region ?q.
       raw_remove_concrete_heap ?hg ?pt a = ?hg a"
    using raw_remove_family_sibling_item_priority_byte_frame[
      OF pre_hg owner_root pt_member q_managed nonmember live]
    by blast
  have bytes:
    "\<forall>a\<in>raw_owner_field_region ?q.
       raw_remove_concrete_heap ?hg ?pt a = ?hg a"
    using item_bytes
      raw_owner_field_region_subset_item[where p="?q"]
    by blast
  show ?thesis
    using DueEventLinked
      one_due_generic_owner_projection_transport[
        OF raw_owner_bytes_to_projection[OF bytes]]
    by (simp add: one_due_event_remove_heap_def)
qed

lemma one_due_ready_insert_owner_live:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and w_managed: "w \<in> universal_managed_nodes (odc_live C) D"
  shows
    "\<forall>a\<in>raw_owner_field_region w.
       one_due_ready_insert_heap D C generic_raw
         (one_due_event_remove_heap D C branch
           (one_due_generic_remove_heap D C
             (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))) a =
       one_due_event_remove_heap D C branch
         (one_due_generic_remove_heap D C
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))) a"
proof -
  let ?he = "one_due_event_remove_heap D C branch
    (one_due_generic_remove_heap D C
      (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))"
  let ?target = "one_due_target_root C"
  let ?fam = "one_due_generic_raw_after_remove D C generic_raw"
  let ?p = "one_due_generic_raw_ptr D (odc_task C)"
  have task_live: "odc_task C \<in> odc_live C"
    by (rule one_due_gateH_task_liveD[OF rel])
  have target_root: "?target \<in> odc_generic_roots C"
    by (rule one_due_gateH_target_in_rootsD[OF rel])
  note after_pre = one_due_after_event_pre_rel[OF rel]
  note after_event = one_due_gateH_after_event_obligations[OF rel]
  have target_ne: "?target \<noteq> odc_delayed_root C"
    using one_due_gateH_pure_entryD[OF rel]
    by (auto simp: one_due_entry_rel_def one_due_context_wf_def)
  have fam_target: "?fam ?target = generic_raw ?target"
    using target_ne
    by (simp add: one_due_generic_raw_after_remove_def)
  have fresh0:
    "raw_fresh_for_insert ?target (ring (generic_raw ?target)) ?p"
    using after_event
    by (simp add: one_due_after_event_obligations_def Let_def)
  have fresh:
    "raw_fresh_for_insert ?target (ring (?fam ?target)) ?p"
    using fresh0 fam_target by simp
  have p_managed: "?p \<in> universal_managed_nodes (odc_live C) D"
    using task_live
    by (auto simp: one_due_generic_raw_ptr_def
        universal_managed_nodes_def)
  have bytes:
    "\<forall>a\<in>raw_owner_field_region w.
       raw_insert_concrete_heap ?he ?target (?fam ?target) ?p a =
         ?he a"
    by (rule raw_insert_end_family_owner_byte_frame[
      OF after_pre target_root fresh p_managed w_managed])
  show ?thesis
    using bytes
    by (simp add: one_due_ready_insert_heap_def fam_target)
qed

lemma one_due_ready_insert_generic_owner_live:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and live: "u \<in> odc_live C"
  shows
    "Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val
         (one_due_ready_insert_heap D C generic_raw
           (one_due_event_remove_heap D C branch
             (one_due_generic_remove_heap D C
               (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))))
         (scheduler_generic_item_ptr (sd_tcb_ptr D u))) =
     Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val
         (one_due_event_remove_heap D C branch
           (one_due_generic_remove_heap D C
             (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))))
         (scheduler_generic_item_ptr (sd_tcb_ptr D u)))"
proof -
  have q_managed:
    "one_due_generic_raw_ptr D u \<in>
       universal_managed_nodes (odc_live C) D"
    using live
    by (auto simp: one_due_generic_raw_ptr_def
        universal_managed_nodes_def)
  show ?thesis
    by (rule one_due_generic_owner_projection_transport[
      OF raw_owner_bytes_to_projection[
        OF one_due_ready_insert_owner_live[OF rel q_managed]]])
qed

lemma one_due_ready_insert_event_owner_live:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and live: "u \<in> odc_live C"
  shows
    "Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val
         (one_due_ready_insert_heap D C generic_raw
           (one_due_event_remove_heap D C branch
             (one_due_generic_remove_heap D C
               (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))))
         (scheduler_event_item_ptr (sd_tcb_ptr D u))) =
     Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val
         (one_due_event_remove_heap D C branch
           (one_due_generic_remove_heap D C
             (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))))
         (scheduler_event_item_ptr (sd_tcb_ptr D u)))"
proof -
  have q_managed:
    "event_item_raw_ptr D u \<in>
       universal_managed_nodes (odc_live C) D"
    using live
    by (auto simp: event_item_raw_ptr_def
        universal_managed_nodes_def)
  show ?thesis
    by (rule one_due_event_owner_projection_transport[
      OF raw_owner_bytes_to_projection[
        OF one_due_ready_insert_owner_live[OF rel q_managed]]])
qed

lemma one_due_ready_insert_priority_live:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and live: "u \<in> odc_live C"
  shows
    "Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val
         (one_due_ready_insert_heap D C generic_raw
           (one_due_event_remove_heap D C branch
             (one_due_generic_remove_heap D C
               (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))))
         (sd_tcb_ptr D u)) =
     Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val
         (one_due_event_remove_heap D C branch
           (one_due_generic_remove_heap D C
             (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))))
         (sd_tcb_ptr D u))"
proof -
  let ?he = "one_due_event_remove_heap D C branch
    (one_due_generic_remove_heap D C
      (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))"
  let ?target = "one_due_target_root C"
  let ?fam = "one_due_generic_raw_after_remove D C generic_raw"
  let ?p = "one_due_generic_raw_ptr D (odc_task C)"
  let ?sib = "event_item_raw_ptr D (odc_task C)"
  have task_live: "odc_task C \<in> odc_live C"
    by (rule one_due_gateH_task_liveD[OF rel])
  have target_root: "?target \<in> odc_generic_roots C"
    by (rule one_due_gateH_target_in_rootsD[OF rel])
  note after_pre = one_due_after_event_pre_rel[OF rel]
  note after_event = one_due_gateH_after_event_obligations[OF rel]
  have target_ne: "?target \<noteq> odc_delayed_root C"
    using one_due_gateH_pure_entryD[OF rel]
    by (auto simp: one_due_entry_rel_def one_due_context_wf_def)
  have fam_target: "?fam ?target = generic_raw ?target"
    using target_ne
    by (simp add: one_due_generic_raw_after_remove_def)
  have fresh0:
    "raw_fresh_for_insert ?target (ring (generic_raw ?target)) ?p"
    using after_event
    by (simp add: one_due_after_event_obligations_def Let_def)
  have fresh:
    "raw_fresh_for_insert ?target (ring (?fam ?target)) ?p"
    using fresh0 fam_target by simp
  have p_managed: "?p \<in> universal_managed_nodes (odc_live C) D"
    using task_live
    by (auto simp: one_due_generic_raw_ptr_def
        universal_managed_nodes_def)
  have sib_managed:
    "?sib \<in> universal_managed_nodes (odc_live C) D"
    using task_live
    by (auto simp: event_item_raw_ptr_def
        universal_managed_nodes_def)
  have p_sib: "?p \<noteq> ?sib"
    by (rule one_due_gateH_generic_event_ptr_distinct[
      OF rel task_live task_live])
  have sib_nonmember0:
    "?sib \<notin> set (ring (generic_raw ?target))"
    by (rule one_due_gateH_event_notin_generic_rootD[
      OF rel task_live target_root])
  have sib_nonmember:
    "?sib \<notin> set (ring (?fam ?target))"
    using sib_nonmember0 fam_target by simp
  have bytes:
    "\<forall>a\<in>universal_priority_field_region (sd_tcb_ptr D u).
       raw_insert_concrete_heap ?he ?target (?fam ?target) ?p a =
         ?he a"
    using raw_insert_end_family_sibling_owner_priority_byte_frame[
      OF after_pre target_root fresh p_managed sib_managed p_sib
        sib_nonmember live]
    by blast
  have field_same:
    "h_val (one_due_ready_insert_heap D C generic_raw ?he)
       (universal_priority_field_ptr (sd_tcb_ptr D u)) =
     h_val ?he (universal_priority_field_ptr (sd_tcb_ptr D u))"
  proof (rule delay_h_val_region_cong)
    fix address
    assume "address \<in>
      {ptr_val (universal_priority_field_ptr (sd_tcb_ptr D u))..+
         size_of TYPE(32 word)}"
    then show
      "one_due_ready_insert_heap D C generic_raw ?he address =
         ?he address"
      using bytes
      by (simp add: universal_priority_field_region_def
          one_due_ready_insert_heap_def fam_target)
  qed
  show ?thesis
    using field_same
    unfolding universal_priority_field_ptr_def
    by (simp only:
      Scheduler_V611_Parse.tskTaskControlBlock_C_h_val_fields(4)
      one_due_ready_insert_heap_def)
qed

lemma one_due_reentry_priority_chain:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and live: "u \<in> odc_live C"
  shows
    "Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val
         (one_due_ready_insert_heap D C generic_raw
           (one_due_event_remove_heap D C branch
             (one_due_generic_remove_heap D C
               (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))))
         (sd_tcb_ptr D u)) =
     Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
         (sd_tcb_ptr D u))"
  using one_due_ready_insert_priority_live[OF rel live]
    one_due_gateH_priority_after_eventD[OF rel live]
  by simp

lemma one_due_reentry_generic_owner_chain:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and live: "u \<in> odc_live C"
  shows
    "Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val
         (one_due_ready_insert_heap D C generic_raw
           (one_due_event_remove_heap D C branch
             (one_due_generic_remove_heap D C
               (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))))
         (scheduler_generic_item_ptr (sd_tcb_ptr D u))) =
     Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
         (scheduler_generic_item_ptr (sd_tcb_ptr D u)))"
  using one_due_ready_insert_generic_owner_live[OF rel live]
    one_due_event_remove_generic_owner_live[OF rel live]
    one_due_generic_remove_generic_owner_live[OF rel live]
  by simp

lemma one_due_reentry_event_owner_chain:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and live: "u \<in> odc_live C"
  shows
    "Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val
         (one_due_ready_insert_heap D C generic_raw
           (one_due_event_remove_heap D C branch
             (one_due_generic_remove_heap D C
               (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))))
         (scheduler_event_item_ptr (sd_tcb_ptr D u))) =
     Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
         (scheduler_event_item_ptr (sd_tcb_ptr D u)))"
  using one_due_ready_insert_event_owner_live[OF rel live]
    one_due_event_remove_event_owner_live[OF rel live]
    one_due_generic_remove_event_owner_live[OF rel live]
  by simp

theorem one_due_reentry_task_observation:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
  shows
    "TaskObservationRel D
       (one_due_ready_insert_heap D C generic_raw
         (one_due_event_remove_heap D C branch
           (one_due_generic_remove_heap D C
             (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))))
       a"
proof -
  have observation:
    "TaskObservationRel D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) a"
    by (rule one_due_gateH_task_observationD[OF rel])
  have live_eq: "odc_live C = sa_live a"
    by (rule one_due_gateH_live_absD[OF rel])
  have fin: "finite (sa_live a)"
    using observation by (simp add: TaskObservationRel_def)
  have per:
    "\<forall>u\<in>sa_live a.
       c_guard (sd_tcb_ptr D u) \<and>
       c_guard (scheduler_generic_item_ptr (sd_tcb_ptr D u)) \<and>
       c_guard (scheduler_event_item_ptr (sd_tcb_ptr D u)) \<and>
       sa_priority a u < 4 \<and>
       unat (Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
         (h_val
           (one_due_ready_insert_heap D C generic_raw
             (one_due_event_remove_heap D C branch
               (one_due_generic_remove_heap D C
                 (hrs_mem
                   (Scheduler_V611_Parse.globals.t_hrs_' c)))))
           (sd_tcb_ptr D u))) = sa_priority a u \<and>
       Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
         (h_val
           (one_due_ready_insert_heap D C generic_raw
             (one_due_event_remove_heap D C branch
               (one_due_generic_remove_heap D C
                 (hrs_mem
                   (Scheduler_V611_Parse.globals.t_hrs_' c)))))
           (sd_tcb_ptr D u)) < 4 \<and>
       Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
         (h_val
           (one_due_ready_insert_heap D C generic_raw
             (one_due_event_remove_heap D C branch
               (one_due_generic_remove_heap D C
                 (hrs_mem
                   (Scheduler_V611_Parse.globals.t_hrs_' c)))))
           (scheduler_generic_item_ptr (sd_tcb_ptr D u))) =
         PTR_COERCE(Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow>
           unit) (sd_tcb_ptr D u) \<and>
       Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
         (h_val
           (one_due_ready_insert_heap D C generic_raw
             (one_due_event_remove_heap D C branch
               (one_due_generic_remove_heap D C
                 (hrs_mem
                   (Scheduler_V611_Parse.globals.t_hrs_' c)))))
           (scheduler_event_item_ptr (sd_tcb_ptr D u))) =
         PTR_COERCE(Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow>
           unit) (sd_tcb_ptr D u)"
  proof (intro ballI)
    fix u
    assume u_abs: "u \<in> sa_live a"
    have u_live: "u \<in> odc_live C"
      using live_eq u_abs by simp
    note entry = TaskObservationRel_liveD[OF observation u_abs]
    note priority_chain =
      one_due_reentry_priority_chain[OF rel u_live]
    note generic_owner_chain =
      one_due_reentry_generic_owner_chain[OF rel u_live]
    note event_owner_chain =
      one_due_reentry_event_owner_chain[OF rel u_live]
    show
      "c_guard (sd_tcb_ptr D u) \<and>
       c_guard (scheduler_generic_item_ptr (sd_tcb_ptr D u)) \<and>
       c_guard (scheduler_event_item_ptr (sd_tcb_ptr D u)) \<and>
       sa_priority a u < 4 \<and>
       unat (Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
         (h_val
           (one_due_ready_insert_heap D C generic_raw
             (one_due_event_remove_heap D C branch
               (one_due_generic_remove_heap D C
                 (hrs_mem
                   (Scheduler_V611_Parse.globals.t_hrs_' c)))))
           (sd_tcb_ptr D u))) = sa_priority a u \<and>
       Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
         (h_val
           (one_due_ready_insert_heap D C generic_raw
             (one_due_event_remove_heap D C branch
               (one_due_generic_remove_heap D C
                 (hrs_mem
                   (Scheduler_V611_Parse.globals.t_hrs_' c)))))
           (sd_tcb_ptr D u)) < 4 \<and>
       Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
         (h_val
           (one_due_ready_insert_heap D C generic_raw
             (one_due_event_remove_heap D C branch
               (one_due_generic_remove_heap D C
                 (hrs_mem
                   (Scheduler_V611_Parse.globals.t_hrs_' c)))))
           (scheduler_generic_item_ptr (sd_tcb_ptr D u))) =
         PTR_COERCE(Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow>
           unit) (sd_tcb_ptr D u) \<and>
       Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
         (h_val
           (one_due_ready_insert_heap D C generic_raw
             (one_due_event_remove_heap D C branch
               (one_due_generic_remove_heap D C
                 (hrs_mem
                   (Scheduler_V611_Parse.globals.t_hrs_' c)))))
           (scheduler_event_item_ptr (sd_tcb_ptr D u))) =
         PTR_COERCE(Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow>
           unit) (sd_tcb_ptr D u)"
      using entry priority_chain generic_owner_chain
        event_owner_chain
      by simp
  qed
  show ?thesis
    unfolding TaskObservationRel_def
    using fin per by blast
qed

text \<open>
  The event families at the insert heap.  Every event root's ring
  relation is carried through both removals and the insertion: the
  linked owner loses exactly the due task's Event item, every other
  event ring is untouched, and the insertion's exact footprint lies in
  the generic side by storage separation.
\<close>

lemma one_due_ready_insert_event_storage_frame:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and root: "e \<in> odc_event_roots C"
    and address:
      "address \<in> raw_xlist_storage e (event_raw e)"
  shows
    "one_due_ready_insert_heap D C generic_raw
       (one_due_event_remove_heap D C branch
         (one_due_generic_remove_heap D C
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))))
       address =
     one_due_event_remove_heap D C branch
       (one_due_generic_remove_heap D C
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))
       address"
proof -
  let ?he = "one_due_event_remove_heap D C branch
    (one_due_generic_remove_heap D C
      (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))"
  let ?target = "one_due_target_root C"
  let ?fam = "one_due_generic_raw_after_remove D C generic_raw"
  let ?p = "one_due_generic_raw_ptr D (odc_task C)"
  let ?source = "odc_delayed_root C"
  have source_root: "?source \<in> odc_generic_roots C"
    by (rule one_due_gateH_source_in_rootsD[OF rel])
  have target_root: "?target \<in> odc_generic_roots C"
    by (rule one_due_gateH_target_in_rootsD[OF rel])
  have target_ne: "?target \<noteq> ?source"
    using one_due_gateH_pure_entryD[OF rel]
    by (auto simp: one_due_entry_rel_def one_due_context_wf_def)
  have fam_target: "?fam ?target = generic_raw ?target"
    using target_ne
    by (simp add: one_due_generic_raw_after_remove_def)
  note after_event = one_due_gateH_after_event_obligations[OF rel]
  have ring_rel: "raw_xlist_rel ?he ?target (generic_raw ?target)"
    using after_event
    by (simp add: one_due_after_event_obligations_def Let_def)
  have fresh0:
    "raw_fresh_for_insert ?target (ring (generic_raw ?target)) ?p"
    using after_event
    by (simp add: one_due_after_event_obligations_def Let_def)
  have footprint:
    "raw_insert_end_exact_write_footprint ?he ?target
       (generic_raw ?target) ?p \<subseteq>
     raw_xlist_storage ?target (generic_raw ?target) \<union>
       raw_item_region ?p"
    by (rule raw_insert_end_exact_footprint_subset_storage[
      OF ring_rel])
  have cross_target:
    "raw_xlist_storage ?target (generic_raw ?target) \<inter>
       raw_xlist_storage e (event_raw e) = {}"
    by (rule one_due_gateH_storage_disjointD[OF rel target_root
      root])
  have p_member: "?p \<in> set (ring (generic_raw ?source))"
    by (rule one_due_gateH_source_memberD[OF rel])
  have p_in_source_storage:
    "raw_item_region ?p \<subseteq>
       raw_xlist_storage ?source (generic_raw ?source)"
    using p_member by (auto simp: raw_xlist_storage_def)
  have cross_source:
    "raw_xlist_storage ?source (generic_raw ?source) \<inter>
       raw_xlist_storage e (event_raw e) = {}"
    by (rule one_due_gateH_storage_disjointD[OF rel source_root
      root])
  have outside:
    "address \<notin> raw_insert_end_exact_write_footprint ?he ?target
       (generic_raw ?target) ?p"
    using footprint cross_target p_in_source_storage cross_source
      address by blast
  have byte:
    "raw_insert_concrete_heap ?he ?target (generic_raw ?target) ?p
       address = ?he address"
    by (rule raw_insert_concrete_heap_exact_external_frame[
      OF ring_rel fresh0 outside])
  show ?thesis
    using byte
    by (simp add: one_due_ready_insert_heap_def)
qed

lemma one_due_event_remove_event_root_raw_rel:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and root: "e \<in> odc_event_roots C"
  shows
    "raw_xlist_rel
       (one_due_event_remove_heap D C branch
         (one_due_generic_remove_heap D C
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))))
       e (one_due_event_raw_after_remove D C branch event_raw e)"
proof -
  let ?hg = "one_due_generic_remove_heap D C
    (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))"
  let ?qt = "event_item_raw_ptr D (odc_task C)"
  note after_event = one_due_gateH_after_event_obligations[OF rel]
  show ?thesis
  proof (cases branch)
    case DueEventNull
    then show ?thesis
      using after_event root
      by (simp add: one_due_after_event_obligations_def Let_def
          one_due_event_raw_after_remove_def)
  next
    case (DueEventLinked owner)
    have rel_linked:
      "one_due_gateH_entry_rel D R c a C (DueEventLinked owner) S
         generic_raw event_raw"
      using rel DueEventLinked by simp
    have owner_root: "owner \<in> odc_event_roots C"
      by (rule one_due_gateH_linked_ownerD[OF rel_linked])
    show ?thesis
    proof (cases "e = owner")
      case True
      have owner_rel:
        "raw_xlist_rel
           (one_due_event_remove_heap D C (DueEventLinked owner) ?hg)
           owner (list_remove_abs ?qt (event_raw owner))"
        using after_event DueEventLinked
        by (simp add: one_due_after_event_obligations_def Let_def)
      then show ?thesis
        using True DueEventLinked
        by (simp add: one_due_event_raw_after_remove_def)
    next
      case False
      have hg_rel: "raw_xlist_rel ?hg e (event_raw e)"
        by (rule one_due_gateH_event_root_after_genericD[OF rel
          root])
      have pre_hg:
        "scheduler_family_pre_rel ?hg (odc_event_roots C) event_raw
           (odc_live C) D"
        by (rule one_due_gateH_event_pre_after_genericD[OF rel])
      have owner_facts:
        "raw_xlist_rel ?hg owner (event_raw owner) \<and>
         ?qt \<in> set (ring (event_raw owner))"
        by (rule one_due_gateH_linked_event_after_genericD[
            OF rel_linked])
      have footprint:
        "raw_remove_exact_write_footprint ?hg owner ?qt \<subseteq>
           raw_xlist_storage owner (event_raw owner)"
        using owner_facts
        by (intro raw_remove_exact_footprint_subset_storage) blast+
      have disj:
        "raw_xlist_storage e (event_raw e) \<inter>
           raw_xlist_storage owner (event_raw owner) = {}"
        by (rule scheduler_family_pre_rel_storage_disjoint[
          OF pre_hg root owner_root False])
      have frame:
        "\<And>a. a \<in> raw_xlist_storage e (event_raw e) \<Longrightarrow>
           one_due_event_remove_heap D C (DueEventLinked owner)
             ?hg a = ?hg a"
      proof -
        fix a
        assume a_in: "a \<in> raw_xlist_storage e (event_raw e)"
        have outside:
          "a \<notin> raw_remove_exact_write_footprint ?hg owner ?qt"
          using footprint disj a_in by blast
        show "one_due_event_remove_heap D C (DueEventLinked owner)
            ?hg a = ?hg a"
          using owner_facts
          by (auto simp: one_due_event_remove_heap_def
              intro: raw_remove_concrete_heap_exact_external_frame[
                OF _ _ outside])
      qed
      have he_rel:
        "raw_xlist_rel
           (one_due_event_remove_heap D C (DueEventLinked owner)
             ?hg) e (event_raw e)"
        by (rule delay_raw_xlist_rel_storage_frame[OF hg_rel frame])
      then show ?thesis
        using False DueEventLinked
        by (simp add: one_due_event_raw_after_remove_def)
    qed
  qed
qed

lemma one_due_reentry_event_root_raw_rel:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and root: "e \<in> odc_event_roots C"
  shows
    "raw_xlist_rel
       (one_due_ready_insert_heap D C generic_raw
         (one_due_event_remove_heap D C branch
           (one_due_generic_remove_heap D C
             (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))))
       e (one_due_event_raw_after_remove D C branch event_raw e)"
proof -
  have he_rel:
    "raw_xlist_rel
       (one_due_event_remove_heap D C branch
         (one_due_generic_remove_heap D C
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))))
       e (one_due_event_raw_after_remove D C branch event_raw e)"
    by (rule one_due_event_remove_event_root_raw_rel[OF rel root])
  have storage_sub:
    "raw_xlist_storage e
       (one_due_event_raw_after_remove D C branch event_raw e) \<subseteq>
     raw_xlist_storage e (event_raw e)"
    by (cases branch)
      (auto simp: one_due_event_raw_after_remove_def
        intro: raw_xlist_storage_remove_subset[THEN subsetD])
  have frame:
    "\<And>a. a \<in> raw_xlist_storage e
        (one_due_event_raw_after_remove D C branch event_raw e) \<Longrightarrow>
       one_due_ready_insert_heap D C generic_raw
         (one_due_event_remove_heap D C branch
           (one_due_generic_remove_heap D C
             (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))))
         a =
       one_due_event_remove_heap D C branch
         (one_due_generic_remove_heap D C
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))) a"
    using storage_sub
    by (intro one_due_ready_insert_event_storage_frame[OF rel root])
      blast
  show ?thesis
    by (rule delay_raw_xlist_rel_storage_frame[OF he_rel frame])
qed

text \<open>
  Per-root event representation at the re-entry family: the ring
  subset, the relabel to the re-entry snapshot family, and the
  abstract well-formedness and kind clauses.
\<close>

lemma one_due_gateH_event_root_repD:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and root: "e \<in> odc_event_roots C"
  shows
    "event_family_root_rep D event_raw (ods_event_family S)
       (odc_live C) e"
  using one_due_gateH_event_relD[OF rel] root
  unfolding scheduler_event_root_family_rel_def
  by blast

lemma one_due_event_raw_set_decode:
  assumes laws: "universal_decoder_laws live D"
    and mem: "u \<in> event_item_raw_set live D"
  shows "\<exists>t\<in>live. u = event_item_raw_ptr D t \<and>
     sd_node_decode D u = Some (Event t)"
  using laws mem
  by (auto simp: event_item_raw_set_def event_item_raw_ptr_def
      universal_decoder_laws_def)

lemma one_due_event_decode_inj:
  assumes laws: "universal_decoder_laws live D"
    and u: "sd_node_decode D u = Some (Event t)"
    and u': "sd_node_decode D u' = Some (Event t)"
  shows "u = u'"
proof -
  have ev_law:
    "\<forall>p t. sd_node_decode D p = Some (Event t) \<longrightarrow>
       t \<in> live \<and>
       p = abi_event_list_item_ptr (sd_tcb_ptr D t)"
    using laws by (simp add: universal_decoder_laws_def)
  have "u = abi_event_list_item_ptr (sd_tcb_ptr D t)"
    using ev_law u by blast
  moreover have
    "u' = abi_event_list_item_ptr (sd_tcb_ptr D t)"
    using ev_law u' by blast
  ultimately show ?thesis by simp
qed

lemma one_due_gateH_task_event_ptr_decode:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
  shows
    "sd_node_decode D (event_item_raw_ptr D (odc_task C)) =
       Some (Event (odc_task C))"
proof -
  have laws: "universal_decoder_laws (odc_live C) D"
    by (rule one_due_gateH_decoder_lawsD[OF rel])
  have task_live: "odc_task C \<in> odc_live C"
    by (rule one_due_gateH_task_liveD[OF rel])
  have bullets:
    "\<forall>t\<in>odc_live C.
       sd_tcb_decode D (sd_tcb_ptr D t) = Some t \<and>
       sd_node_decode D
         (abi_generic_list_item_ptr (sd_tcb_ptr D t)) =
         Some (Generic t) \<and>
       sd_node_decode D
         (abi_event_list_item_ptr (sd_tcb_ptr D t)) =
         Some (Event t)"
    using laws by (simp add: universal_decoder_laws_def)
  show ?thesis
    using bspec[OF bullets task_live]
    by (simp add: event_item_raw_ptr_def)
qed

lemma one_due_gateH_event_ring_decode_inj:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and root: "e \<in> odc_event_roots C"
    and u_in: "u \<in> insert (event_item_raw_ptr D (odc_task C))
      (set (ring (event_raw e)))"
    and u'_in: "u' \<in> insert (event_item_raw_ptr D (odc_task C))
      (set (ring (event_raw e)))"
    and eq: "sd_node_decode D u = sd_node_decode D u'"
  shows "u = u'"
proof -
  have laws: "universal_decoder_laws (odc_live C) D"
    by (rule one_due_gateH_decoder_lawsD[OF rel])
  have task_live: "odc_task C \<in> odc_live C"
    by (rule one_due_gateH_task_liveD[OF rel])
  have qt_set:
    "event_item_raw_ptr D (odc_task C) \<in>
       event_item_raw_set (odc_live C) D"
    using task_live by (auto simp: event_item_raw_set_def)
  have ring_sub:
    "set (ring (event_raw e)) \<subseteq>
       event_item_raw_set (odc_live C) D"
    using one_due_gateH_event_root_repD[OF rel root]
    by (simp add: event_family_root_rep_def)
  have u_set: "u \<in> event_item_raw_set (odc_live C) D"
    using u_in qt_set ring_sub by blast
  have u'_set: "u' \<in> event_item_raw_set (odc_live C) D"
    using u'_in qt_set ring_sub by blast
  obtain t where du: "sd_node_decode D u = Some (Event t)"
    using one_due_event_raw_set_decode[OF laws u_set] by blast
  have du': "sd_node_decode D u' = Some (Event t)"
    using eq du by simp
  show ?thesis
    by (rule one_due_event_decode_inj[OF laws du du'])
qed

theorem one_due_reentry_event_root_rep:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and root: "e \<in> odc_event_roots C"
  shows
    "event_family_root_rep D
       (one_due_event_raw_after_remove D C branch event_raw)
       (ods_event_family (one_due_reentry_snapshot C branch S))
       (odc_live C) e"
proof -
  note base = one_due_gateH_event_root_repD[OF rel root]
  have shape': "one_due_family_shape
     (one_due_reentry_context C (odc_task C))
     (one_due_reentry_snapshot C branch S)"
    by (rule one_due_reentry_family_shape[
      OF one_due_gateH_pure_entryD[OF rel]])
  have abs_wf:
    "xlist_wf (ods_event_family
       (one_due_reentry_snapshot C branch S) e)"
    using shape' root
    by (auto simp: one_due_family_shape_def
        one_due_reentry_context_components)
  have abs_kind:
    "event_ring (ods_event_family
       (one_due_reentry_snapshot C branch S) e)"
    using shape' root
    by (auto simp: one_due_family_shape_def
        one_due_reentry_context_components)
  show ?thesis
  proof (cases branch)
    case DueEventNull
    then show ?thesis
      using base abs_wf abs_kind
      by (simp add: event_family_root_rep_def
          one_due_event_raw_after_remove_def
          one_due_reentry_snapshot_event_at)
  next
    case (DueEventLinked owner)
    show ?thesis
    proof (cases "e = owner")
      case True
      have rel_linked:
        "one_due_gateH_entry_rel D R c a C (DueEventLinked owner) S
           generic_raw event_raw"
        using rel DueEventLinked by simp
      have owner_root: "owner \<in> odc_event_roots C"
        by (rule one_due_gateH_linked_ownerD[OF rel_linked])
      have base_sub:
        "set (ring (event_raw e)) \<subseteq>
           event_item_raw_set (odc_live C) D"
        using base by (simp add: event_family_root_rep_def)
      have sub':
        "set (ring (list_remove_abs
           (event_item_raw_ptr D (odc_task C)) (event_raw e))) \<subseteq>
         event_item_raw_set (odc_live C) D"
        using base_sub
        by (auto dest!: subsetD[OF list_remove_abs_ring_subset])
      have base_relabel:
        "xlist_relabel (sd_node_decode D) (event_raw e)
           (ods_event_family S e)"
        using base by (simp add: event_family_root_rep_def)
      have wf_raw: "xlist_wf (event_raw e)"
        by (rule raw_xlist_rel_wf[OF
            scheduler_event_root_family_raw_rootD[OF
              one_due_gateH_event_relD[OF rel] root]])
      have pn:
        "sd_node_decode D (event_item_raw_ptr D (odc_task C)) =
           Some (Event (odc_task C))"
        by (rule one_due_gateH_task_event_ptr_decode[OF rel])
      have relabel':
        "xlist_relabel (sd_node_decode D)
           (list_remove_abs (event_item_raw_ptr D (odc_task C))
             (event_raw e))
           (list_remove_abs (Event (odc_task C))
             (ods_event_family S e))"
        by (rule xlist_relabel_remove[OF base_relabel wf_raw pn
            one_due_gateH_event_ring_decode_inj[OF rel root]])
      show ?thesis
        using sub' relabel' abs_wf abs_kind True DueEventLinked
        by (simp add: event_family_root_rep_def
            one_due_event_raw_after_remove_def
            one_due_reentry_snapshot_event_at)
    next
      case False
      then show ?thesis
        using base abs_wf abs_kind DueEventLinked
        by (simp add: event_family_root_rep_def
            one_due_event_raw_after_remove_def
            one_due_reentry_snapshot_event_at)
    qed
  qed
qed

text \<open>
  The event key representation at the insert heap: every live task's
  Event key byte survives all three writes, and the abstract per-ring
  keys transport through the snapshot equations.
\<close>

lemma one_due_gateH_event_keysD:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and live: "t \<in> odc_live C"
  shows
    "raw_key_at (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (event_item_raw_ptr D t) = odc_K_E C t"
  using one_due_gateH_event_relD[OF rel] live
  unfolding scheduler_event_root_family_rel_def
    event_family_key_rep_def
  by blast

lemma one_due_event_remove_key_at_live:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and live: "u \<in> odc_live C"
  shows
    "raw_key_at
       (one_due_event_remove_heap D C branch
         (one_due_generic_remove_heap D C
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))))
       (event_item_raw_ptr D u) =
     raw_key_at
       (one_due_generic_remove_heap D C
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))
       (event_item_raw_ptr D u)"
proof (cases branch)
  case DueEventNull
  then show ?thesis by (simp add: one_due_event_remove_heap_def)
next
  case (DueEventLinked owner)
  let ?hg = "one_due_generic_remove_heap D C
    (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))"
  let ?qt = "event_item_raw_ptr D (odc_task C)"
  let ?q = "event_item_raw_ptr D u"
  have rel_linked:
    "one_due_gateH_entry_rel D R c a C (DueEventLinked owner) S
       generic_raw event_raw"
    using rel DueEventLinked by simp
  have owner_facts:
    "raw_xlist_rel ?hg owner (event_raw owner) \<and>
     ?qt \<in> set (ring (event_raw owner))"
    by (rule one_due_gateH_linked_event_after_genericD[
        OF rel_linked])
  have owner_root: "owner \<in> odc_event_roots C"
    by (rule one_due_gateH_linked_ownerD[OF rel_linked])
  have owner_rel: "raw_xlist_rel ?hg owner (event_raw owner)"
    and qt_member: "?qt \<in> set (ring (event_raw owner))"
    using owner_facts by blast+
  have key_eq:
    "raw_key_at (raw_remove_concrete_heap ?hg ?qt) ?q =
       raw_key_at ?hg ?q"
  proof (cases "?q = ?qt")
    case True
    then show ?thesis
      using raw_remove_concrete_heap_key_at_removed[
        OF owner_rel qt_member]
      by simp
  next
    case False
    show ?thesis
    proof (cases "?q \<in> set (ring (event_raw owner))")
      case True
      have q_survivor:
        "?q \<in> set (remove1 ?qt (ring (event_raw owner)))"
        using True False
        by (simp add: in_set_remove1)
      show ?thesis
        using raw_remove_concrete_heap_payload_effect[
          OF owner_rel qt_member] q_survivor
        by blast
    next
      case False'': False
      have pre_hg:
        "scheduler_family_pre_rel ?hg (odc_event_roots C)
           event_raw (odc_live C) D"
        by (rule one_due_gateH_event_pre_after_genericD[OF rel])
      have q_managed:
        "?q \<in> universal_managed_nodes (odc_live C) D"
        using live
        by (auto simp: event_item_raw_ptr_def
            universal_managed_nodes_def)
      have item_bytes:
        "\<forall>a\<in>raw_item_region ?q.
           raw_remove_concrete_heap ?hg ?qt a = ?hg a"
        using raw_remove_family_sibling_item_priority_byte_frame[
          OF pre_hg owner_root qt_member q_managed False'' live]
        by blast
      have item_same:
        "h_val (raw_remove_concrete_heap ?hg ?qt) ?q =
           h_val ?hg ?q"
      proof (rule delay_h_val_region_cong)
        fix a
        assume "a \<in> {ptr_val ?q..+size_of TYPE(xLIST_ITEM_C)}"
        then show
          "raw_remove_concrete_heap ?hg ?qt a = ?hg a"
          using item_bytes by (simp add: raw_item_region_def)
      qed
      then show ?thesis by (simp add: raw_key_at_def)
    qed
  qed
  show ?thesis
    using key_eq DueEventLinked
    by (simp add: one_due_event_remove_heap_def)
qed

lemma one_due_ready_insert_key_at_live:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and w_managed: "w \<in> universal_managed_nodes (odc_live C) D"
  shows
    "raw_key_at
       (one_due_ready_insert_heap D C generic_raw
         (one_due_event_remove_heap D C branch
           (one_due_generic_remove_heap D C
             (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))))
       w =
     raw_key_at
       (one_due_event_remove_heap D C branch
         (one_due_generic_remove_heap D C
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))))
       w"
proof -
  let ?he = "one_due_event_remove_heap D C branch
    (one_due_generic_remove_heap D C
      (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))"
  let ?target = "one_due_target_root C"
  let ?fam = "one_due_generic_raw_after_remove D C generic_raw"
  let ?p = "one_due_generic_raw_ptr D (odc_task C)"
  have task_live: "odc_task C \<in> odc_live C"
    by (rule one_due_gateH_task_liveD[OF rel])
  have target_root: "?target \<in> odc_generic_roots C"
    by (rule one_due_gateH_target_in_rootsD[OF rel])
  note after_pre = one_due_after_event_pre_rel[OF rel]
  note after_event = one_due_gateH_after_event_obligations[OF rel]
  have target_ne: "?target \<noteq> odc_delayed_root C"
    using one_due_gateH_pure_entryD[OF rel]
    by (auto simp: one_due_entry_rel_def one_due_context_wf_def)
  have fam_target: "?fam ?target = generic_raw ?target"
    using target_ne
    by (simp add: one_due_generic_raw_after_remove_def)
  have fresh0:
    "raw_fresh_for_insert ?target (ring (generic_raw ?target)) ?p"
    using after_event
    by (simp add: one_due_after_event_obligations_def Let_def)
  have fresh:
    "raw_fresh_for_insert ?target (ring (?fam ?target)) ?p"
    using fresh0 fam_target by simp
  have p_managed: "?p \<in> universal_managed_nodes (odc_live C) D"
    using task_live
    by (auto simp: one_due_generic_raw_ptr_def
        universal_managed_nodes_def)
  have bytes:
    "\<forall>a\<in>raw_key_field_region w.
       raw_insert_concrete_heap ?he ?target (?fam ?target) ?p a =
         ?he a"
    by (rule raw_insert_end_family_key_byte_frame[
      OF after_pre target_root fresh p_managed w_managed])
  have proj:
    "raw_key_at
       (raw_insert_concrete_heap ?he ?target (?fam ?target) ?p) w =
     raw_key_at ?he w"
    by (rule raw_key_bytes_to_projection[OF bytes])
  show ?thesis
    using proj
    by (simp add: one_due_ready_insert_heap_def fam_target)
qed

lemma one_due_reentry_event_key_raw:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and live: "u \<in> odc_live C"
  shows
    "raw_key_at
       (one_due_ready_insert_heap D C generic_raw
         (one_due_event_remove_heap D C branch
           (one_due_generic_remove_heap D C
             (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))))
       (event_item_raw_ptr D u) = odc_K_E C u"
proof -
  have key_h:
    "raw_key_at (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (event_item_raw_ptr D u) = odc_K_E C u"
    by (rule one_due_gateH_event_keysD[OF rel live])
  have key_hg:
    "raw_key_at
       (one_due_generic_remove_heap D C
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))
       (event_item_raw_ptr D u) =
     raw_key_at (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (event_item_raw_ptr D u)"
    using one_due_gateH_generic_remove_event_item_frameD[
      OF rel live]
    by (simp add: raw_key_at_def)
  have key_he:
    "raw_key_at
       (one_due_event_remove_heap D C branch
         (one_due_generic_remove_heap D C
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))))
       (event_item_raw_ptr D u) =
     raw_key_at
       (one_due_generic_remove_heap D C
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))
       (event_item_raw_ptr D u)"
    by (rule one_due_event_remove_key_at_live[OF rel live])
  have q_managed:
    "event_item_raw_ptr D u \<in>
       universal_managed_nodes (odc_live C) D"
    using live
    by (auto simp: event_item_raw_ptr_def
        universal_managed_nodes_def)
  have key_hi:
    "raw_key_at
       (one_due_ready_insert_heap D C generic_raw
         (one_due_event_remove_heap D C branch
           (one_due_generic_remove_heap D C
             (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))))
       (event_item_raw_ptr D u) =
     raw_key_at
       (one_due_event_remove_heap D C branch
         (one_due_generic_remove_heap D C
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))))
       (event_item_raw_ptr D u)"
    by (rule one_due_ready_insert_key_at_live[OF rel q_managed])
  show ?thesis using key_h key_hg key_he key_hi by simp
qed

theorem one_due_reentry_event_key_rep:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
  shows
    "event_family_key_rep D
       (one_due_ready_insert_heap D C generic_raw
         (one_due_event_remove_heap D C branch
           (one_due_generic_remove_heap D C
             (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))))
       (odc_event_roots C)
       (one_due_event_raw_after_remove D C branch event_raw)
       (ods_event_family (one_due_reentry_snapshot C branch S))
       (odc_live C) (odc_K_E C)"
proof -
  have raw_keys:
    "\<forall>t\<in>odc_live C.
       raw_key_at
         (one_due_ready_insert_heap D C generic_raw
           (one_due_event_remove_heap D C branch
             (one_due_generic_remove_heap D C
               (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))))
         (event_item_raw_ptr D t) = odc_K_E C t"
    using one_due_reentry_event_key_raw[OF rel] by blast
  have base_abs:
    "\<forall>lp\<in>odc_event_roots C. \<forall>t\<in>odc_live C.
       Event t \<in> set (ring (ods_event_family S lp)) \<longrightarrow>
       item_key (ods_event_family S lp) (Event t) = odc_K_E C t"
    using one_due_gateH_event_relD[OF rel]
    unfolding scheduler_event_root_family_rel_def
      event_family_key_rep_def
    by blast
  have abs_keys:
    "\<forall>lp\<in>odc_event_roots C. \<forall>t\<in>odc_live C.
       Event t \<in> set (ring (ods_event_family
         (one_due_reentry_snapshot C branch S) lp)) \<longrightarrow>
       item_key (ods_event_family
         (one_due_reentry_snapshot C branch S) lp) (Event t) =
         odc_K_E C t"
  proof (intro ballI impI)
    fix lp t
    assume lp_root: "lp \<in> odc_event_roots C"
      and t_live: "t \<in> odc_live C"
      and t_in: "Event t \<in> set (ring (ods_event_family
        (one_due_reentry_snapshot C branch S) lp))"
    show "item_key (ods_event_family
       (one_due_reentry_snapshot C branch S) lp) (Event t) =
       odc_K_E C t"
    proof (cases branch)
      case DueEventNull
      then show ?thesis
        using base_abs lp_root t_live t_in
        by (simp add: one_due_reentry_snapshot_event_at)
    next
      case (DueEventLinked owner)
      show ?thesis
      proof (cases "lp = owner")
        case True
        have t_in_old:
          "Event t \<in> set (ring (ods_event_family S lp))"
          using t_in True DueEventLinked
          by (auto simp: one_due_reentry_snapshot_event_at
              dest!: subsetD[OF list_remove_abs_ring_subset])
        then show ?thesis
          using base_abs lp_root t_live True DueEventLinked
          by (simp add: one_due_reentry_snapshot_event_at
              list_remove_abs_item_key)
      next
        case False
        then show ?thesis
          using base_abs lp_root t_live t_in DueEventLinked
          by (simp add: one_due_reentry_snapshot_event_at)
      qed
    qed
  qed
  show ?thesis
    using raw_keys abs_keys
    by (simp add: event_family_key_rep_def)
qed

text \<open>
  The packaged event pre-relation and the family relation at the
  insert heap.  The container representation stays an explicit premise
  here; its per-item transport is the next rung.
\<close>

lemma one_due_reentry_event_pre_rel:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
  shows
    "scheduler_family_pre_rel
       (one_due_ready_insert_heap D C generic_raw
         (one_due_event_remove_heap D C branch
           (one_due_generic_remove_heap D C
             (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))))
       (odc_event_roots C)
       (one_due_event_raw_after_remove D C branch event_raw)
       (odc_live C) D"
proof -
  have base:
    "scheduler_family_pre_rel
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (odc_event_roots C) event_raw (odc_live C) D"
    by (rule one_due_gateH_event_preD[OF rel])
  have ring_sub:
    "\<And>e. set (ring (one_due_event_raw_after_remove D C branch
       event_raw e)) \<subseteq> set (ring (event_raw e))"
    by (cases branch)
      (auto simp: one_due_event_raw_after_remove_def
        dest!: subsetD[OF list_remove_abs_ring_subset])
  have fam_hi:
    "raw_family_rel
       (one_due_ready_insert_heap D C generic_raw
         (one_due_event_remove_heap D C branch
           (one_due_generic_remove_heap D C
             (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))))
       (odc_event_roots C)
       (one_due_event_raw_after_remove D C branch event_raw)"
    using base one_due_reentry_event_root_raw_rel[OF rel]
    by (auto simp: scheduler_family_pre_rel_def raw_family_rel_def)
  have managed_sub:
    "\<forall>lp\<in>odc_event_roots C.
       set (ring (one_due_event_raw_after_remove D C branch
         event_raw lp)) \<subseteq>
       universal_managed_nodes (odc_live C) D"
  proof
    fix lp
    assume lp_root: "lp \<in> odc_event_roots C"
    have base_sub:
      "set (ring (event_raw lp)) \<subseteq>
         universal_managed_nodes (odc_live C) D"
      using base lp_root
      by (auto simp: scheduler_family_pre_rel_def)
    show "set (ring (one_due_event_raw_after_remove D C branch
        event_raw lp)) \<subseteq>
        universal_managed_nodes (odc_live C) D"
      using ring_sub[of lp] base_sub by blast
  qed
  have ring_pairwise:
    "\<forall>lp\<in>odc_event_roots C. \<forall>lq\<in>odc_event_roots C.
       lp \<noteq> lq \<longrightarrow>
       set (ring (one_due_event_raw_after_remove D C branch
         event_raw lp)) \<inter>
       set (ring (one_due_event_raw_after_remove D C branch
         event_raw lq)) = {}"
  proof (intro ballI impI)
    fix lp lq
    assume lp_root: "lp \<in> odc_event_roots C"
      and lq_root: "lq \<in> odc_event_roots C"
      and ne: "lp \<noteq> lq"
    have base_disj:
      "set (ring (event_raw lp)) \<inter>
         set (ring (event_raw lq)) = {}"
      using base lp_root lq_root ne
      by (auto simp: scheduler_family_pre_rel_def)
    show "set (ring (one_due_event_raw_after_remove D C branch
        event_raw lp)) \<inter>
        set (ring (one_due_event_raw_after_remove D C branch
          event_raw lq)) = {}"
      using ring_sub[of lp] ring_sub[of lq] base_disj by blast
  qed
  show ?thesis
    using base fam_hi managed_sub ring_pairwise
    by (simp add: scheduler_family_pre_rel_def)
qed

theorem one_due_reentry_event_family_rel:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and container:
      "event_family_container_rep D
         (one_due_ready_insert_heap D C generic_raw
           (one_due_event_remove_heap D C branch
             (one_due_generic_remove_heap D C
               (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))))
         (odc_event_roots C)
         (one_due_event_raw_after_remove D C branch event_raw)
         (odc_live C)"
  shows
    "scheduler_event_root_family_rel D
       (one_due_ready_insert_heap D C generic_raw
         (one_due_event_remove_heap D C branch
           (one_due_generic_remove_heap D C
             (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))))
       (odc_event_roots C) (odc_pending_root C)
       (one_due_event_raw_after_remove D C branch event_raw)
       (ods_event_family (one_due_reentry_snapshot C branch S))
       (odc_live C) (odc_K_E C)"
proof -
  have laws: "universal_decoder_laws (odc_live C) D"
    by (rule one_due_gateH_decoder_lawsD[OF rel])
  have pending:
    "odc_pending_root C \<in> odc_event_roots C"
    using one_due_gateH_event_relD[OF rel]
    unfolding scheduler_event_root_family_rel_def
    by blast
  have reps:
    "\<forall>lp\<in>odc_event_roots C.
       event_family_root_rep D
         (one_due_event_raw_after_remove D C branch event_raw)
         (ods_event_family (one_due_reentry_snapshot C branch S))
         (odc_live C) lp"
    using one_due_reentry_event_root_rep[OF rel] by blast
  show ?thesis
    using one_due_reentry_event_pre_rel[OF rel] laws pending reps
      container one_due_reentry_event_key_rep[OF rel]
    by (simp add: scheduler_event_root_family_rel_def)
qed

end
