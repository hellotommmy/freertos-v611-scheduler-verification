theory Scheduler_Ordered_Insert_General_Loop
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Ordered_Insert_General_Source.Scheduler_Ordered_Insert_General_Source"
begin

text \<open>
  Actual generated-while discharge for arbitrary non-maximum insertion keys.
  This leaf is intentionally separate from the frozen general-source parent so
  downstream refinement sessions are not invalidated while the AutoCorres loop
  proof is developed.
\<close>

definition scheduler_ordered_loop_inv ::
  "Scheduler_V611_Parse.globals \<Rightarrow>
   Scheduler_V611_Parse.xLIST_C ptr \<Rightarrow>
   (raw_node_id, raw_key) xlist_abs \<Rightarrow> raw_key \<Rightarrow>
   Scheduler_V611_Parse.xLIST_ITEM_C ptr \<Rightarrow>
   raw_node_id list \<Rightarrow> raw_node_id list \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> bool"
where
  "scheduler_ordered_loop_inv s0 lp xs k iterator before after t
     \<longleftrightarrow>
     t = s0 \<and>
     ring xs = before @ after \<and>
     (\<forall>u \<in> set before. item_key xs u \<le> k) \<and>
     abi_item_ptr iterator =
       last (raw_end_item (abi_list_ptr lp) # before)"

lemma scheduler_ordered_loop_inv_initial:
  "scheduler_ordered_loop_inv s0 lp xs k
     (scheduler_end_item lp) [] (ring xs) s0"
  by (simp add: scheduler_ordered_loop_inv_def)

definition scheduler_ordered_loop_cond ::
  "raw_key \<Rightarrow> Scheduler_V611_Parse.xLIST_ITEM_C ptr \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> bool"
where
  "scheduler_ordered_loop_cond k it s \<longleftrightarrow>
     Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
         (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C
           (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s)) it)))
     \<le> k"

definition scheduler_ordered_loop_body ::
  "Scheduler_V611_Parse.xLIST_ITEM_C ptr \<Rightarrow>
   (Scheduler_V611_Parse.xLIST_ITEM_C ptr,
    Scheduler_V611_Parse.globals) res_monad"
where
  "scheduler_ordered_loop_body it = do {
     guard (\<lambda>_. c_guard it);
     it' \<leftarrow> gets (\<lambda>s.
       Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C
         (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s)) it));
     guard (\<lambda>s.
       c_guard
         (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C
           (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s)) it')));
     guard (\<lambda>_. c_guard it');
     return it'
   }"

lemma scheduler_ordered_loop_inv_guards:
  fixes h :: heap_mem
  assumes ordered: "raw_ordered_xlist_rel h (abi_list_ptr lp) xs"
    and heap: "h = hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s0)"
    and inv:
      "scheduler_ordered_loop_inv s0 lp xs k it before after t"
  shows
    "c_guard it \<and>
     c_guard
       (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C
         (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' t)) it))"
proof -
  let ?e = "raw_end_item (abi_list_ptr lp)"
  let ?c = "last (?e # before)"
  have state: "t = s0"
    and split: "ring xs = before @ after"
    and iterator: "abi_item_ptr it = ?c"
    using inv by (simp_all add: scheduler_ordered_loop_inv_def)
  have rel: "raw_xlist_rel h (abi_list_ptr lp) xs"
    using ordered by (simp add: raw_ordered_xlist_rel_def)
  have c_cycle: "?c \<in> insert ?e (set (ring xs))"
  proof (cases before)
    case Nil
    then show ?thesis by simp
  next
    case (Cons y ys)
    have c_eq: "?c = last before"
      using Cons by simp
    have last_before: "last before \<in> set before"
      using Cons by simp
    have before_subset: "set before \<subseteq> set (ring xs)"
      using split by auto
    have last_cycle: "last before \<in> set (ring xs)"
      using last_before before_subset by blast
    show ?thesis
      apply (subst c_eq)
      apply (rule insertI2)
      apply (rule last_cycle)
      done
  qed
  have it_exact: "it = scheduler_item_of_raw ?c"
  proof -
    have abi: "abi_item_ptr it = abi_item_ptr (scheduler_item_of_raw ?c)"
      using iterator by simp
    show ?thesis using abi by (rule iffD1[OF abi_item_ptr_eq_iff])
  qed
  have bridge:
    "c_guard (scheduler_item_of_raw ?c) \<and>
     c_guard
       (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C
         (h_val h (scheduler_item_of_raw ?c)))"
    using scheduler_ordered_loop_read_bridge[OF rel c_cycle] by simp
  show ?thesis using state heap it_exact bridge by simp
qed

lemma scheduler_ordered_loop_guard_iff:
  fixes h :: heap_mem
  assumes ordered: "raw_ordered_xlist_rel h (abi_list_ptr lp) xs"
    and key: "k = raw_key_at h (abi_item_ptr p)"
    and key_nonmax: "k \<noteq> (max_word :: 32 word)"
    and split: "ring xs = before @ after"
    and iterator:
      "abi_item_ptr it =
       last (raw_end_item (abi_list_ptr lp) # before)"
  shows
    "(Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C
        (h_val h
          (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C (h_val h it)))
       \<le> Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C (h_val h p))
     \<longleftrightarrow>
     (\<exists>y ys. after = y # ys \<and> item_key xs y \<le> k)"
proof -
  let ?e = "raw_end_item (abi_list_ptr lp)"
  let ?c = "last (?e # before)"
  let ?q = "raw_next_at h (abi_list_ptr lp) ?c"
  have rel: "raw_xlist_rel h (abi_list_ptr lp) xs"
    and sentinel: "raw_sentinel_max h (abi_list_ptr lp)"
    using ordered by (simp_all add: raw_ordered_xlist_rel_def)
  have it_exact: "it = scheduler_item_of_raw ?c"
  proof -
    have abi:
      "abi_item_ptr it = abi_item_ptr (scheduler_item_of_raw ?c)"
      using iterator by simp
    show ?thesis using abi by (rule iffD1[OF abi_item_ptr_eq_iff])
  qed
  have boundary: "?q = hd (after @ [?e])"
    using raw_ordered_scan_split_next[OF rel split] by simp
  have guard_raw:
    "(Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C
        (h_val h
          (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C (h_val h it)))
       \<le> Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C (h_val h p))
     \<longleftrightarrow>
     raw_key_at h ?q \<le> k"
    using scheduler_while_guard_iff_raw_keys[
        where h=h and c="?c" and raw_lp="abi_list_ptr lp" and p=p]
      it_exact key
    by simp
  show ?thesis
  proof (cases after)
    case Nil
    have q_end: "?q = ?e" using boundary Nil by simp
    have end_max: "raw_key_at h ?e = (max_word :: 32 word)"
      using sentinel by (simp add: raw_sentinel_max_def)
    have not_guard: "\<not> raw_key_at h ?q \<le> k"
      using q_end end_max key_nonmax by simp
    show ?thesis using Nil guard_raw not_guard by simp
  next
    case (Cons y ys)
    have q_y: "?q = y" using boundary Cons by simp
    have y_live: "y \<in> set (ring xs)"
      using split Cons by auto
    have y_key: "item_key xs y = raw_key_at h y"
      using raw_xlist_rel_live_itemD[OF rel y_live] by blast
    show ?thesis using Cons guard_raw q_y y_key by simp
  qed
qed

lemma scheduler_ordered_loop_inv_guard_step:
  fixes h :: heap_mem
  assumes ordered: "raw_ordered_xlist_rel h (abi_list_ptr lp) xs"
    and key: "k = raw_key_at h (abi_item_ptr p)"
    and key_nonmax: "k \<noteq> (max_word :: 32 word)"
    and heap: "h = hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s0)"
    and inv:
      "scheduler_ordered_loop_inv s0 lp xs k it before after t"
    and guard:
      "Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C
         (h_val h
           (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C (h_val h it)))
       \<le> Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C (h_val h p)"
  obtains y ys where
    "after = y # ys"
    "scheduler_ordered_loop_inv s0 lp xs k
       (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C (h_val h it))
       (before @ [y]) ys t"
    "length ys < length after"
proof -
  have state: "t = s0"
    and split: "ring xs = before @ after"
    and before_le: "\<forall>u \<in> set before. item_key xs u \<le> k"
    and iterator:
      "abi_item_ptr it =
       last (raw_end_item (abi_list_ptr lp) # before)"
    using inv by (simp_all add: scheduler_ordered_loop_inv_def)
  have exists:
    "\<exists>y ys. after = y # ys \<and> item_key xs y \<le> k"
    using scheduler_ordered_loop_guard_iff[
        OF ordered key key_nonmax split iterator]
      guard by simp
  then obtain y ys where after: "after = y # ys"
    and y_le: "item_key xs y \<le> k" by blast
  let ?e = "raw_end_item (abi_list_ptr lp)"
  let ?c = "last (?e # before)"
  have it_exact: "it = scheduler_item_of_raw ?c"
  proof -
    have abi: "abi_item_ptr it = abi_item_ptr (scheduler_item_of_raw ?c)"
      using iterator by simp
    show ?thesis using abi by (rule iffD1[OF abi_item_ptr_eq_iff])
  qed
  have rel: "raw_xlist_rel h (abi_list_ptr lp) xs"
    using ordered by (simp add: raw_ordered_xlist_rel_def)
  have old_boundary:
    "raw_next_at h (abi_list_ptr lp) ?c = y"
    using raw_ordered_scan_split_next[OF rel split] after by simp
  have next_abi:
    "abi_item_ptr
       (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C (h_val h it)) = y"
    using scheduler_item_next_abi_raw[
        where h=h and u="?c" and raw_lp="abi_list_ptr lp"]
      it_exact old_boundary by simp
  have new_inv:
    "scheduler_ordered_loop_inv s0 lp xs k
       (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C (h_val h it))
       (before @ [y]) ys t"
    using state split before_le after y_le next_abi
    by (simp add: scheduler_ordered_loop_inv_def)
  have decrease: "length ys < length after"
    using after by simp
  show thesis by (rule that[OF after new_inv decrease])
qed

lemma scheduler_ordered_loop_body_step:
  fixes h :: heap_mem
  assumes ordered: "raw_ordered_xlist_rel h (abi_list_ptr lp) xs"
    and key: "k = raw_key_at h (abi_item_ptr p)"
    and key_nonmax: "k \<noteq> (max_word :: 32 word)"
    and heap: "h = hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s0)"
    and inv:
      "scheduler_ordered_loop_inv s0 lp xs k it before after t"
    and cond: "scheduler_ordered_loop_cond k it t"
  shows
    "scheduler_ordered_loop_body it \<bullet> t
     \<lbrace>\<lambda>Res it' t'.
       \<exists>y ys.
         after = y # ys \<and>
         scheduler_ordered_loop_inv s0 lp xs k it'
           (before @ [y]) ys t' \<and>
         length ys < length after
     \<rbrace>"
proof -
  have state: "t = s0"
    using inv by (simp add: scheduler_ordered_loop_inv_def)
  have generated_guard:
    "Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C
       (h_val h
         (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C (h_val h it)))
     \<le> Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C (h_val h p)"
    using cond key state heap scheduler_item_key_is_raw_key_abi[
        where h=h and p=p]
    by (simp add: scheduler_ordered_loop_cond_def)
  obtain y ys where after: "after = y # ys"
    and new_inv:
      "scheduler_ordered_loop_inv s0 lp xs k
        (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C (h_val h it))
        (before @ [y]) ys t"
    and decrease: "length ys < length after"
    by (rule scheduler_ordered_loop_inv_guard_step[
          OF ordered key key_nonmax heap inv generated_guard])
  have old_guards:
    "c_guard it \<and>
     c_guard
       (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C
         (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' t)) it))"
    by (rule scheduler_ordered_loop_inv_guards[OF ordered heap inv])
  have new_guards:
    "c_guard
       (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C (h_val h it)) \<and>
     c_guard
       (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C
         (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' t))
           (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C (h_val h it))))"
    by (rule scheduler_ordered_loop_inv_guards[
          OF ordered heap new_inv])
  show ?thesis
    unfolding scheduler_ordered_loop_body_def
    apply runs_to_vcg
    using after new_inv decrease old_guards new_guards state heap
    by simp_all
qed

lemma scheduler_ordered_loop_exit_split:
  fixes h :: heap_mem
  assumes ordered: "raw_ordered_xlist_rel h (abi_list_ptr lp) xs"
    and key: "k = raw_key_at h (abi_item_ptr p)"
    and key_nonmax: "k \<noteq> (max_word :: 32 word)"
    and inv:
      "scheduler_ordered_loop_inv s0 lp xs k it before after t"
    and guard_false:
      "\<not>
       (Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C
          (h_val h
            (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C (h_val h it)))
        \<le> Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C (h_val h p))"
  shows
    "before = ordered_scan_prefix (item_key xs) k (ring xs) \<and>
     after = ordered_scan_suffix (item_key xs) k (ring xs)"
proof -
  have split: "ring xs = before @ after"
    and before_le: "\<forall>u \<in> set before. item_key xs u \<le> k"
    and iterator:
      "abi_item_ptr it =
       last (raw_end_item (abi_list_ptr lp) # before)"
    using inv by (simp_all add: scheduler_ordered_loop_inv_def)
  have no_head:
    "\<not> (\<exists>y ys. after = y # ys \<and> item_key xs y \<le> k)"
    using scheduler_ordered_loop_guard_iff[
        OF ordered key key_nonmax split iterator]
      guard_false by simp
  have sorted: "sorted (map (item_key xs) (ring xs))"
    using ordered by (simp add: raw_ordered_xlist_rel_def)
  have after_gt: "\<forall>u \<in> set after. k < item_key xs u"
  proof (cases after)
    case Nil
    then show ?thesis by simp
  next
    case (Cons y ys)
    have head_gt: "k < item_key xs y"
      using no_head Cons by auto
    have sorted_split:
      "sorted (map (item_key xs) (before @ y # ys))"
      using sorted split Cons by simp
    show ?thesis
      using sorted_suffix_head_gt_all[OF sorted_split head_gt] Cons by simp
  qed
  have identified:
    "ordered_scan_prefix (item_key xs) k (ring xs) = before \<and>
     ordered_scan_suffix (item_key xs) k (ring xs) = after"
    by (rule ordered_scan_prefix_eq_split[OF split before_le after_gt])
  show ?thesis using identified by simp
qed

theorem scheduler_ordered_generated_loop_nonmax:
  fixes h :: heap_mem
  assumes ordered: "raw_ordered_xlist_rel h (abi_list_ptr lp) xs"
    and key: "k = raw_key_at h (abi_item_ptr p)"
    and key_nonmax: "k \<noteq> (max_word :: 32 word)"
    and heap: "h = hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s0)"
    and inv:
      "scheduler_ordered_loop_inv s0 lp xs k it before after t"
  shows
    "whileLoop (scheduler_ordered_loop_cond k)
       scheduler_ordered_loop_body it \<bullet> t
     \<lbrace>\<lambda>Res it' t'.
       \<exists>before after.
         scheduler_ordered_loop_inv s0 lp xs k it' before after t' \<and>
         before = ordered_scan_prefix (item_key xs) k (ring xs) \<and>
         after = ordered_scan_suffix (item_key xs) k (ring xs)
     \<rbrace>"
proof -
  let ?I =
    "\<lambda>it' t' n.
       \<exists>before after.
         scheduler_ordered_loop_inv s0 lp xs k it' before after t' \<and>
         n = length after"
  let ?Q =
    "\<lambda>it' t'.
       \<exists>before after.
         scheduler_ordered_loop_inv s0 lp xs k it' before after t' \<and>
         before = ordered_scan_prefix (item_key xs) k (ring xs) \<and>
         after = ordered_scan_suffix (item_key xs) k (ring xs)"
  have body:
    "\<And>it' t' n.
      ?I it' t' n \<Longrightarrow>
      scheduler_ordered_loop_cond k it' t' \<Longrightarrow>
      scheduler_ordered_loop_body it' \<bullet> t'
       \<lbrace>\<lambda>Res q u. \<exists>n'. ?I q u n' \<and> (n', n) \<in> measure id\<rbrace>"
  proof -
    fix it' t' n
    assume indexed: "?I it' t' n"
      and cond: "scheduler_ordered_loop_cond k it' t'"
    then obtain before' after' where
      inv':
        "scheduler_ordered_loop_inv s0 lp xs k it' before' after' t'"
      and n: "n = length after'" by blast
    have run:
      "scheduler_ordered_loop_body it' \<bullet> t'
       \<lbrace>\<lambda>Res q u.
         \<exists>y ys.
           after' = y # ys \<and>
           scheduler_ordered_loop_inv s0 lp xs k q
             (before' @ [y]) ys u \<and>
           length ys < length after'
       \<rbrace>"
      by (rule scheduler_ordered_loop_body_step[
            OF ordered key key_nonmax heap inv' cond])
    show
      "scheduler_ordered_loop_body it' \<bullet> t'
       \<lbrace>\<lambda>Res q u. \<exists>n'. ?I q u n' \<and> (n', n) \<in> measure id\<rbrace>"
      apply (rule runs_to_weaken[OF run])
      using n by auto
  qed
  have exit:
    "\<And>it' t' n.
      ?I it' t' n \<Longrightarrow>
      \<not> scheduler_ordered_loop_cond k it' t' \<Longrightarrow>
      ?Q it' t'"
  proof -
    fix it' t' n
    assume indexed: "?I it' t' n"
      and cond_false: "\<not> scheduler_ordered_loop_cond k it' t'"
    then obtain before' after' where
      inv':
        "scheduler_ordered_loop_inv s0 lp xs k it' before' after' t'"
      by blast
    have state: "t' = s0"
      using inv' by (simp add: scheduler_ordered_loop_inv_def)
    have p_key:
      "Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C (h_val h p) = k"
      using scheduler_item_key_is_raw_key_abi[where h=h and p=p] key
      by simp
    have generated_false:
      "\<not>
       (Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C
          (h_val h
            (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C
              (h_val h it')))
        \<le> Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C (h_val h p))"
      using cond_false state heap p_key
      by (simp add: scheduler_ordered_loop_cond_def)
    have identified:
      "before' = ordered_scan_prefix (item_key xs) k (ring xs) \<and>
       after' = ordered_scan_suffix (item_key xs) k (ring xs)"
      by (rule scheduler_ordered_loop_exit_split[
            OF ordered key key_nonmax inv' generated_false])
    show "?Q it' t'" using inv' identified by blast
  qed
  have indexed_initial: "?I it t (length after)"
    using inv by blast
  show ?thesis
    by (rule runs_to_whileLoop_variant_res[
          OF body exit wf_measure indexed_initial])
qed

corollary scheduler_ordered_generated_loop_nonmax_exact_iterator:
  fixes s :: Scheduler_V611_Parse.globals
    and h :: heap_mem
    and lp :: "Scheduler_V611_Parse.xLIST_C ptr"
    and p :: "Scheduler_V611_Parse.xLIST_ITEM_C ptr"
    and xs :: "(raw_node_id, raw_key) xlist_abs"
    and k :: raw_key
    and before :: "raw_node_id list"
  defines "h \<equiv> hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s)"
    and "k \<equiv> raw_key_at h (abi_item_ptr p)"
    and "before \<equiv>
      ordered_scan_prefix (item_key xs) k (ring xs)"
  assumes ordered: "raw_ordered_xlist_rel h (abi_list_ptr lp) xs"
    and key_nonmax: "k \<noteq> (max_word :: 32 word)"
  shows
    "whileLoop (scheduler_ordered_loop_cond k)
       scheduler_ordered_loop_body (scheduler_end_item lp) \<bullet> s
     \<lbrace>\<lambda>Res it t.
       it = scheduler_item_of_raw
         (last (raw_end_item (abi_list_ptr lp) # before)) \<and>
       t = s
     \<rbrace>"
proof -
  have heap_eq:
    "h = hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s)"
    using h_def by simp
  have key_eq:
    "k = raw_key_at h (abi_item_ptr p)"
    using k_def by simp
  have initial:
    "scheduler_ordered_loop_inv s lp xs k
       (scheduler_end_item lp) [] (ring xs) s"
    by (rule scheduler_ordered_loop_inv_initial)
  have run:
    "whileLoop (scheduler_ordered_loop_cond k)
       scheduler_ordered_loop_body (scheduler_end_item lp) \<bullet> s
     \<lbrace>\<lambda>Res it t.
       \<exists>before after.
         scheduler_ordered_loop_inv s lp xs k it before after t \<and>
         before = ordered_scan_prefix (item_key xs) k (ring xs) \<and>
         after = ordered_scan_suffix (item_key xs) k (ring xs)
    \<rbrace>"
    by (rule scheduler_ordered_generated_loop_nonmax[
          OF ordered key_eq key_nonmax heap_eq initial])
  show ?thesis
    apply (rule runs_to_weaken[OF run])
    unfolding scheduler_ordered_loop_inv_def before_def
    subgoal for r t
      apply (cases r)
      subgoal for e
        by (simp only: case_exception_or_result_Exception if_False)
      subgoal for v
        apply (simp only: case_exception_or_result_Result)
        apply clarify
        apply (rule conjI)
         apply (rule iffD1[OF abi_item_ptr_eq_iff])
         apply simp
        apply simp
        done
      done
    done
qed

definition scheduler_ordered_insert_general_heap ::
  "heap_mem \<Rightarrow> Scheduler_V611_Parse.xLIST_C ptr \<Rightarrow>
   (raw_node_id, raw_key) xlist_abs \<Rightarrow>
   Scheduler_V611_Parse.xLIST_ITEM_C ptr \<Rightarrow> heap_mem"
where
  "scheduler_ordered_insert_general_heap h lp xs p =
     (let k = raw_key_at h (abi_item_ptr p);
          before = ordered_scan_prefix (item_key xs) k (ring xs);
          c = scheduler_item_of_raw
            (last (raw_end_item (abi_list_ptr lp) # before));
          q = Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C (h_val h c);
          h1 = scheduler_insert_next_heap h p q;
          h2 = scheduler_insert_previous_heap h1 q p;
          h3 = scheduler_insert_previous_heap h2 p c;
          h4 = scheduler_insert_next_heap h3 c p;
          h5 = scheduler_insert_container_heap h4 lp p
      in scheduler_insert_count_heap h5 lp)"

lemma scheduler_ordered_insert_general_heap_abi:
  assumes item_guard: "c_guard p"
    and list_guard: "c_guard lp"
  shows
    "scheduler_ordered_insert_general_heap h lp xs p =
     raw_ordered_insert_general_heap h (abi_list_ptr lp) xs
       (abi_item_ptr p)"
proof -
  have next_abi:
    "abi_item_ptr
       (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C
         (h_val h (scheduler_item_of_raw u))) =
     raw_next_at h (abi_list_ptr lp) u" for u
    by (rule scheduler_item_next_abi_raw)
  show ?thesis
    unfolding scheduler_ordered_insert_general_heap_def
      raw_ordered_insert_general_heap_def Let_def
    by (simp only:
        next_abi
        abi_item_ptr_scheduler_item_of_raw
        scheduler_insert_next_heap_abi
        scheduler_insert_previous_heap_abi
        scheduler_insert_container_heap_abi[OF item_guard]
        scheduler_insert_count_heap_abi[OF list_guard])
qed

lemma scheduler_next_state_update_to_whole:
  assumes guard: "c_guard u"
  shows
    "(\<lambda>(a :: heap_raw_state). hrs_mem_update
       (heap_update u
         (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C_update
           (\<lambda>_. q) (h_val (hrs_mem a) u))) a) =
     (\<lambda>(a :: heap_raw_state). hrs_mem_update
       (\<lambda>h. scheduler_insert_next_heap h u q) a)"
  apply (rule ext)
  subgoal for a
    apply (cases a)
    apply (simp add: hrs_mem_update_def hrs_mem_def
        scheduler_next_field_update_to_whole[OF guard])
    done
  done

lemma scheduler_previous_state_update_to_whole:
  assumes guard: "c_guard u"
  shows
    "(\<lambda>(a :: heap_raw_state). hrs_mem_update
       (heap_update u
         (Scheduler_V611_Parse.xLIST_ITEM_C.pxPrevious_C_update
           (\<lambda>_. q) (h_val (hrs_mem a) u))) a) =
     (\<lambda>(a :: heap_raw_state). hrs_mem_update
       (\<lambda>h. scheduler_insert_previous_heap h u q) a)"
  apply (rule ext)
  subgoal for a
    apply (cases a)
    apply (simp add: hrs_mem_update_def hrs_mem_def
        scheduler_previous_field_update_to_whole[OF guard])
    done
  done

lemma scheduler_container_state_update_to_whole:
  "(\<lambda>(a :: heap_raw_state). hrs_mem_update
     (heap_update p
       (Scheduler_V611_Parse.xLIST_ITEM_C.pvContainer_C_update
         (\<lambda>_. PTR_COERCE(Scheduler_V611_Parse.xLIST_C \<rightarrow> unit) lp)
         (h_val (hrs_mem a) p))) a) =
   (\<lambda>(a :: heap_raw_state). hrs_mem_update
     (\<lambda>h. scheduler_insert_container_heap h lp p) a)"
  apply (rule ext)
  subgoal for a
    apply (cases a)
    apply (simp add: hrs_mem_update_def hrs_mem_def
        scheduler_insert_container_heap_def)
    done
  done

lemma scheduler_count_state_update_to_whole:
  "(\<lambda>(a :: heap_raw_state). hrs_mem_update
     (heap_update lp
       (Scheduler_V611_Parse.xLIST_C.uxNumberOfItems_C_update
         (\<lambda>n. n + 1) (h_val (hrs_mem a) lp))) a) =
   (\<lambda>(a :: heap_raw_state). hrs_mem_update
     (\<lambda>h. scheduler_insert_count_heap h lp) a)"
  apply (rule ext)
  subgoal for a
    apply (cases a)
    apply (simp add: hrs_mem_update_def hrs_mem_def
        scheduler_insert_count_heap_def)
    done
  done

lemma raw_ordered_max_previous:
  assumes rel: "raw_xlist_rel h lp xs"
  shows
    "raw_prev_at h lp (raw_end_item lp) =
     last (raw_end_item lp # ring xs)"
proof -
  have links: "raw_ring_links h lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have path:
    "list_all
      (\<lambda>(u, v). raw_next_at h lp u = v \<and> raw_prev_at h lp v = u)
      (raw_path_edges (raw_end_item lp) (ring xs) (raw_end_item lp))"
    using links by (simp add: raw_ring_links_path_iff)
  have edge:
    "(last (raw_end_item lp # ring xs), raw_end_item lp) \<in>
      set (raw_path_edges (raw_end_item lp) (ring xs)
        (raw_end_item lp))"
    using raw_ordered_scan_path_boundary[where
        start="raw_end_item lp" and before="ring xs" and after="[]"
          and finish="raw_end_item lp"]
    by simp
  show ?thesis using path edge by (auto simp: list_all_iff)
qed

lemma scheduler_ordered_max_iterator:
  assumes rel: "raw_xlist_rel h (abi_list_ptr lp) xs"
  shows
    "Scheduler_V611_Parse.xMINI_LIST_ITEM_C.pxPrevious_C
       (Scheduler_V611_Parse.xLIST_C.xListEnd_C (h_val h lp)) =
     scheduler_item_of_raw
       (last (raw_end_item (abi_list_ptr lp) # ring xs))"
proof -
  let ?e = "raw_end_item (abi_list_ptr lp)"
  let ?c = "last (?e # ring xs)"
  have raw_previous: "raw_prev_at h (abi_list_ptr lp) ?e = ?c"
    by (rule raw_ordered_max_previous[OF rel])
  have abi_read:
    "List_V611_Raw_Skip_Translation.xMINI_LIST_ITEM_C.pxPrevious_C
       (List_V611_Raw_Skip_Translation.xLIST_C.xListEnd_C
         (h_val h (abi_list_ptr lp))) =
     abi_item_ptr
       (Scheduler_V611_Parse.xMINI_LIST_ITEM_C.pxPrevious_C
         (Scheduler_V611_Parse.xLIST_C.xListEnd_C (h_val h lp)))"
    by (rule abi_sentinel_previous_h_val)
  have raw_read:
    "List_V611_Raw_Skip_Translation.xMINI_LIST_ITEM_C.pxPrevious_C
       (List_V611_Raw_Skip_Translation.xLIST_C.xListEnd_C
         (h_val h (abi_list_ptr lp))) = ?c"
    using raw_previous by (simp add: raw_prev_at_def raw_end_item_def)
  have abi_eq:
    "abi_item_ptr
       (Scheduler_V611_Parse.xMINI_LIST_ITEM_C.pxPrevious_C
         (Scheduler_V611_Parse.xLIST_C.xListEnd_C (h_val h lp))) =
     abi_item_ptr (scheduler_item_of_raw ?c)"
    using abi_read raw_read by simp
  show ?thesis using abi_eq by (rule iffD1[OF abi_item_ptr_eq_iff])
qed

theorem scheduler_vListInsert_ordered_nonmax_exact_state:
  fixes s :: Scheduler_V611_Parse.globals
  assumes ordered:
      "raw_ordered_xlist_rel
        (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
        (abi_list_ptr lp) xs"
    and fresh:
      "raw_fresh_for_insert (abi_list_ptr lp) (ring xs)
        (abi_item_ptr p)"
    and key_nonmax:
      "raw_key_at
        (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
        (abi_item_ptr p) \<noteq> (max_word :: 32 word)"
  shows
    "Scheduler_V611_Delay_Translation.vListInsert' lp p \<bullet> s
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       t = scheduler_mem_state
         (raw_ordered_insert_general_heap
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
           (abi_list_ptr lp) xs (abi_item_ptr p)) s
     \<rbrace>"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s)"
  let ?k = "raw_key_at ?h (abi_item_ptr p)"
  let ?before =
    "ordered_scan_prefix (item_key xs) ?k (ring xs)"
  let ?rc =
    "last (raw_end_item (abi_list_ptr lp) # ?before)"
  let ?c = "scheduler_item_of_raw ?rc"
  let ?rq = "raw_next_at ?h (abi_list_ptr lp) ?rc"
  let ?q = "scheduler_item_of_raw ?rq"
  have rel: "raw_xlist_rel ?h (abi_list_ptr lp) xs"
    using ordered by (simp add: raw_ordered_xlist_rel_def)
  have raw_p_guard: "c_guard (abi_item_ptr p)"
    using fresh by (simp add: raw_fresh_for_insert_def)
  have p_guard: "c_guard p"
    using raw_p_guard by (rule iffD1[OF abi_item_ptr_c_guard])
  have raw_lp_guard: "c_guard (abi_list_ptr lp)"
    using rel by (simp add: raw_xlist_rel_def raw_xlist_layout_def)
  have lp_guard: "c_guard lp"
    using raw_lp_guard by (rule iffD1[OF abi_list_ptr_c_guard])
  have rc_cycle:
    "?rc \<in> insert (raw_end_item (abi_list_ptr lp)) (set (ring xs))"
    by (rule ordered_scan_predecessor_in_cycle)
  have rq_cycle:
    "?rq \<in> insert (raw_end_item (abi_list_ptr lp)) (set (ring xs))"
    by (rule raw_ordered_scan_successor_in_cycle[OF rel])
  have c_guard: "c_guard ?c"
    by (rule scheduler_cycle_node_guard[OF rel rc_cycle])
  have q_guard: "c_guard ?q"
    by (rule scheduler_cycle_node_guard[OF rel rq_cycle])
  have c_next:
    "Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C (h_val ?h ?c) = ?q"
    by (rule scheduler_item_next_is_raw_successor)
  have c_next_guard:
    "c_guard
       (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C (h_val ?h ?c))"
    using c_next q_guard by simp
  have c_guard_empty:
    "?before = [] \<Longrightarrow>
     c_guard
       (scheduler_item_of_raw (raw_end_item (abi_list_ptr lp)))"
    using c_guard by simp
  have c_guard_nonempty:
    "?before \<noteq> [] \<Longrightarrow>
     c_guard (scheduler_item_of_raw (last ?before))"
    using c_guard by simp
  have c_next_guard_empty:
    "?before = [] \<Longrightarrow>
     c_guard
       (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C
         (h_val ?h
           (scheduler_item_of_raw (raw_end_item (abi_list_ptr lp)))))"
    using c_next_guard by simp
  have c_next_guard_nonempty:
    "?before \<noteq> [] \<Longrightarrow>
     c_guard
       (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C
         (h_val ?h (scheduler_item_of_raw (last ?before))))"
    using c_next_guard by simp
  have next_update_empty:
    "?before = [] \<Longrightarrow>
     scheduler_insert_next_heap h
       (scheduler_item_of_raw (raw_end_item (abi_list_ptr lp))) q =
     heap_update
       (scheduler_item_of_raw (raw_end_item (abi_list_ptr lp)))
       (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C_update
         (\<lambda>_. q)
         (h_val h
           (scheduler_item_of_raw (raw_end_item (abi_list_ptr lp))))) h"
    for h q
  proof -
    assume empty: "?before = []"
    show ?thesis
      by (rule scheduler_next_field_update_to_whole[
            OF c_guard_empty[OF empty]])
  qed
  have next_update_nonempty:
    "?before \<noteq> [] \<Longrightarrow>
     scheduler_insert_next_heap h
       (scheduler_item_of_raw (last ?before)) q =
     heap_update (scheduler_item_of_raw (last ?before))
       (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C_update
         (\<lambda>_. q) (h_val h (scheduler_item_of_raw (last ?before)))) h"
    for h q
  proof -
    assume nonempty: "?before \<noteq> []"
    show ?thesis
      by (rule scheduler_next_field_update_to_whole[
            OF c_guard_nonempty[OF nonempty]])
  qed
  have next_state_update_empty:
    "?before = [] \<Longrightarrow>
     (\<lambda>(a :: heap_raw_state). hrs_mem_update
       (heap_update
         (scheduler_item_of_raw (raw_end_item (abi_list_ptr lp)))
         (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C_update
           (\<lambda>_. p)
           (h_val (hrs_mem a)
             (scheduler_item_of_raw (raw_end_item (abi_list_ptr lp)))))) a) =
     (\<lambda>(a :: heap_raw_state). hrs_mem_update
       (\<lambda>h. scheduler_insert_next_heap h
         (scheduler_item_of_raw (raw_end_item (abi_list_ptr lp))) p) a)"
  proof -
    assume empty: "?before = []"
    show ?thesis
      by (rule scheduler_next_state_update_to_whole[
            OF c_guard_empty[OF empty]])
  qed
  have next_state_update_nonempty:
    "?before \<noteq> [] \<Longrightarrow>
     (\<lambda>(a :: heap_raw_state). hrs_mem_update
       (heap_update (scheduler_item_of_raw (last ?before))
         (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C_update
           (\<lambda>_. p)
           (h_val (hrs_mem a) (scheduler_item_of_raw (last ?before))))) a) =
     (\<lambda>(a :: heap_raw_state). hrs_mem_update
       (\<lambda>h. scheduler_insert_next_heap h
         (scheduler_item_of_raw (last ?before)) p) a)"
  proof -
    assume nonempty: "?before \<noteq> []"
    show ?thesis
      by (rule scheduler_next_state_update_to_whole[
            OF c_guard_nonempty[OF nonempty]])
  qed
  have hex_max:
    "(0xFFFFFFFF :: 32 word) = (max_word :: 32 word)"
    by simp
  have key_nonvalue:
    "Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C (h_val ?h p)
       \<noteq> 0xFFFFFFFF"
    apply (subst hex_max)
    using key_nonmax
    by (simp add: scheduler_item_key_is_raw_key_abi)
  have item_key_read:
    "Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C (h_val ?h p) = ?k"
    by (rule scheduler_item_key_is_raw_key_abi)
  have sentinel_ptr:
    "PTR(Scheduler_V611_Parse.xLIST_ITEM_C)
       &(lp\<rightarrow>[''xListEnd_C'']) = scheduler_end_item lp"
    by (simp add: scheduler_end_item_def)
  have initial:
    "scheduler_ordered_loop_inv s lp xs ?k
       (scheduler_end_item lp) [] (ring xs) s"
    by (rule scheduler_ordered_loop_inv_initial)
  have initial_guards:
    "c_guard (scheduler_end_item lp) \<and>
     c_guard
       (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C
         (h_val ?h (scheduler_end_item lp)))"
    using scheduler_ordered_loop_inv_guards[
        OF ordered refl initial] by simp
  have loop_run:
    "whileLoop (scheduler_ordered_loop_cond ?k)
       scheduler_ordered_loop_body (scheduler_end_item lp) \<bullet> s
     \<lbrace>\<lambda>Res it t. it = ?c \<and> t = s\<rbrace>"
    using scheduler_ordered_generated_loop_nonmax_exact_iterator[
        where s=s and lp=lp and p=p and xs=xs]
      ordered key_nonmax
    by simp
  have concrete:
    "scheduler_ordered_insert_general_heap ?h lp xs p =
     raw_ordered_insert_general_heap ?h (abi_list_ptr lp) xs
       (abi_item_ptr p)"
    by (rule scheduler_ordered_insert_general_heap_abi[OF p_guard lp_guard])
  have loop_run_generated:
    "whileLoop
       (\<lambda>it sa.
          Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C
            (h_val
              (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' sa))
              (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C
                (h_val
                  (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' sa))
                  it)))
          \<le> Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C
               (h_val ?h p))
       (\<lambda>it. do {
          guard (\<lambda>_. c_guard it);
          it' \<leftarrow> gets (\<lambda>sa.
            Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C
              (h_val
                (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' sa))
                it));
          guard (\<lambda>sa.
            c_guard
              (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C
                (h_val
                  (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' sa))
                  it')));
          guard (\<lambda>_. c_guard it');
          return it'
        })
       (scheduler_end_item lp) \<bullet> s
     \<lbrace>\<lambda>Res it t. it = ?c \<and> t = s\<rbrace>"
    using loop_run
    unfolding scheduler_ordered_loop_cond_def
      scheduler_ordered_loop_body_def item_key_read
    by assumption
  show ?thesis
    unfolding Scheduler_V611_Delay_Translation.vListInsert'_def
      scheduler_ordered_loop_cond_def scheduler_ordered_loop_body_def
    apply runs_to_vcg
    apply (simp_all only:
        hrs_mem_update key_nonvalue sentinel_ptr c_next)
    apply (simp_all add:
        h_val_heap_update p_guard lp_guard c_guard q_guard initial_guards)
    apply (rule runs_to_weaken[OF loop_run_generated])
    subgoal for r t
      apply (cases r)
      subgoal for e
        by (simp only: case_exception_or_result_Exception if_False)
      subgoal for v
        apply (simp only: case_exception_or_result_Result)
        apply clarify
        apply runs_to_vcg
        apply (simp_all only: hrs_mem_update c_next)
        apply (simp_all add:
            h_val_heap_update p_guard lp_guard c_guard q_guard
            c_guard_empty c_guard_nonempty
            c_next_guard_empty c_next_guard_nonempty)
        apply (simp_all only:
            scheduler_next_state_update_to_whole[OF p_guard]
            scheduler_previous_state_update_to_whole[OF p_guard]
            next_state_update_empty next_state_update_nonempty
            scheduler_container_state_update_to_whole
            scheduler_count_state_update_to_whole)
        subgoal
          apply (simp only: concrete[symmetric])
          apply (cases s)
          apply (simp add:
              scheduler_mem_state_def
              hrs_mem_update_def
              hrs_mem_def
              split: prod.splits)
          apply clarify
          apply (simp only:
              scheduler_next_field_update_to_whole[OF p_guard, symmetric]
              scheduler_previous_field_update_to_whole[OF p_guard, symmetric]
              scheduler_previous_field_update_to_whole[OF q_guard, symmetric])
          apply (fold scheduler_insert_next_heap_def
              scheduler_insert_previous_heap_def)
          apply (simp add:
              scheduler_ordered_insert_general_heap_def Let_def)
          done
        subgoal
          apply (subst next_state_update_nonempty)
           apply assumption
          apply (simp only: concrete[symmetric])
          apply (cases s)
          apply (simp add:
              scheduler_mem_state_def
              hrs_mem_update_def
              hrs_mem_def
              split: prod.splits)
          apply clarify
          apply (simp only:
              scheduler_next_field_update_to_whole[OF p_guard, symmetric]
              scheduler_previous_field_update_to_whole[OF p_guard, symmetric]
              scheduler_previous_field_update_to_whole[OF q_guard, symmetric])
          apply (fold scheduler_insert_next_heap_def
              scheduler_insert_previous_heap_def)
          apply (simp add:
              scheduler_ordered_insert_general_heap_def Let_def)
          done
        done
      done
    done
qed

theorem scheduler_vListInsert_ordered_max_exact_state:
  fixes s :: Scheduler_V611_Parse.globals
  assumes ordered:
      "raw_ordered_xlist_rel
        (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
        (abi_list_ptr lp) xs"
    and fresh:
      "raw_fresh_for_insert (abi_list_ptr lp) (ring xs)
        (abi_item_ptr p)"
    and key_max:
      "raw_key_at
        (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
        (abi_item_ptr p) = (max_word :: 32 word)"
  shows
    "Scheduler_V611_Delay_Translation.vListInsert' lp p \<bullet> s
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       t = scheduler_mem_state
         (raw_ordered_insert_general_heap
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
           (abi_list_ptr lp) xs (abi_item_ptr p)) s
     \<rbrace>"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s)"
  let ?rc = "last (raw_end_item (abi_list_ptr lp) # ring xs)"
  let ?c = "scheduler_item_of_raw ?rc"
  let ?rq = "raw_next_at ?h (abi_list_ptr lp) ?rc"
  let ?q = "scheduler_item_of_raw ?rq"
  have rel: "raw_xlist_rel ?h (abi_list_ptr lp) xs"
    using ordered by (simp add: raw_ordered_xlist_rel_def)
  have raw_p_guard: "c_guard (abi_item_ptr p)"
    using fresh by (simp add: raw_fresh_for_insert_def)
  have p_guard: "c_guard p"
    using raw_p_guard by (rule iffD1[OF abi_item_ptr_c_guard])
  have raw_lp_guard: "c_guard (abi_list_ptr lp)"
    using rel by (simp add: raw_xlist_rel_def raw_xlist_layout_def)
  have lp_guard: "c_guard lp"
    using raw_lp_guard by (rule iffD1[OF abi_list_ptr_c_guard])
  have rc_cycle:
    "?rc \<in> insert (raw_end_item (abi_list_ptr lp)) (set (ring xs))"
  proof (cases "ring xs")
    case Nil
    then show ?thesis by simp
  next
    case (Cons y ys)
    have rc_eq: "?rc = last (ring xs)" using Cons by simp
    have last_live: "last (ring xs) \<in> set (ring xs)"
      using Cons by simp
    show ?thesis
      apply (subst rc_eq)
      apply (rule insertI2)
      apply (rule last_live)
      done
  qed
  have links: "raw_ring_links ?h (abi_list_ptr lp) (ring xs)"
    using rel by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have rq_cycle:
    "?rq \<in> insert (raw_end_item (abi_list_ptr lp)) (set (ring xs))"
    by (rule raw_ring_links_next_closed[OF links rc_cycle])
  have c_guard: "c_guard ?c"
    by (rule scheduler_cycle_node_guard[OF rel rc_cycle])
  have q_guard: "c_guard ?q"
    by (rule scheduler_cycle_node_guard[OF rel rq_cycle])
  have c_next:
    "Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C (h_val ?h ?c) = ?q"
    by (rule scheduler_item_next_is_raw_successor)
  have c_next_guard:
    "c_guard
       (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C (h_val ?h ?c))"
    using c_next q_guard by simp
  have max_c_guard_empty:
    "ring xs = [] \<Longrightarrow>
     c_guard
       (scheduler_item_of_raw (raw_end_item (abi_list_ptr lp)))"
    using c_guard by simp
  have max_c_guard_nonempty:
    "ring xs \<noteq> [] \<Longrightarrow>
     c_guard (scheduler_item_of_raw (last (ring xs)))"
    using c_guard by simp
  have max_next_guard_empty:
    "ring xs = [] \<Longrightarrow>
     c_guard
       (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C
         (h_val ?h
           (scheduler_item_of_raw (raw_end_item (abi_list_ptr lp)))))"
    using c_next_guard by simp
  have max_next_guard_nonempty:
    "ring xs \<noteq> [] \<Longrightarrow>
     c_guard
       (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C
         (h_val ?h (scheduler_item_of_raw (last (ring xs)))))"
    using c_next_guard by simp
  have max_raw_q_guard_empty:
    "ring xs = [] \<Longrightarrow>
     c_guard
       (scheduler_item_of_raw
         (List_V611_Raw_Skip_Translation.xMINI_LIST_ITEM_C.pxNext_C
           (List_V611_Raw_Skip_Translation.xLIST_C.xListEnd_C
             (h_val ?h (abi_list_ptr lp)))))"
    using q_guard by (simp add: raw_next_at_def raw_end_item_def)
  have max_raw_q_guard_nonempty:
    "ring xs \<noteq> [] \<Longrightarrow>
     c_guard
       (scheduler_item_of_raw
         (raw_next_at ?h (abi_list_ptr lp) (last (ring xs))))"
    using q_guard by simp
  have max_next_state_empty:
    "ring xs = [] \<Longrightarrow>
     (\<lambda>(a :: heap_raw_state). hrs_mem_update
       (heap_update
         (scheduler_item_of_raw (raw_end_item (abi_list_ptr lp)))
         (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C_update
           (\<lambda>_. p)
           (h_val (hrs_mem a)
             (scheduler_item_of_raw (raw_end_item (abi_list_ptr lp)))))) a) =
     (\<lambda>(a :: heap_raw_state). hrs_mem_update
       (\<lambda>h. scheduler_insert_next_heap h
         (scheduler_item_of_raw (raw_end_item (abi_list_ptr lp))) p) a)"
  proof -
    assume empty: "ring xs = []"
    show ?thesis
      by (rule scheduler_next_state_update_to_whole[
            OF max_c_guard_empty[OF empty]])
  qed
  have max_next_state_nonempty:
    "ring xs \<noteq> [] \<Longrightarrow>
     (\<lambda>(a :: heap_raw_state). hrs_mem_update
       (heap_update (scheduler_item_of_raw (last (ring xs)))
         (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C_update
           (\<lambda>_. p)
           (h_val (hrs_mem a)
             (scheduler_item_of_raw (last (ring xs)))))) a) =
     (\<lambda>(a :: heap_raw_state). hrs_mem_update
       (\<lambda>h. scheduler_insert_next_heap h
         (scheduler_item_of_raw (last (ring xs))) p) a)"
  proof -
    assume nonempty: "ring xs \<noteq> []"
    show ?thesis
      by (rule scheduler_next_state_update_to_whole[
            OF max_c_guard_nonempty[OF nonempty]])
  qed
  have key_value:
    "Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C (h_val ?h p) =
       0xFFFFFFFF"
    using key_max by (simp add: scheduler_item_key_is_raw_key_abi)
  have iterator:
    "Scheduler_V611_Parse.xMINI_LIST_ITEM_C.pxPrevious_C
       (Scheduler_V611_Parse.xLIST_C.xListEnd_C (h_val ?h lp)) = ?c"
    by (rule scheduler_ordered_max_iterator[OF rel])
  have concrete:
    "scheduler_ordered_insert_general_heap ?h lp xs p =
     raw_ordered_insert_general_heap ?h (abi_list_ptr lp) xs
       (abi_item_ptr p)"
    by (rule scheduler_ordered_insert_general_heap_abi[OF p_guard lp_guard])
  show ?thesis
    unfolding Scheduler_V611_Delay_Translation.vListInsert'_def
    apply runs_to_vcg
    apply (simp_all only:
        hrs_mem_update key_value iterator c_next)
    apply (simp_all add:
        h_val_heap_update p_guard lp_guard c_guard q_guard
        max_c_guard_empty max_c_guard_nonempty
        max_next_guard_empty max_next_guard_nonempty
        max_raw_q_guard_empty max_raw_q_guard_nonempty)
    apply (rule conjI)
    subgoal
      apply (rule impI)
      apply (simp only:
          scheduler_next_state_update_to_whole[OF p_guard]
          scheduler_previous_state_update_to_whole[OF p_guard]
          max_next_state_empty
          scheduler_container_state_update_to_whole
          scheduler_count_state_update_to_whole)
      apply (simp only: concrete[symmetric])
      apply (simp only:
          scheduler_ordered_insert_general_heap_def
          key_max ordered_scan_prefix_max_word Let_def)
      apply (cases s)
      apply (simp add:
          scheduler_mem_state_def
          hrs_mem_update_def
          hrs_mem_def
          split: prod.splits)
      apply clarify
      apply (simp only:
          scheduler_next_field_update_to_whole[OF p_guard, symmetric]
          scheduler_previous_field_update_to_whole[OF p_guard, symmetric]
          scheduler_previous_field_update_to_whole[OF q_guard, symmetric])
      apply (fold scheduler_insert_next_heap_def
          scheduler_insert_previous_heap_def)
      apply simp
      done
    subgoal
      apply (rule impI)
      apply (simp only:
          scheduler_next_state_update_to_whole[OF p_guard]
          scheduler_previous_state_update_to_whole[OF p_guard]
          scheduler_container_state_update_to_whole
          scheduler_count_state_update_to_whole)
      apply (subst max_next_state_nonempty)
       apply assumption
      apply (simp only: concrete[symmetric])
      apply (simp only:
          scheduler_ordered_insert_general_heap_def
          key_max ordered_scan_prefix_max_word Let_def)
      apply (cases s)
      apply (simp add:
          scheduler_mem_state_def
          hrs_mem_update_def
          hrs_mem_def
          split: prod.splits)
      apply clarify
      apply (simp only:
          scheduler_next_field_update_to_whole[OF p_guard, symmetric]
          scheduler_previous_field_update_to_whole[OF p_guard, symmetric]
          scheduler_previous_field_update_to_whole[OF q_guard, symmetric])
      apply (fold scheduler_insert_next_heap_def
          scheduler_insert_previous_heap_def)
      apply simp
      done
    done
qed

theorem scheduler_vListInsert_ordered_general_exact_state:
  fixes s :: Scheduler_V611_Parse.globals
  assumes ordered:
      "raw_ordered_xlist_rel
        (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
        (abi_list_ptr lp) xs"
    and fresh:
      "raw_fresh_for_insert (abi_list_ptr lp) (ring xs)
        (abi_item_ptr p)"
  shows
    "Scheduler_V611_Delay_Translation.vListInsert' lp p \<bullet> s
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       t = scheduler_mem_state
         (raw_ordered_insert_general_heap
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
           (abi_list_ptr lp) xs (abi_item_ptr p)) s
     \<rbrace>"
proof (cases
    "raw_key_at (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
       (abi_item_ptr p) = (max_word :: 32 word)")
  case True
  show ?thesis
    by (rule scheduler_vListInsert_ordered_max_exact_state[
          OF ordered fresh True])
next
  case False
  show ?thesis
    by (rule scheduler_vListInsert_ordered_nonmax_exact_state[
          OF ordered fresh False])
qed

end
