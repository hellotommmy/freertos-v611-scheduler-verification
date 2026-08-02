theory Scheduler_Ordered_Insert_General_Source
  imports
    "EAL6_FreeRTOS_V611_Scheduler_P2_Insert_Source.Scheduler_P2_Insert_Source"
    "EAL6_FreeRTOS_V611_Scheduler_Ordered_Insert_General_Bridges.Scheduler_Ordered_Insert_General_Bridges"
    "EAL6_FreeRTOS_V611_List_Raw_R6_Ordered_Insert_Empty_Refinement.List_V611_Raw_R6_Ordered_Insert_Empty_Refinement"
begin

text \<open>
  Parametric prefix and transformer bricks for the stock ordered insertion
  loop.  Nothing in this theory fixes a task, priority, clock value, item key,
  ring length, insertion position, or source branch.
\<close>

definition ordered_scan_prefix ::
  "('a \<Rightarrow> 'k::linorder) \<Rightarrow> 'k \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "ordered_scan_prefix key k xs = takeWhile (\<lambda>x. key x \<le> k) xs"

definition ordered_scan_suffix ::
  "('a \<Rightarrow> 'k::linorder) \<Rightarrow> 'k \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "ordered_scan_suffix key k xs = dropWhile (\<lambda>x. key x \<le> k) xs"

definition ordered_scan_inv ::
  "'a \<Rightarrow> ('a \<Rightarrow> 'k::linorder) \<Rightarrow> 'k \<Rightarrow>
   'a list \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> bool"
where
  "ordered_scan_inv end key k xs iterator n \<longleftrightarrow>
     n \<le> length xs \<and>
     iterator = last (end # take n xs) \<and>
     (\<forall>x \<in> set (take n xs). key x \<le> k)"

lemma ordered_scan_inv_initial:
  "ordered_scan_inv end key k xs end 0"
  by (simp add: ordered_scan_inv_def)

lemma ordered_scan_inv_step:
  assumes inv: "ordered_scan_inv end key k xs iterator n"
    and in_range: "n < length xs"
    and guard: "key (xs ! n) \<le> k"
  shows
    "ordered_scan_inv end key k xs (xs ! n) (Suc n)"
proof -
  have n_le: "n \<le> length xs"
    using in_range by simp
  have take_suc:
    "take (Suc n) xs = take n xs @ [xs ! n]"
    using in_range by (simp add: take_Suc_conv_app_nth)
  have prefix:
    "\<forall>x \<in> set (take n xs). key x \<le> k"
    using inv by (simp add: ordered_scan_inv_def)
  show ?thesis
    using in_range guard prefix
    by (simp add: ordered_scan_inv_def take_suc)
qed

lemma ordered_scan_inv_next:
  assumes inv: "ordered_scan_inv end key k xs iterator n"
    and in_range: "n < length xs"
  shows
    "hd (drop n xs @ [end]) = xs ! n"
  using in_range by (simp add: hd_drop_conv_nth)

lemma ordered_scan_prefix_suffix:
  "ordered_scan_prefix key k xs @ ordered_scan_suffix key k xs = xs"
  by (simp add: ordered_scan_prefix_def ordered_scan_suffix_def)

lemma ordered_scan_prefix_all_le:
  "x \<in> set (ordered_scan_prefix key k xs) \<Longrightarrow> key x \<le> k"
  by (auto simp: ordered_scan_prefix_def dest: set_takeWhileD)

lemma ordered_scan_suffix_head_gt:
  assumes suffix: "ordered_scan_suffix key k xs = y # ys"
  shows "k < key y"
  using suffix
proof (induction xs arbitrary: y ys)
  case Nil
  then show ?case by (simp add: ordered_scan_suffix_def)
next
  case (Cons x xs)
  show ?case
  proof (cases "key x \<le> k")
    case True
    then show ?thesis
      using Cons.IH Cons.prems
      by (simp add: ordered_scan_suffix_def)
  next
    case False
    then show ?thesis
      using Cons.prems
      by (simp add: ordered_scan_suffix_def)
  qed
qed

lemma stable_key_insert_take_drop:
  fixes key :: "'a \<Rightarrow> 'k::linorder"
  shows
    "stable_key_insert key x xs =
       ordered_scan_prefix key (key x) xs @
       x # ordered_scan_suffix key (key x) xs"
proof (induction xs)
  case Nil
  then show ?case
    by (simp add: ordered_scan_prefix_def ordered_scan_suffix_def)
next
  case (Cons y ys)
  show ?case
  proof (cases "key y \<le> key x")
    case True
    then have not_less: "\<not> key x < key y" by simp
    show ?thesis
      using Cons.IH True not_less
      by (simp add: ordered_scan_prefix_def ordered_scan_suffix_def)
  next
    case False
    then have less: "key x < key y" by simp
    show ?thesis
      using False less
      by (simp add: ordered_scan_prefix_def ordered_scan_suffix_def)
  qed
qed

lemma ordered_scan_prefix_max_word:
  fixes key :: "'a \<Rightarrow> 32 word"
  shows "ordered_scan_prefix key max_word xs = xs"
  by (induction xs) (simp_all add: ordered_scan_prefix_def)

lemma raw_ordered_scan_path_boundary:
  "(last (start # before), hd (after @ [finish])) \<in>
     set (raw_path_edges start (before @ after) finish)"
proof (induction before arbitrary: start)
  case Nil
  show ?case by (cases after) simp_all
next
  case (Cons x xs)
  have tail:
    "(last (x # xs), hd (after @ [finish])) \<in>
       set (raw_path_edges x (xs @ after) finish)"
    by (rule Cons.IH)
  show ?case using tail by simp
qed

lemma raw_ordered_scan_split_next:
  assumes rel: "raw_xlist_rel h lp xs"
    and split: "ring xs = before @ after"
  shows
    "raw_next_at h lp (last (raw_end_item lp # before)) =
       hd (after @ [raw_end_item lp])"
proof -
  have links: "raw_ring_links h lp (before @ after)"
    using rel split
    by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have path:
    "list_all
      (\<lambda>(u, v). raw_next_at h lp u = v \<and> raw_prev_at h lp v = u)
      (raw_path_edges (raw_end_item lp) (before @ after)
        (raw_end_item lp))"
    using links by (simp add: raw_ring_links_path_iff)
  have edge:
    "(last (raw_end_item lp # before),
       hd (after @ [raw_end_item lp])) \<in>
      set (raw_path_edges (raw_end_item lp) (before @ after)
        (raw_end_item lp))"
    by (rule raw_ordered_scan_path_boundary)
  show ?thesis using path edge by (auto simp: list_all_iff)
qed

lemma ordered_scan_prefix_eq_split:
  fixes key :: "'a \<Rightarrow> 'k::linorder"
  assumes split: "xs = before @ after"
    and before_le: "\<forall>x \<in> set before. key x \<le> k"
    and after_gt: "\<forall>x \<in> set after. k < key x"
  shows
    "ordered_scan_prefix key k xs = before \<and>
     ordered_scan_suffix key k xs = after"
proof -
  have take_before:
    "takeWhile (\<lambda>x. key x \<le> k) before = before"
    using before_le by (induction before) auto
  have drop_before:
    "dropWhile (\<lambda>x. key x \<le> k) before = []"
    using before_le by (induction before) auto
  have take_after:
    "takeWhile (\<lambda>x. key x \<le> k) after = []"
    using after_gt by (cases after) auto
  have drop_after:
    "dropWhile (\<lambda>x. key x \<le> k) after = after"
    using after_gt by (cases after) auto
  show ?thesis
    using split take_before drop_before take_after drop_after
    by (simp add: ordered_scan_prefix_def ordered_scan_suffix_def)
qed

lemma sorted_suffix_head_gt_all:
  fixes key :: "'a \<Rightarrow> 'k::linorder"
  assumes sorted: "sorted (map key (before @ y # ys))"
    and head_gt: "k < key y"
  shows "\<forall>z \<in> set (y # ys). k < key z"
proof -
  have suffix_sorted: "sorted (map key (y # ys))"
    using sorted by (simp add: sorted_append)
  have y_le: "\<forall>z \<in> set ys. key y \<le> key z"
    using suffix_sorted by simp
  show ?thesis using head_gt y_le by auto
qed

definition raw_ordered_insert_general_heap ::
  "heap_mem \<Rightarrow> xLIST_C ptr \<Rightarrow>
   (raw_node_id, raw_key) xlist_abs \<Rightarrow> raw_node_id \<Rightarrow>
   heap_mem"
where
  "raw_ordered_insert_general_heap h lp xs p =
     (let k = raw_key_at h p;
          before = ordered_scan_prefix (item_key xs) k (ring xs);
          c = last (raw_end_item lp # before);
          q = raw_next_at h lp c;
          h1 = raw_insert_next_heap h p q;
          h2 = raw_insert_previous_heap h1 q p;
          h3 = raw_insert_previous_heap h2 p c;
          h4 = raw_insert_next_heap h3 c p;
          h5 = raw_insert_container_heap h4 lp p
      in raw_insert_count_heap h5 lp)"

lemma raw_ordered_insert_general_heap_source_order:
  fixes h :: heap_mem
    and lp :: "xLIST_C ptr"
    and xs :: "(raw_node_id, raw_key) xlist_abs"
    and p :: raw_node_id
  shows
    "raw_ordered_insert_general_heap h lp xs p =
       (let k = raw_key_at h p;
            before = ordered_scan_prefix (item_key xs) k (ring xs);
            c = last (raw_end_item lp # before);
            q = raw_next_at h lp c
        in raw_insert_count_heap
             (raw_insert_container_heap
               (raw_insert_next_heap
                 (raw_insert_previous_heap
                   (raw_insert_previous_heap
                     (raw_insert_next_heap h p q) q p) p c) c p) lp p) lp)"
  by (simp add: raw_ordered_insert_general_heap_def Let_def)

lemma ordered_scan_predecessor_in_cycle:
  "last (end # ordered_scan_prefix key k xs) \<in> insert end (set xs)"
proof (cases "ordered_scan_prefix key k xs")
  case Nil
  then show ?thesis by simp
next
  case (Cons y ys)
  have last_prefix:
    "last (ordered_scan_prefix key k xs) \<in>
       set (ordered_scan_prefix key k xs)"
    using Cons by simp
  have prefix_subset:
    "set (ordered_scan_prefix key k xs) \<subseteq> set xs"
    by (auto simp: ordered_scan_prefix_def dest: set_takeWhileD)
  have last_in_xs:
    "last (ordered_scan_prefix key k xs) \<in> set xs"
    using last_prefix prefix_subset by blast
  have last_cons:
    "last (end # ordered_scan_prefix key k xs) =
     last (ordered_scan_prefix key k xs)"
    using Cons by simp
  show ?thesis using last_cons last_in_xs by simp
qed

lemma raw_ordered_scan_successor_in_cycle:
  fixes k :: raw_key
  assumes rel: "raw_xlist_rel h lp xs"
  defines
    "c \<equiv>
       last (raw_end_item lp #
         ordered_scan_prefix (item_key xs) k (ring xs))"
  shows
    "raw_next_at h lp c \<in>
       insert (raw_end_item lp) (set (ring xs))"
proof -
  have links: "raw_ring_links h lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have c_cycle:
    "c \<in> insert (raw_end_item lp) (set (ring xs))"
    unfolding c_def by (rule ordered_scan_predecessor_in_cycle)
  show ?thesis
    by (rule raw_ring_links_next_closed[OF links c_cycle])
qed

lemma raw_ordered_insert_general_heap_count_effect:
  assumes rel: "raw_xlist_rel h lp xs"
    and fresh: "raw_fresh_for_insert lp (ring xs) p"
  shows
    "uxNumberOfItems_C
       (h_val (raw_ordered_insert_general_heap h lp xs p) lp) =
     uxNumberOfItems_C (h_val h lp) + 1"
proof -
  let ?k = "raw_key_at h p"
  let ?before =
    "ordered_scan_prefix (item_key xs) ?k (ring xs)"
  let ?c = "last (raw_end_item lp # ?before)"
  let ?q = "raw_next_at h lp ?c"
  let ?h1 = "raw_insert_next_heap h p ?q"
  let ?h2 = "raw_insert_previous_heap ?h1 ?q p"
  let ?h3 = "raw_insert_previous_heap ?h2 p ?c"
  let ?h4 = "raw_insert_next_heap ?h3 ?c p"
  let ?h5 = "raw_insert_container_heap ?h4 lp p"
  have layout: "raw_xlist_layout lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def)
  have lp_guard: "c_guard lp"
    using layout by (simp add: raw_xlist_layout_def)
  have c_cycle:
    "?c \<in> insert (raw_end_item lp) (set (ring xs))"
    by (rule ordered_scan_predecessor_in_cycle)
  have q_cycle:
    "?q \<in> insert (raw_end_item lp) (set (ring xs))"
    by (rule raw_ordered_scan_successor_in_cycle[OF rel])
  have item_list:
    "raw_item_region p \<inter> raw_list_region lp = {}"
    using fresh by (simp add: raw_fresh_for_insert_def)
  have h1_list: "h_val ?h1 lp = h_val h lp"
    by (rule raw_insert_next_heap_preserves_list[OF fresh])
  have h2_count:
    "uxNumberOfItems_C (h_val ?h2 lp) =
     uxNumberOfItems_C (h_val ?h1 lp)"
    unfolding raw_insert_previous_heap_def
    by (rule raw_previous_field_update_preserves_count[OF layout q_cycle])
  have h3_list: "h_val ?h3 lp = h_val ?h2 lp"
    by (rule raw_insert_previous_heap_preserves_list[OF fresh])
  have h4_count:
    "uxNumberOfItems_C (h_val ?h4 lp) =
     uxNumberOfItems_C (h_val ?h3 lp)"
    unfolding raw_insert_next_heap_def
    by (rule raw_next_field_update_preserves_count[OF layout c_cycle])
  have h5_list: "h_val ?h5 lp = h_val ?h4 lp"
    unfolding raw_insert_container_heap_def
    by (rule raw_item_update_preserves_disjoint_list[OF item_list])
  have final_count:
    "uxNumberOfItems_C (h_val (raw_insert_count_heap ?h5 lp) lp) =
     uxNumberOfItems_C (h_val ?h5 lp) + 1"
    unfolding raw_insert_count_heap_def
    using lp_guard by (simp add: h_val_heap_update)
  show ?thesis
    using h1_list h2_count h3_list h4_count h5_list final_count
    by (simp add: raw_ordered_insert_general_heap_def Let_def)
qed

lemma raw_ordered_insert_general_heap_index_effect:
  assumes rel: "raw_xlist_rel h lp xs"
    and fresh: "raw_fresh_for_insert lp (ring xs) p"
  shows
    "pxIndex_C
       (h_val (raw_ordered_insert_general_heap h lp xs p) lp) =
     pxIndex_C (h_val h lp)"
proof -
  let ?k = "raw_key_at h p"
  let ?before =
    "ordered_scan_prefix (item_key xs) ?k (ring xs)"
  let ?c = "last (raw_end_item lp # ?before)"
  let ?q = "raw_next_at h lp ?c"
  let ?h1 = "raw_insert_next_heap h p ?q"
  let ?h2 = "raw_insert_previous_heap ?h1 ?q p"
  let ?h3 = "raw_insert_previous_heap ?h2 p ?c"
  let ?h4 = "raw_insert_next_heap ?h3 ?c p"
  let ?h5 = "raw_insert_container_heap ?h4 lp p"
  have layout: "raw_xlist_layout lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def)
  have lp_guard: "c_guard lp"
    using layout by (simp add: raw_xlist_layout_def)
  have c_cycle:
    "?c \<in> insert (raw_end_item lp) (set (ring xs))"
    by (rule ordered_scan_predecessor_in_cycle)
  have q_cycle:
    "?q \<in> insert (raw_end_item lp) (set (ring xs))"
    by (rule raw_ordered_scan_successor_in_cycle[OF rel])
  have item_list:
    "raw_item_region p \<inter> raw_list_region lp = {}"
    using fresh by (simp add: raw_fresh_for_insert_def)
  have h1_list: "h_val ?h1 lp = h_val h lp"
    by (rule raw_insert_next_heap_preserves_list[OF fresh])
  have h2_index:
    "pxIndex_C (h_val ?h2 lp) = pxIndex_C (h_val ?h1 lp)"
    unfolding raw_insert_previous_heap_def
    by (rule raw_previous_field_update_preserves_index[OF layout q_cycle])
  have h3_list: "h_val ?h3 lp = h_val ?h2 lp"
    by (rule raw_insert_previous_heap_preserves_list[OF fresh])
  have h4_index:
    "pxIndex_C (h_val ?h4 lp) = pxIndex_C (h_val ?h3 lp)"
    unfolding raw_insert_next_heap_def
    by (rule raw_next_field_update_preserves_index[OF layout c_cycle])
  have h5_list: "h_val ?h5 lp = h_val ?h4 lp"
    unfolding raw_insert_container_heap_def
    by (rule raw_item_update_preserves_disjoint_list[OF item_list])
  have final_index:
    "pxIndex_C (h_val (raw_insert_count_heap ?h5 lp) lp) =
     pxIndex_C (h_val ?h5 lp)"
    unfolding raw_insert_count_heap_def
    using lp_guard by (simp add: h_val_heap_update)
  show ?thesis
    using h1_list h2_index h3_list h4_index h5_list final_index
    by (simp add: raw_ordered_insert_general_heap_def Let_def)
qed

definition scheduler_ordered_scan_inv ::
  "Scheduler_V611_Parse.globals \<Rightarrow> heap_mem \<Rightarrow>
   Scheduler_V611_Parse.xLIST_C ptr \<Rightarrow>
   Scheduler_V611_Parse.xLIST_ITEM_C ptr \<Rightarrow>
   (raw_node_id, raw_key) xlist_abs \<Rightarrow> raw_key \<Rightarrow>
   Scheduler_V611_Parse.xLIST_ITEM_C ptr \<Rightarrow>
   raw_node_id list \<Rightarrow> raw_node_id list \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> bool"
where
  "scheduler_ordered_scan_inv s0 h0 lp p xs k iterator before after t
     \<longleftrightarrow>
     t = s0 \<and>
     h0 = hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s0) \<and>
     raw_ordered_xlist_rel h0 (abi_list_ptr lp) xs \<and>
     raw_fresh_for_insert (abi_list_ptr lp) (ring xs) (abi_item_ptr p) \<and>
     k = raw_key_at h0 (abi_item_ptr p) \<and>
     ring xs = before @ after \<and>
     (\<forall>u \<in> set before. item_key xs u \<le> k) \<and>
     (let c = last (raw_end_item (abi_list_ptr lp) # before);
          q = raw_next_at h0 (abi_list_ptr lp) c
      in iterator = scheduler_item_of_raw c \<and>
         q = hd (after @ [raw_end_item (abi_list_ptr lp)]) \<and>
         c_guard iterator \<and>
         c_guard (scheduler_item_of_raw q) \<and>
         Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C
           (h_val h0 iterator) = scheduler_item_of_raw q \<and>
         Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C
           (h_val h0 iterator) = raw_key_at h0 c \<and>
         Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C
           (h_val h0 (scheduler_item_of_raw q)) = raw_key_at h0 q)"

lemma scheduler_ordered_scan_inv_initial:
  assumes ordered:
      "raw_ordered_xlist_rel h0 (abi_list_ptr lp) xs"
    and fresh:
      "raw_fresh_for_insert (abi_list_ptr lp) (ring xs) (abi_item_ptr p)"
    and heap: "h0 = hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s0)"
    and key: "k = raw_key_at h0 (abi_item_ptr p)"
  shows
    "scheduler_ordered_scan_inv s0 h0 lp p xs k
       (scheduler_end_item lp) [] (ring xs) s0"
proof -
  have rel:
    "raw_xlist_rel h0 (abi_list_ptr lp) xs"
    using ordered by (simp add: raw_ordered_xlist_rel_def)
  let ?e = "raw_end_item (abi_list_ptr lp)"
  have boundary:
    "raw_next_at h0 (abi_list_ptr lp) ?e =
       hd (ring xs @ [?e])"
    using raw_ordered_scan_split_next[OF rel, where before="[]" and
        after="ring xs"] by simp
  have bridge:
    "c_guard (scheduler_item_of_raw ?e) \<and>
     c_guard (scheduler_item_of_raw
       (raw_next_at h0 (abi_list_ptr lp) ?e)) \<and>
     Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C
       (h_val h0 (scheduler_item_of_raw ?e)) =
       scheduler_item_of_raw (raw_next_at h0 (abi_list_ptr lp) ?e) \<and>
     Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C
       (h_val h0 (scheduler_item_of_raw ?e)) = raw_key_at h0 ?e \<and>
     Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C
       (h_val h0 (scheduler_item_of_raw
         (raw_next_at h0 (abi_list_ptr lp) ?e))) =
       raw_key_at h0 (raw_next_at h0 (abi_list_ptr lp) ?e)"
    using scheduler_ordered_loop_read_bridge[OF rel, where c="?e"]
    by simp
  have end_exact: "scheduler_end_item lp = scheduler_item_of_raw ?e"
  proof -
    have abi:
      "abi_item_ptr (scheduler_end_item lp) =
       abi_item_ptr (scheduler_item_of_raw ?e)"
      by simp
    show ?thesis using abi by (rule iffD1[OF abi_item_ptr_eq_iff])
  qed
  show ?thesis
    using ordered fresh heap key boundary bridge end_exact
    by (simp add: scheduler_ordered_scan_inv_def Let_def)
qed

lemma scheduler_ordered_scan_inv_guard_step:
  assumes inv:
      "scheduler_ordered_scan_inv s0 h0 lp p xs k iterator
        before after t"
    and key_nonmax: "k \<noteq> (max_word :: 32 word)"
    and guard:
      "Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C
         (h_val h0
           (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C
             (h_val h0 iterator)))
       \<le> Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C (h_val h0 p)"
  obtains y ys where
    "after = y # ys"
    "scheduler_ordered_scan_inv s0 h0 lp p xs k
       (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C (h_val h0 iterator))
       (before @ [y]) ys t"
    "length ys < length after"
proof -
  let ?e = "raw_end_item (abi_list_ptr lp)"
  let ?c = "last (?e # before)"
  let ?q = "raw_next_at h0 (abi_list_ptr lp) ?c"
  have state: "t = s0"
    and heap: "h0 = hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s0)"
    and ordered: "raw_ordered_xlist_rel h0 (abi_list_ptr lp) xs"
    and fresh:
      "raw_fresh_for_insert (abi_list_ptr lp) (ring xs) (abi_item_ptr p)"
    and key: "k = raw_key_at h0 (abi_item_ptr p)"
    and split: "ring xs = before @ after"
    and before_le: "\<forall>u \<in> set before. item_key xs u \<le> k"
    and iterator: "iterator = scheduler_item_of_raw ?c"
    and boundary: "?q = hd (after @ [?e])"
    and next_exact:
      "Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C
         (h_val h0 iterator) = scheduler_item_of_raw ?q"
    and q_key:
      "Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C
         (h_val h0 (scheduler_item_of_raw ?q)) = raw_key_at h0 ?q"
    using inv
    by (auto simp: scheduler_ordered_scan_inv_def Let_def)
  have rel: "raw_xlist_rel h0 (abi_list_ptr lp) xs"
    and sentinel: "raw_sentinel_max h0 (abi_list_ptr lp)"
    and sorted: "sorted (map (item_key xs) (ring xs))"
    using ordered by (simp_all add: raw_ordered_xlist_rel_def)
  have p_key:
    "Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C (h_val h0 p) = k"
    using scheduler_item_key_is_raw_key_abi[where h=h0 and p=p] key
    by simp
  have guard_raw: "raw_key_at h0 ?q \<le> k"
    using guard next_exact q_key p_key by simp
  have after_nonempty: "after \<noteq> []"
  proof
    assume "after = []"
    then have q_end: "?q = ?e" using boundary by simp
    have end_max: "raw_key_at h0 ?e = (max_word :: 32 word)"
      using sentinel by (simp add: raw_sentinel_max_def)
    have "(max_word :: 32 word) \<le> k"
      using guard_raw q_end end_max by simp
    then have "k = (max_word :: 32 word)" by simp
    then show False using key_nonmax by contradiction
  qed
  obtain y ys where after: "after = y # ys"
    using after_nonempty by (cases after) auto
  have y_live: "y \<in> set (ring xs)"
    using split after by auto
  have y_key: "item_key xs y = raw_key_at h0 y"
    using raw_xlist_rel_live_itemD[OF rel y_live] by blast
  have q_y: "?q = y"
    using boundary after by simp
  have y_le: "item_key xs y \<le> k"
    using guard_raw q_y y_key by simp
  have new_split: "ring xs = (before @ [y]) @ ys"
    using split after by simp
  have new_before_le:
    "\<forall>u \<in> set (before @ [y]). item_key xs u \<le> k"
    using before_le y_le by simp
  have new_boundary:
    "raw_next_at h0 (abi_list_ptr lp) y = hd (ys @ [?e])"
    using raw_ordered_scan_split_next[OF rel new_split] by simp
  have y_cycle: "y \<in> insert ?e (set (ring xs))"
    using y_live by simp
  have new_bridge:
    "c_guard (scheduler_item_of_raw y) \<and>
     c_guard (scheduler_item_of_raw
       (raw_next_at h0 (abi_list_ptr lp) y)) \<and>
     Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C
       (h_val h0 (scheduler_item_of_raw y)) =
       scheduler_item_of_raw (raw_next_at h0 (abi_list_ptr lp) y) \<and>
     Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C
       (h_val h0 (scheduler_item_of_raw y)) = raw_key_at h0 y \<and>
     Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C
       (h_val h0 (scheduler_item_of_raw
         (raw_next_at h0 (abi_list_ptr lp) y))) =
       raw_key_at h0 (raw_next_at h0 (abi_list_ptr lp) y)"
    using scheduler_ordered_loop_read_bridge[OF rel y_cycle]
    by simp
  have new_last: "last (?e # before @ [y]) = y"
    by simp
  have new_inv:
    "scheduler_ordered_scan_inv s0 h0 lp p xs k
       (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C (h_val h0 iterator))
       (before @ [y]) ys t"
    using state heap ordered fresh key new_split new_before_le next_exact
      q_y new_boundary new_bridge new_last
    by (simp add: scheduler_ordered_scan_inv_def Let_def)
  have decrease: "length ys < length after"
    using after by simp
  show thesis by (rule that[OF after new_inv decrease])
qed

end
