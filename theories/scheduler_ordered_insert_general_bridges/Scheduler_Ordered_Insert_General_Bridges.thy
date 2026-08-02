theory Scheduler_Ordered_Insert_General_Bridges
  imports
    "EAL6_FreeRTOS_V611_Scheduler_P2_Insert_Source.Scheduler_P2_Insert_Source"
    "EAL6_FreeRTOS_V611_Scheduler_P2_Raw_Relation.Scheduler_P2_Raw_Relation"
begin

text \<open>
  Generated-scheduler read bridges for an arbitrary node in an arbitrary raw
  list cycle.  The inverse coercion below changes only the generated record
  universe; it preserves the machine address.
\<close>

definition scheduler_item_of_raw ::
  "List_V611_Raw_Skip_Translation.xLIST_ITEM_C ptr \<Rightarrow>
   Scheduler_V611_Parse.xLIST_ITEM_C ptr"
where
  "scheduler_item_of_raw p =
     PTR_COERCE(List_V611_Raw_Skip_Translation.xLIST_ITEM_C \<rightarrow>
       Scheduler_V611_Parse.xLIST_ITEM_C) p"

lemma abi_item_ptr_scheduler_item_of_raw [simp]:
  "abi_item_ptr (scheduler_item_of_raw p) = p"
  by (simp add: scheduler_item_of_raw_def abi_item_ptr_def)

lemma scheduler_item_of_raw_abi_item_ptr [simp]:
  "scheduler_item_of_raw (abi_item_ptr p) = p"
  by (simp add: scheduler_item_of_raw_def abi_item_ptr_def)

lemma scheduler_cycle_node_guard:
  assumes rel: "raw_xlist_rel h (abi_list_ptr lp) xs"
    and cycle:
      "u \<in> insert (raw_end_item (abi_list_ptr lp)) (set (ring xs))"
  shows "c_guard (scheduler_item_of_raw u)"
proof -
  have raw_guard: "c_guard u"
    by (rule raw_xlist_rel_cycle_node_guard[OF rel cycle])
  have coerced_guard:
      "c_guard (abi_item_ptr (scheduler_item_of_raw u))"
    using raw_guard by simp
  show ?thesis
    using coerced_guard by (rule iffD1[OF abi_item_ptr_c_guard])
qed

lemma scheduler_item_next_abi_raw:
  "abi_item_ptr
      (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C
        (h_val h (scheduler_item_of_raw u))) =
    raw_next_at h raw_lp u"
proof -
  have abi_read:
    "List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pxNext_C
       (h_val h (abi_item_ptr (scheduler_item_of_raw u))) =
     abi_item_ptr
       (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C
         (h_val h (scheduler_item_of_raw u)))"
    by (rule abi_item_next_h_val)
  have raw_read:
    "List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pxNext_C
       (h_val h u) = raw_next_at h raw_lp u"
    by (rule raw_full_next_is_sentinel_safe)
  show ?thesis using abi_read raw_read by simp
qed

lemma scheduler_item_next_is_raw_successor:
  "Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C
      (h_val h (scheduler_item_of_raw u)) =
    scheduler_item_of_raw (raw_next_at h raw_lp u)"
proof -
  have coerced:
    "abi_item_ptr
       (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C
         (h_val h (scheduler_item_of_raw u))) =
     abi_item_ptr (scheduler_item_of_raw (raw_next_at h raw_lp u))"
    by (simp add: scheduler_item_next_abi_raw)
  show ?thesis
    using coerced by (rule iffD1[OF abi_item_ptr_eq_iff])
qed

lemma scheduler_item_key_is_raw_key:
  "Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C
      (h_val h (scheduler_item_of_raw u)) = raw_key_at h u"
proof -
  have abi_read:
    "List_V611_Raw_Skip_Translation.xLIST_ITEM_C.xItemValue_C
       (h_val h (abi_item_ptr (scheduler_item_of_raw u))) =
     Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C
       (h_val h (scheduler_item_of_raw u))"
    by (rule abi_item_key_h_val)
  show ?thesis
    using abi_read by (simp add: raw_key_at_def)
qed

lemma scheduler_item_key_is_raw_key_abi:
  "Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C (h_val h p) =
    raw_key_at h (abi_item_ptr p)"
  using scheduler_item_key_is_raw_key[where h=h and u="abi_item_ptr p"]
  by simp

lemma scheduler_live_node_key_is_item_key:
  assumes rel: "raw_xlist_rel h (abi_list_ptr lp) xs"
    and live: "u \<in> set (ring xs)"
  shows
    "Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C
       (h_val h (scheduler_item_of_raw u)) = item_key xs u"
proof -
  have raw_key: "item_key xs u = raw_key_at h u"
    using raw_xlist_rel_live_itemD[OF rel live] by blast
  show ?thesis using raw_key scheduler_item_key_is_raw_key by simp
qed

lemma scheduler_cycle_successor_guard:
  assumes rel: "raw_xlist_rel h (abi_list_ptr lp) xs"
    and cycle:
      "u \<in> insert (raw_end_item (abi_list_ptr lp)) (set (ring xs))"
  shows
    "c_guard (scheduler_item_of_raw (raw_next_at h (abi_list_ptr lp) u))"
proof -
  have links:
    "raw_ring_links h (abi_list_ptr lp) (ring xs)"
    using rel by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have next_cycle:
    "raw_next_at h (abi_list_ptr lp) u \<in>
       insert (raw_end_item (abi_list_ptr lp)) (set (ring xs))"
    by (rule raw_ring_links_next_closed[OF links cycle])
  show ?thesis
    by (rule scheduler_cycle_node_guard[OF rel next_cycle])
qed

lemma scheduler_while_guard_iff_raw_keys:
  "(Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C
       (h_val h
         (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C
           (h_val h (scheduler_item_of_raw c))))
       \<le> Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C (h_val h p))
   \<longleftrightarrow>
   raw_key_at h (raw_next_at h raw_lp c) \<le>
     raw_key_at h (abi_item_ptr p)"
proof -
  have next_abi:
    "abi_item_ptr
       (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C
         (h_val h (scheduler_item_of_raw c))) =
     raw_next_at h raw_lp c"
    by (rule scheduler_item_next_abi_raw)
  have next_key:
    "Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C
       (h_val h
         (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C
           (h_val h (scheduler_item_of_raw c)))) =
     raw_key_at h (raw_next_at h raw_lp c)"
    using scheduler_item_key_is_raw_key_abi[
        where h=h and
          p="Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C
            (h_val h (scheduler_item_of_raw c))"]
      next_abi
    by simp
  have item_key:
    "Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C (h_val h p) =
     raw_key_at h (abi_item_ptr p)"
    by (rule scheduler_item_key_is_raw_key_abi)
  show ?thesis using next_key item_key by simp
qed

theorem scheduler_ordered_loop_read_bridge:
  assumes rel: "raw_xlist_rel h (abi_list_ptr lp) xs"
    and cycle:
      "c \<in> insert (raw_end_item (abi_list_ptr lp)) (set (ring xs))"
  defines "q \<equiv> raw_next_at h (abi_list_ptr lp) c"
  shows
    "c_guard (scheduler_item_of_raw c) \<and>
     c_guard (scheduler_item_of_raw q) \<and>
     abi_item_ptr
       (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C
         (h_val h (scheduler_item_of_raw c))) = q \<and>
     Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C
       (h_val h (scheduler_item_of_raw c)) = scheduler_item_of_raw q \<and>
     Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C
       (h_val h (scheduler_item_of_raw c)) = raw_key_at h c \<and>
     Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C
       (h_val h (scheduler_item_of_raw q)) = raw_key_at h q \<and>
     (\<forall>p.
       (Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C
          (h_val h
            (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C
              (h_val h (scheduler_item_of_raw c))))
          \<le> Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C (h_val h p))
       \<longleftrightarrow>
       raw_key_at h q \<le> raw_key_at h (abi_item_ptr p))"
proof -
  have c_guard: "c_guard (scheduler_item_of_raw c)"
    by (rule scheduler_cycle_node_guard[OF rel cycle])
  have q_guard: "c_guard (scheduler_item_of_raw q)"
    unfolding q_def
    by (rule scheduler_cycle_successor_guard[OF rel cycle])
  have next_abi:
    "abi_item_ptr
       (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C
         (h_val h (scheduler_item_of_raw c))) = q"
    unfolding q_def by (rule scheduler_item_next_abi_raw)
  have next_exact:
    "Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C
       (h_val h (scheduler_item_of_raw c)) = scheduler_item_of_raw q"
    unfolding q_def by (rule scheduler_item_next_is_raw_successor)
  have c_key:
    "Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C
       (h_val h (scheduler_item_of_raw c)) = raw_key_at h c"
    by (rule scheduler_item_key_is_raw_key)
  have q_key:
    "Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C
       (h_val h (scheduler_item_of_raw q)) = raw_key_at h q"
    by (rule scheduler_item_key_is_raw_key)
  have guard_iff:
    "\<forall>p.
      (Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C
         (h_val h
           (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C
             (h_val h (scheduler_item_of_raw c))))
         \<le> Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C (h_val h p))
      \<longleftrightarrow>
      raw_key_at h q \<le> raw_key_at h (abi_item_ptr p)"
    unfolding q_def
    by (rule allI, rule scheduler_while_guard_iff_raw_keys)
  show ?thesis
    using c_guard q_guard next_abi next_exact c_key q_key guard_iff
    by blast
qed

end
