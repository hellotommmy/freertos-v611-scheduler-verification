# General remove then insert-end sequential needle

Status: static design only. No Isabelle command was run for this note. The
existing insert transformer theory, `theories/ROOT`, and the build script are
deliberately untouched.

## Goal and dependency boundary

The smallest leaf theory should import exactly the two public refinement
interfaces:

```isabelle
theory List_V611_Raw_R6_Remove_Insert_End_Sequential
  imports
    "EAL6_FreeRTOS_V611_List_Raw_R6_Remove_General_Refinement.List_V611_Raw_R6_Remove_General_Refinement"
    "EAL6_FreeRTOS_V611_List_Raw_R6_Insert_Post_Transformer.List_V611_Raw_R6_Insert_Post_Transformer"
begin
```

The insert-side dependency is the stable theorem
`raw_vListInsertEnd_general_refines_via_transformer`. Its current signature is:

```isabelle
raw_xlist_rel (hrs_mem (t_hrs_' s)) lp xs \<Longrightarrow>
raw_fresh_for_insert lp (ring xs) p \<Longrightarrow>
raw_count_can_increment xs \<Longrightarrow>
vListInsertEnd' lp p \<bullet> s
\<lbrace>\<lambda>r t.
  r = Result () \<and>
  raw_xlist_rel (hrs_mem (t_hrs_' t)) lp
    (list_insert_end_abs p
      (raw_key_at (hrs_mem (t_hrs_' s)) p) xs)\<rbrace>
```

The remove-side dependency is `raw_vListRemove_general_refines`, augmented in
this leaf with one missing observation: the key of the removed item. This is
necessary because `raw_xlist_rel ... (list_remove_abs p xs)` intentionally says
nothing about `p` after `p` has left the live ring.

## Exact public sequential statement

Use a named wrapper so that `runs_to_bind` is the only composition mechanism:

```isabelle
definition raw_remove_then_insert_end' where
  "raw_remove_then_insert_end' lp p =
     (do {
        vListRemove' p;
        vListInsertEnd' lp p
      })"

theorem raw_vListRemove_then_InsertEnd_general_refines:
  assumes rel:
    "raw_xlist_rel (hrs_mem (t_hrs_' s)) lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "raw_remove_then_insert_end' lp p \<bullet> s
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       raw_xlist_rel (hrs_mem (t_hrs_' t)) lp
         (list_insert_end_abs p
           (raw_key_at (hrs_mem (t_hrs_' s)) p)
           (list_remove_abs p xs))
     \<rbrace>"
```

There should be no external freshness or count-increment assumption. In
particular, requiring `raw_count_can_increment xs` would incorrectly exclude a
full original list even though the preceding removal creates exactly one free
count slot.

## Bridge 1: the removed member is fresh for re-insertion

Recommended reusable lemma:

```isabelle
lemma raw_member_fresh_for_reinsert:
  assumes rel: "raw_xlist_rel h lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "raw_fresh_for_insert lp (ring (list_remove_abs p xs)) p"
```

Proof ledger:

```isabelle
proof -
  have layout: "raw_xlist_layout lp (ring xs)"
    using rel by (simp add: raw_xlist_rel_def)
  have distinct: "distinct (ring xs)"
    using raw_xlist_rel_distinct_cycle_nodes[OF rel] by simp
  have not_live: "p \<notin> set (remove1 p (ring xs))"
    by (rule raw_distinct_member_notin_remove1[OF distinct member])
  have p_guard: "c_guard p"
    using layout member by (auto simp: raw_xlist_layout_def)
  have p_not_end: "p \<noteq> raw_end_item lp"
    using layout member by (auto simp: raw_xlist_layout_def)
  have p_list:
    "raw_item_region p \<inter> raw_list_region lp = {}"
    using layout member by (auto simp: raw_xlist_layout_def)
  have p_items:
    "\<forall>q \<in> set (remove1 p (ring xs)).
       raw_item_region p \<inter> raw_item_region q = {}"
  proof (intro ballI)
    fix q
    assume survivor: "q \<in> set (remove1 p (ring xs))"
    have info: "q \<in> set (ring xs) \<and> q \<noteq> p"
      by (rule raw_distinct_remove1_survivorD[
            OF distinct member survivor])
    show "raw_item_region p \<inter> raw_item_region q = {}"
      using layout member info
      by (auto simp: raw_xlist_layout_def)
  qed
  show ?thesis
    using p_guard p_not_end not_live p_list p_items
    by (simp add: raw_fresh_for_insert_def list_remove_abs_def)
qed
```

This fact must be derived from the original relation, not from the intermediate
remove relation: the latter has forgotten the layout facts for `p`.

## Bridge 2: removal always creates count headroom

Recommended reusable lemma:

```isabelle
lemma raw_list_remove_count_can_increment:
  assumes rel: "raw_xlist_rel h lp xs"
    and member: "p \<in> set (ring xs)"
  shows "raw_count_can_increment (list_remove_abs p xs)"
```

Proof ledger:

```isabelle
proof -
  let ?w = "uxNumberOfItems_C (h_val h lp)"
  have count_eq: "length (ring xs) = unat ?w"
    using raw_xlist_rel_countD[OF rel] by simp
  have word_bound: "?w \<le> (max_word :: 32 word)"
    by (rule word_order.extremum)
  have count_bound:
    "length (ring xs) \<le> unat (max_word :: 32 word)"
    using count_eq word_bound by (simp add: word_le_nat_alt)
  have removed_lt:
    "length (remove1 p (ring xs)) < length (ring xs)"
    using member by (simp add: length_remove1)
  have shortened_bound:
    "length (remove1 p (ring xs)) < unat (max_word :: 32 word)"
    using removed_lt count_bound by arith
  show ?thesis
    using shortened_bound
    by (simp add: raw_count_can_increment_def list_remove_abs_def)
qed
```

The `word_order.extremum` step expresses only that a 32-bit word is at most
the maximum 32-bit word; no non-wrap assumption on the original list is used.

## Bridge 3: removal preserves the removed item's key

The existing live-payload theorem only quantifies over survivors. Build the
missing fact by projecting the already checked exact heap transformer; do not
symbolically execute `vListRemove'` again.

First add two small field/frame bricks:

```isabelle
lemma raw_remove_index_heap_preserves_live_item:
  assumes layout: "raw_xlist_layout lp rs"
    and live: "q \<in> set rs"
  shows
    "h_val (raw_remove_index_heap h lp p) q = h_val h q"
proof (cases "pxIndex_C (h_val h lp) = p")
  case True
  have frame:
    "h_val
       (heap_update lp
         (pxIndex_C_update
           (\<lambda>_. xLIST_ITEM_C.pxPrevious_C (h_val h p))
           (h_val h lp)) h) q =
     h_val h q"
    by (rule raw_layout_list_update_preserves_live_item[OF layout live])
  show ?thesis
    using True frame by (simp add: raw_remove_index_heap_def)
next
  case False
  then show ?thesis by (simp add: raw_remove_index_heap_def)
qed

lemma raw_remove_container_heap_preserves_key:
  assumes guard: "c_guard p"
  shows
    "raw_key_at (raw_remove_container_heap h p) p = raw_key_at h p"
  using guard
  by (simp add: raw_remove_container_heap_def raw_key_at_def
      h_val_heap_update)
```

Then compose the suffix writes. The final count update reuses the existing
`raw_remove_count_heap_preserves_live_item` theorem.

```isabelle
lemma raw_remove_suffix_heap_preserves_removed_key:
  assumes layout: "raw_xlist_layout lp rs"
    and member: "p \<in> set rs"
  shows
    "raw_key_at (raw_remove_suffix_heap h lp p) p = raw_key_at h p"
proof -
  let ?hi = "raw_remove_index_heap h lp p"
  let ?hc = "raw_remove_container_heap ?hi p"
  have guard: "c_guard p"
    using layout member by (auto simp: raw_xlist_layout_def)
  have index_same: "h_val ?hi p = h_val h p"
    by (rule raw_remove_index_heap_preserves_live_item[OF layout member])
  have container_key: "raw_key_at ?hc p = raw_key_at ?hi p"
    by (rule raw_remove_container_heap_preserves_key[OF guard])
  have count_same:
    "h_val (raw_remove_count_heap ?hc lp) p = h_val ?hc p"
    by (rule raw_remove_count_heap_preserves_live_item[OF layout member])
  show ?thesis
    using index_same container_key count_same
    by (simp add: raw_remove_suffix_heap_def raw_key_at_def)
qed
```

Lift this through the two unlink writes and the concrete transformer:

```isabelle
lemma raw_remove_concrete_heap_preserves_removed_key:
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
  have suffix_key:
    "raw_key_at
       (raw_remove_suffix_heap (raw_source_unlink_two h p) lp p) p =
     raw_key_at (raw_source_unlink_two h p) p"
    by (rule raw_remove_suffix_heap_preserves_removed_key[
          OF layout member])
  show ?thesis
    using raw_remove_concrete_heap_eq[OF rel member]
      suffix_key unlink_key
    by (simp add: raw_remove_source_heap_def)
qed
```

The key point is that
`raw_source_unlink_two_preserves_live_payload[OF rel member member]` may be
instantiated with `q = p`: `p` is live in the *pre*-remove ring. The subsequent
container clear changes only `pvContainer_C`, not `xItemValue_C`.

Project the pure key fact from the existing exact source heap theorem:

```isabelle
theorem raw_vListRemove_general_removed_key_effect:
  assumes rel:
    "raw_xlist_rel (hrs_mem (t_hrs_' s)) lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "vListRemove' p \<bullet> s
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       raw_key_at (hrs_mem (t_hrs_' t)) p =
         raw_key_at (hrs_mem (t_hrs_' s)) p
     \<rbrace>"
proof -
  note heap = raw_vListRemove_general_heap_effect[OF rel member]
  note key = raw_remove_concrete_heap_preserves_removed_key[OF rel member]
  show ?thesis
    apply (rule runs_to_weaken[OF heap])
    using key by auto
qed
```

Conjoin it with the public remove refinement:

```isabelle
theorem raw_vListRemove_general_refines_with_removed_key:
  assumes rel:
    "raw_xlist_rel (hrs_mem (t_hrs_' s)) lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "vListRemove' p \<bullet> s
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       raw_xlist_rel (hrs_mem (t_hrs_' t)) lp (list_remove_abs p xs) \<and>
       raw_key_at (hrs_mem (t_hrs_' t)) p =
         raw_key_at (hrs_mem (t_hrs_' s)) p
     \<rbrace>"
proof -
  note refined = raw_vListRemove_general_refines[OF rel member]
  note key = raw_vListRemove_general_removed_key_effect[OF rel member]
  have grouped:
    "vListRemove' p \<bullet> s
     \<lbrace>\<lambda>r t.
       (r = Result () \<and>
        raw_xlist_rel (hrs_mem (t_hrs_' t)) lp (list_remove_abs p xs)) \<and>
       (r = Result () \<and>
        raw_key_at (hrs_mem (t_hrs_' t)) p =
          raw_key_at (hrs_mem (t_hrs_' s)) p)
     \<rbrace>"
    using refined key by (simp only: runs_to_conj)
  show ?thesis
    apply (rule runs_to_weaken[OF grouped])
    by auto
qed
```

## `runs_to_bind` composition skeleton

AutoCorres2's exact rule is `runs_to_bind`. For this normal-result-only first
command, its exception obligation is vacuous because the strengthened remove
postcondition contains `r = Result ()`.

```isabelle
proof -
  let ?ys = "list_remove_abs p xs"
  let ?k = "raw_key_at (hrs_mem (t_hrs_' s)) p"
  let ?Q =
    "\<lambda>r t.
       r = Result () \<and>
       raw_xlist_rel (hrs_mem (t_hrs_' t)) lp
         (list_insert_end_abs p ?k ?ys)"
  have fresh: "raw_fresh_for_insert lp (ring ?ys) p"
    by (rule raw_member_fresh_for_reinsert[OF rel member])
  have can_increment: "raw_count_can_increment ?ys"
    by (rule raw_list_remove_count_can_increment[OF rel member])
  have remove:
    "vListRemove' p \<bullet> s
     \<lbrace>\<lambda>r u.
       r = Result () \<and>
       raw_xlist_rel (hrs_mem (t_hrs_' u)) lp ?ys \<and>
       raw_key_at (hrs_mem (t_hrs_' u)) p = ?k
     \<rbrace>"
    by (rule raw_vListRemove_general_refines_with_removed_key[
          OF rel member])

  have bind_pre:
    "vListRemove' p \<bullet> s
     \<lbrace>\<lambda>r u.
       (\<forall>v. r = Result v \<longrightarrow>
          vListInsertEnd' lp p \<bullet> u \<lbrace>?Q\<rbrace>) \<and>
       (\<forall>e. r = Exception e \<longrightarrow> e \<noteq> default
          \<longrightarrow> ?Q (Exception e) u)
     \<rbrace>"
  proof (rule runs_to_weaken[OF remove])
    fix r u
    assume post:
      "r = Result () \<and>
       raw_xlist_rel (hrs_mem (t_hrs_' u)) lp ?ys \<and>
       raw_key_at (hrs_mem (t_hrs_' u)) p = ?k"
    have rel_u: "raw_xlist_rel (hrs_mem (t_hrs_' u)) lp ?ys"
      using post by simp
    have key_u: "raw_key_at (hrs_mem (t_hrs_' u)) p = ?k"
      using post by simp
    show
      "(\<forall>v. r = Result v \<longrightarrow>
          vListInsertEnd' lp p \<bullet> u \<lbrace>?Q\<rbrace>) \<and>
       (\<forall>e. r = Exception e \<longrightarrow> e \<noteq> default
          \<longrightarrow> ?Q (Exception e) u)"
    proof (intro conjI allI impI)
      fix v
      assume "r = Result v"
      have insert:
        "vListInsertEnd' lp p \<bullet> u
         \<lbrace>\<lambda>r' t.
           r' = Result () \<and>
           raw_xlist_rel (hrs_mem (t_hrs_' t)) lp
             (list_insert_end_abs p
               (raw_key_at (hrs_mem (t_hrs_' u)) p) ?ys)
         \<rbrace>"
        by (rule raw_vListInsertEnd_general_refines_via_transformer[
              OF rel_u fresh can_increment])
      show "vListInsertEnd' lp p \<bullet> u \<lbrace>?Q\<rbrace>"
        apply (rule runs_to_weaken[OF insert])
        using key_u by auto
    next
      fix e
      assume "r = Exception e"
      then show
        "e \<noteq> default \<longrightarrow> ?Q (Exception e) u"
        using post by simp
    qed
  qed

  show ?thesis
    unfolding raw_remove_then_insert_end'_def
    by (rule runs_to_bind[OF bind_pre])
qed
```

This is the proposition exposed by `runs_to_bind_iff`. The first conjunct uses
the insert refinement and rewrites its intermediate raw key with `key_u`; the
second contradicts `r = Result ()`.

## Minimal checker order once execution is authorized

1. Check the freshness lemma alone.
2. Check the count-headroom lemma alone.
3. Check the three pure key-preservation bricks through
   `raw_remove_concrete_heap_preserves_removed_key`.
4. Check the source key projection and strengthened remove theorem.
5. Only then add the `runs_to_bind` theorem.

No new C VCG should be needed. If a proof attempt starts unfolding
`vListRemove'_def` or `vListInsertEnd'_def`, it has crossed the intended
abstraction boundary.


The theory closes with:

```isabelle
end
```
