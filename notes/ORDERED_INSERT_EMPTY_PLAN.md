# Stock ordered `vListInsert`: empty-list refinement plan

Status: static source/theory/session-artifact inspection only. No Isabelle
command was run. No existing theory, `theories/ROOT`, or build script was
edited, and no original formalization was consulted.

## 1. Static availability verdict

The raw-skip translation does contain a usable generated `vListInsert'`
constant.

Evidence:

- `theories/list_raw_skip/List_V611_Raw_Skip_Translation.thy` installs the
  untouched stock `list.c` and runs `autocorres [skip_heap_abs, ...]` over the
  whole file. `vListInsert` is neither in `no_body` nor excluded by a function
  scope.
- Run `20260731Tlist-raw-skip-01` completed
  `EAL6_FreeRTOS_V611_List_Raw_Skip` successfully.
- A read-only string scan of the resulting Poly/ML session heap contains the
  fully qualified constant
  `List_V611_Raw_Skip_Translation.vListInsert'`, as well as
  `raw.vListInsert'_def`, `l1_vListInsert'_def`,
  `l2_vListInsert'_def`, and the generated correspondence facts.
- `PROOF_PORT_LEDGER.md` records the checker-reported public type

  ```isabelle
  vListInsert' ::
    xLIST_C ptr \<Rightarrow> xLIST_ITEM_C ptr \<Rightarrow>
    (unit, unit, lifted_globals) spec_monad
  ```

The old `20260731Tlist-smoke-11-signatures` “undefined fact” belongs to the
different non-raw-skip smoke theory and does not contradict the raw-skip heap.

What is not yet statically exported is the readable top-level
`vListInsert'_def` body: the raw-skip theory prints four other list functions
but omits this one. The constant's availability is confirmed; the exact
`whileLoop`/branch term shape still deserves a one-line child probe before
writing the VCG proof.

## 2. A necessary representation repair

The desired theorem cannot be true from only

```isabelle
raw_xlist_rel h lp xs
ring xs = []
raw_fresh_for_insert lp (ring xs) p
```

for an arbitrary non-maximum item key.

`raw_xlist_rel` constrains count, cursor, links, live item payloads, and spatial
layout, but it does **not** constrain the embedded sentinel's item value.
Consequently it admits an empty self-loop whose sentinel key is, for example,
`0`. If the fresh item's key is `1`, the non-special C branch starts at the
sentinel and tests `sentinel_next_key <= 1`. That is true; the next pointer is
the sentinel again, so the loop repeats forever. A total `runs_to` theorem
cannot follow.

The source initializer does establish the missing fact. Name it explicitly:

```isabelle
definition raw_sentinel_max ::
  "heap_mem \<Rightarrow> xLIST_C ptr \<Rightarrow> bool"
where
  "raw_sentinel_max h lp \<longleftrightarrow>
     raw_key_at h (raw_end_item lp) = (max_word :: 32 word)"
```

The generic common-prefix lemma
`raw_sentinel_item_value_prefix_generic` connects this full-item observation
to the real embedded `xMINI_LIST_ITEM_C.xItemValue_C` field written by
`vListInitialise`.

There are therefore two exact source interfaces:

- item key `= max_word`: the C special branch bypasses the loop, so no
  sentinel-key premise is needed;
- arbitrary item key: require `raw_sentinel_max`. This covers both the special
  branch and every non-maximum key.

Do not silently add the sentinel fact to `raw_xlist_rel` in this rung: that
would replay every existing relation proof. Carry it as a layered ordered-list
invariant, then consider a later representation migration.

## 3. Empty relation facts and `cursor = None`

The first pure brick should expose all facts needed by both source branches:

```isabelle
lemma raw_xlist_rel_empty_facts:
  assumes rel: "raw_xlist_rel h lp xs"
    and empty: "ring xs = []"
  shows
    "cursor xs = None \<and>
     uxNumberOfItems_C (h_val h lp) = 0 \<and>
     pxIndex_C (h_val h lp) = raw_end_item lp \<and>
     raw_next_at h lp (raw_end_item lp) = raw_end_item lp \<and>
     raw_prev_at h lp (raw_end_item lp) = raw_end_item lp"
```

Proof outline:

1. obtain `xlist_wf xs` and the raw count/link facts from `rel`;
2. `ring xs = []` makes any `Some c` cursor impossible, hence
   `cursor xs = None`;
3. `raw_xlist_rel_countD` plus `unat w = 0` gives the concrete count word
   `0`;
4. use `raw_xlist_rel_index_eq_cursor_node` to obtain
   `pxIndex = raw_end_item lp`;
5. simplify `raw_ring_links h lp []`, or use
   `raw_ring_links_empty_iff`, for the two sentinel self-links.

This is load-bearing for the refinement: stock ordered insert never writes
`pxIndex`. The concrete cursor therefore stays at the sentinel, and
`list_insert_ordered_abs` leaves the abstract cursor at `None`. The existing
`raw_xlist_rel_singletonI` is not reusable because it describes the
insert-end singleton with `cursor = Some p` and `pxIndex = p`.

The corresponding pure abstract fields are:

```isabelle
lemma list_insert_ordered_empty_fields:
  assumes empty: "ring xs = []"
  shows
    "ring (list_insert_ordered_abs p k xs) = [p] \<and>
     cursor (list_insert_ordered_abs p k xs) = cursor xs \<and>
     item_key (list_insert_ordered_abs p k xs) p = k"
  using empty
  by (simp add: list_insert_ordered_abs_def)
```

## 4. Branch normalization

Let

```isabelle
?h = hrs_mem (t_hrs_' s)
?e = raw_end_item lp
?k = raw_key_at ?h p
```

### 4.1 `portMAX_DELAY` special branch

For `?k = max_word`, source executes
`pxIterator = pxList->xListEnd.pxPrevious` and does not enter the loop.
The empty-link fact gives:

```isabelle
lemma raw_ordered_empty_special_iterator:
  assumes rel: "raw_xlist_rel h lp xs"
    and empty: "ring xs = []"
  shows
    "xMINI_LIST_ITEM_C.pxPrevious_C (xListEnd_C (h_val h lp)) =
     raw_end_item lp"
```

The generated literal `0xFFFFFFFF :: 32 word` should normalize to
`max_word` by `simp`; freeze a one-line helper only if the printed definition
does not normalize automatically.

### 4.2 Non-maximum, zero-iteration branch

For `?k \<noteq> max_word`, source initializes `pxIterator = ?e`. The loop
guard is false on its first test:

```isabelle
lemma raw_ordered_empty_loop_guard_false:
  assumes rel: "raw_xlist_rel h lp xs"
    and empty: "ring xs = []"
    and sentinel: "raw_sentinel_max h lp"
    and nonmax: "raw_key_at h p \<noteq> (max_word :: 32 word)"
  shows
    "\<not>
      (raw_key_at h (raw_next_at h lp (raw_end_item lp))
        \<le> raw_key_at h p)"
```

Reason: empty links make `next(end) = end`, the sentinel premise changes the
left side to `max_word`, and `max_word <= k` implies `k = max_word`.

The source-shaped corollary should be supplied after the signature probe:

```isabelle
lemma raw_ordered_empty_source_loop_guard_false:
  assumes rel: "raw_xlist_rel h lp xs"
    and empty: "ring xs = []"
    and sentinel: "raw_sentinel_max h lp"
    and nonmax: "raw_key_at h p \<noteq> (max_word :: 32 word)"
  shows
    "\<not>
      (xLIST_ITEM_C.xItemValue_C
         (h_val h
           (xLIST_ITEM_C.pxNext_C
             (h_val h (raw_end_item lp))))
       \<le> xLIST_ITEM_C.xItemValue_C (h_val h p))"
```

Use `raw_full_next_is_sentinel_safe`,
`raw_sentinel_item_value_prefix_generic`, and `raw_key_at_def`. Keep this
source-shaped fact local rather than teaching the global simplifier about
embedded-sentinel aliasing.

Both branches therefore exit the search phase with the same iterator `?e`.

## 5. Exact six-write heap transformer

After the read/branch/search phase, the stock C writes in this exact order:

1. `p->pxNext = e`;
2. `p->pxNext->pxPrevious = p`, hence `e->pxPrevious = p`;
3. `p->pxPrevious = e`;
4. `e->pxNext = p`;
5. `p->pvContainer = lp`;
6. `lp->uxNumberOfItems = 1`, by incrementing the represented empty count.

There is no `pxIndex` write.

Reuse the field-precise insert-end primitives:

```isabelle
definition raw_ordered_insert_empty_heap ::
  "heap_mem \<Rightarrow> xLIST_C ptr \<Rightarrow> raw_node_id \<Rightarrow> heap_mem"
where
  "raw_ordered_insert_empty_heap h lp p =
     (let e = raw_end_item lp;
          h1 = raw_insert_next_heap h p e;
          h2 = raw_insert_previous_heap h1 e p;
          h3 = raw_insert_previous_heap h2 p e;
          h4 = raw_insert_next_heap h3 e p;
          h5 = raw_insert_container_heap h4 lp p
      in raw_insert_count_heap h5 lp)"
```

The second stage must use the heap after stage 1: it represents the C lvalue
`p->pxNext->pxPrevious`. Prove `p.next = e` immediately after `h1` before
folding it to the explicit `e` target.

The exact observable effect should be:

```isabelle
definition raw_ordered_empty_effect ::
  "heap_mem \<Rightarrow> heap_mem \<Rightarrow> xLIST_C ptr \<Rightarrow>
   raw_node_id \<Rightarrow> bool"
where
  "raw_ordered_empty_effect h h' lp p \<longleftrightarrow>
     uxNumberOfItems_C (h_val h' lp) = 1 \<and>
     pxIndex_C (h_val h' lp) = raw_end_item lp \<and>
     raw_ring_links h' lp [p] \<and>
     raw_key_at h' p = raw_key_at h p \<and>
     pvContainer_C (h_val h' p) =
       PTR_COERCE(xLIST_C \<rightarrow> unit) lp \<and>
     raw_key_at h' (raw_end_item lp) =
       raw_key_at h (raw_end_item lp)"
```

The final sentinel-key frame is not required by `raw_xlist_rel`, but it is
required to compose another ordered insertion later.

Recommended pure projection theorem:

```isabelle
lemma raw_ordered_insert_empty_transformer_effect:
  assumes rel: "raw_xlist_rel h lp xs"
    and empty: "ring xs = []"
    and fresh: "raw_fresh_for_insert lp (ring xs) p"
  shows
    "raw_ordered_empty_effect h
       (raw_ordered_insert_empty_heap h lp p) lp p"
```

Prove it as separate selector bricks before assembling:

- count becomes `1` and index remains `e`;
- `p.next = e` and `p.prev = e`;
- `e.next = p` and `e.prev = p`;
- `p` key is unchanged and container becomes `lp`;
- sentinel key is unchanged.

Use `raw_ring_links_singleton_iff` for topology. Do not use a whole
`xLIST_ITEM_C` allocation assumption for the embedded sentinel.

## 6. Source heap-effect theorems

The source VCG should be split at the proof-relevant C branch.

```isabelle
theorem raw_vListInsert_ordered_empty_max_heap_effect:
  assumes rel:
    "raw_xlist_rel (hrs_mem (t_hrs_' s)) lp xs"
    and empty: "ring xs = []"
    and fresh: "raw_fresh_for_insert lp (ring xs) p"
    and key_max:
      "raw_key_at (hrs_mem (t_hrs_' s)) p =
       (max_word :: 32 word)"
  shows
    "vListInsert' lp p \<bullet> s
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       hrs_mem (t_hrs_' t) =
         raw_ordered_insert_empty_heap
           (hrs_mem (t_hrs_' s)) lp p
     \<rbrace>"
```

This branch needs no `raw_sentinel_max` assumption.

```isabelle
theorem raw_vListInsert_ordered_empty_nonmax_heap_effect:
  assumes rel:
    "raw_xlist_rel (hrs_mem (t_hrs_' s)) lp xs"
    and empty: "ring xs = []"
    and fresh: "raw_fresh_for_insert lp (ring xs) p"
    and sentinel:
      "raw_sentinel_max (hrs_mem (t_hrs_' s)) lp"
    and key_nonmax:
      "raw_key_at (hrs_mem (t_hrs_' s)) p \<noteq>
       (max_word :: 32 word)"
  shows
    "vListInsert' lp p \<bullet> s
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       hrs_mem (t_hrs_' t) =
         raw_ordered_insert_empty_heap
           (hrs_mem (t_hrs_' s)) lp p
     \<rbrace>"
```

Here the loop is proved to take exactly zero iterations; do not invent a
general loop invariant.

The arbitrary-key source certificate is only a case split:

```isabelle
theorem raw_vListInsert_ordered_empty_heap_effect:
  assumes rel:
    "raw_xlist_rel (hrs_mem (t_hrs_' s)) lp xs"
    and empty: "ring xs = []"
    and fresh: "raw_fresh_for_insert lp (ring xs) p"
    and sentinel:
      "raw_sentinel_max (hrs_mem (t_hrs_' s)) lp"
  shows
    "vListInsert' lp p \<bullet> s
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       hrs_mem (t_hrs_' t) =
         raw_ordered_insert_empty_heap
           (hrs_mem (t_hrs_' s)) lp p
     \<rbrace>"
  using raw_vListInsert_ordered_empty_max_heap_effect
    raw_vListInsert_ordered_empty_nonmax_heap_effect
  by (cases
      "raw_key_at (hrs_mem (t_hrs_' s)) p =
       (max_word :: 32 word)") auto
```

The final proof line is a skeleton; after the signature probe, prefer an
explicit two-case Isar proof if `auto` does not instantiate the state and
premises immediately.

## 7. Relation transfer

Use a new ordered-empty assembler because the existing singleton constructor
has the wrong cursor:

```isabelle
lemma raw_xlist_rel_ordered_empty_insertI:
  assumes rel: "raw_xlist_rel h lp xs"
    and empty: "ring xs = []"
    and fresh: "raw_fresh_for_insert lp (ring xs) p"
    and count: "uxNumberOfItems_C (h_val h' lp) = 1"
    and index: "pxIndex_C (h_val h' lp) = raw_end_item lp"
    and links: "raw_ring_links h' lp [p]"
    and key: "raw_key_at h' p = k"
    and container:
      "pvContainer_C (h_val h' p) =
       PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
  shows
    "raw_xlist_rel h' lp (list_insert_ordered_abs p k xs)"
```

Proof ledger:

1. derive `cursor xs = None` from the empty relation;
2. use `list_insert_ordered_empty_fields`, so the target ring is `[p]` and
   target cursor is still `None`;
3. extend the old empty layout with
   `raw_xlist_layout_extend_set[OF old_layout fresh]`;
4. use `list_insert_ordered_preserves_wf`;
5. count is `unat 1 = length [p]`;
6. `index = end` gives `raw_cursor_at h' lp = None`;
7. discharge topology and the only live-item payload with `links`, `key`,
   and `container`.

Then:

```isabelle
lemma raw_ordered_empty_effect_refines:
  assumes rel: "raw_xlist_rel h lp xs"
    and empty: "ring xs = []"
    and fresh: "raw_fresh_for_insert lp (ring xs) p"
    and effect: "raw_ordered_empty_effect h h' lp p"
  shows
    "raw_xlist_rel h' lp
       (list_insert_ordered_abs p (raw_key_at h p) xs)"
```

This is a direct invocation of
`raw_xlist_rel_ordered_empty_insertI` after unfolding the effect.

## 8. Public arbitrary-key refinement theorem

The exact public target, with the necessary sentinel invariant made visible,
is:

```isabelle
theorem raw_vListInsert_ordered_empty_refines:
  assumes rel:
    "raw_xlist_rel (hrs_mem (t_hrs_' s)) lp xs"
    and empty: "ring xs = []"
    and fresh: "raw_fresh_for_insert lp (ring xs) p"
    and sentinel:
      "raw_sentinel_max (hrs_mem (t_hrs_' s)) lp"
  shows
    "vListInsert' lp p \<bullet> s
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       raw_xlist_rel (hrs_mem (t_hrs_' t)) lp
         (list_insert_ordered_abs p
           (raw_key_at (hrs_mem (t_hrs_' s)) p) xs) \<and>
       raw_sentinel_max (hrs_mem (t_hrs_' t)) lp
     \<rbrace>"
```

Proof:

1. take `raw_vListInsert_ordered_empty_heap_effect`;
2. take `raw_ordered_insert_empty_transformer_effect`;
3. project `raw_ordered_empty_effect_refines`;
4. use the effect's sentinel-key frame and the initial `sentinel` premise;
5. finish by `runs_to_weaken`. Do not reopen `vListInsert'_def`.

Also export the useful special-case corollary without the sentinel premise:

```isabelle
theorem raw_vListInsert_ordered_empty_max_refines:
  assumes rel:
    "raw_xlist_rel (hrs_mem (t_hrs_' s)) lp xs"
    and empty: "ring xs = []"
    and fresh: "raw_fresh_for_insert lp (ring xs) p"
    and key_max:
      "raw_key_at (hrs_mem (t_hrs_' s)) p =
       (max_word :: 32 word)"
  shows
    "vListInsert' lp p \<bullet> s
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       raw_xlist_rel (hrs_mem (t_hrs_' t)) lp
         (list_insert_ordered_abs p
           (max_word :: 32 word) xs)
     \<rbrace>"
```

No `raw_count_can_increment` premise is needed: the represented input ring is
empty, so the concrete count is `0` and the sole increment yields `1` without
wrap.

## 9. Ordered-role relation for later nonempty work

For delayed lists, the better long-term layer is:

```isabelle
definition raw_ordered_xlist_rel where
  "raw_ordered_xlist_rel h lp xs \<longleftrightarrow>
     raw_xlist_rel h lp xs \<and>
     raw_sentinel_max h lp \<and>
     sorted (map (item_key xs) (ring xs))"
```

The empty initialized list satisfies this predicate; the public theorem above
plus `list_insert_ordered_is_sorted` gives its empty-to-singleton
preservation. This avoids polluting FIFO ready-list relations with an ordered
role invariant and gives the future general-N loop proof exactly the sortedness
and sentinel facts it needs.

For positive `vTaskDelay`, the scheduler proof must additionally establish that
the generic item removed from the ready list is fresh for the selected empty
delayed-list object and that the preceding key write has set
`raw_key_at h p = xTimeToWake`. The ordered-empty theorem then covers both
no-wrap/current-delayed and wrap/overflow-delayed choices, including
`xTimeToWake = portMAX_DELAY`.

## 10. Minimal probe and checker staircase

Do not edit the stable raw-skip theory merely to inspect the definition.
When execution is authorized, create a disposable child theory importing
`EAL6_FreeRTOS_V611_List_Raw_Skip` with:

```isabelle
term "vListInsert'"
print_statement vListInsert'_def
print_statement raw.vListInsert'_def
```

Build only that child with `quick_and_dirty=false`, one worker, and a 60--120 s
timeout. Record the printed top-level branch and `whileLoop` shape. If the
top-level `_def` alias is not printable, the already confirmed
`raw.vListInsert'_def` is the fallback inspection point.

Use two proof-bearing leaves:

```isabelle
theory List_V611_Raw_R6_Ordered_Insert_Empty_Source
  imports
    "EAL6_FreeRTOS_V611_List_Raw_R6_Insert_Source_Effects.List_V611_Raw_R6_Insert_Source_Effects"
begin
```

This first leaf owns `raw_sentinel_max`, empty facts, the transformer, and the
branch-specific/unified source heap certificates. Once green, a second leaf
imports it together with the existing post-transformer session:

```isabelle
theory List_V611_Raw_R6_Ordered_Insert_Empty_Refinement
  imports
    "EAL6_FreeRTOS_V611_List_Raw_R6_Ordered_Insert_Empty_Source.List_V611_Raw_R6_Ordered_Insert_Empty_Source"
    "EAL6_FreeRTOS_V611_List_Raw_R6_Insert_Post_Transformer.List_V611_Raw_R6_Insert_Post_Transformer"
begin
```

That leaf owns transformer projections, the ordered-empty relation assembler,
and the public refinement theorem. No ROOT edit is part of this design-only
task.

Use this checker order:

1. pure empty facts, sentinel predicate, and false initial loop guard;
2. maximum-key source heap theorem -- this is the next smallest
   proof-bearing rung because it contains no loop;
3. non-maximum zero-iteration source heap theorem;
4. unified arbitrary-key exact heap theorem;
5. transformer selector projections and effect;
6. relation assembler;
7. public refinement theorem.

If step 3 produces a general loop invariant goal, stop and inspect the printed
definition/VCG goal: the empty guard should reduce before induction. Do not
start a monolithic general-N ordered-insert proof from this rung.
