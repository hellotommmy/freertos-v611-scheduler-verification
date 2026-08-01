# R5 design: raw heap to `xlist_abs` relation

Status: `DESIGN_ONLY_NOT_CHECKER_GREEN`

This note defines the first machine-checkable representation relation between
the `skip_heap_abs` byte heap and the independently reconstructed
`('id, 'key) xlist_abs` model.  It uses only the unmodified V6.1.1 source, the
blind pure model, and the current raw R0--R3 evidence.  No original
formalization was consulted, no Isabelle build was run for this design, and no
existing theory was changed.

The first refinement target is deliberately the checked fixed-address path:

```text
raw canonical empty at 0x1000
  -- vListInsertEnd' 0x1000 0x2000 --> raw singleton

raw_empty_abs keys
  -- list_insert_end_abs raw_item_ptr k -->
     raw_singleton_abs raw_item_ptr keys k
```

The representation is factored so this first witness does not prematurely
claim arbitrary-list allocation, scheduler ownership, or a full typed object
at the cast sentinel.

## 1. Node identity choice

Use the actual typed list-item pointer as the abstract node identifier:

```isabelle
type_synonym raw_node_id = "xLIST_ITEM_C ptr"
type_synonym raw_key = "32 word"
```

Thus the instantiated pure state is
`(raw_node_id, raw_key) xlist_abs`.

This choice is both the minimum bridge and the least lossy one.

- `ring` can record concrete source order without an injection table.
- `cursor = Some p` means exactly the concrete item pointer `p`.
- the cast sentinel has the same pointer type, so its exclusion is an explicit
  invariant rather than a hidden datatype assumption.
- a later scheduler relation can map role-specific item pointers to task IDs.

Do not use `pvOwner_C` or a TCB pointer as the node ID.  One TCB contains at
least a generic item and an event item; collapsing them to their common owner
would make two distinct list memberships the same abstract node.  Do not use a
bare `addr` unless a later multi-language bridge needs it: it discards the C
type that the current generated facts already preserve.

For a list pointer `lp`, write

```isabelle
definition raw_end_item :: "xLIST_C ptr \<Rightarrow> raw_node_id" where
  "raw_end_item lp = raw_sentinel_ptr lp"
```

and require

```text
raw_end_item lp notin set (ring xs).
```

The sentinel denotes abstract `None`; it is never a real node in `ring`.

## 2. Prefix-safe concrete accessors

The concrete sentinel is a 12-byte `xMINI_LIST_ITEM_C` embedded at list offset
8, but the C source casts its address to `xLIST_ITEM_C *`.  Define relation
accessors that use the mini view at the sentinel and the full item view only at
real nodes:

```isabelle
definition raw_next_at ::
  "heap_mem \<Rightarrow> xLIST_C ptr \<Rightarrow> raw_node_id \<Rightarrow>
   raw_node_id"
where
  "raw_next_at h lp p =
     (if p = raw_end_item lp then
        xMINI_LIST_ITEM_C.pxNext_C
          (xListEnd_C (h_val h lp))
      else xLIST_ITEM_C.pxNext_C (h_val h p))"

definition raw_prev_at ::
  "heap_mem \<Rightarrow> xLIST_C ptr \<Rightarrow> raw_node_id \<Rightarrow>
   raw_node_id"
where
  "raw_prev_at h lp p =
     (if p = raw_end_item lp then
        xMINI_LIST_ITEM_C.pxPrevious_C
          (xListEnd_C (h_val h lp))
      else xLIST_ITEM_C.pxPrevious_C (h_val h p))"

definition raw_key_at :: "heap_mem \<Rightarrow> raw_node_id \<Rightarrow> raw_key"
where
  "raw_key_at h p = xLIST_ITEM_C.xItemValue_C (h_val h p)"

definition raw_cursor_at ::
  "heap_mem \<Rightarrow> xLIST_C ptr \<Rightarrow> raw_node_id option"
where
  "raw_cursor_at h lp =
     (let p = pxIndex_C (h_val h lp)
      in if p = raw_end_item lp then None else Some p)"
```

The checked R3a facts

```text
raw_sentinel_item_value_prefix
raw_sentinel_next_prefix
raw_sentinel_previous_prefix
```

connect raw C reads through the cast pointer to these prefix-safe accessors.
No definition above decodes a full sentinel item.

For general `N`, the fixed `raw_list_ptr` facts must be replaced by the
following arbitrary-`lp` interface.  First name the genuine embedded mini
pointer and the two exact four-byte field regions:

```isabelle
definition raw_end_mini :: "xLIST_C ptr \<Rightarrow> xMINI_LIST_ITEM_C ptr" where
  "raw_end_mini lp =
     PTR(xMINI_LIST_ITEM_C) &(lp\<rightarrow>[''xListEnd_C''])"

definition raw_sentinel_next_field_region ::
  "xLIST_C ptr \<Rightarrow> addr set"
where
  "raw_sentinel_next_field_region lp =
     {ptr_val (PTR(xLIST_ITEM_C ptr)
       &(raw_end_item lp\<rightarrow>[''pxNext_C'']))
      ..+size_of TYPE(raw_node_id)}"

definition raw_sentinel_previous_field_region ::
  "xLIST_C ptr \<Rightarrow> addr set"
where
  "raw_sentinel_previous_field_region lp =
     {ptr_val (PTR(xLIST_ITEM_C ptr)
       &(raw_end_item lp\<rightarrow>[''pxPrevious_C'']))
      ..+size_of TYPE(raw_node_id)}"
```

The prefix/read targets are genuinely quantified over `lp`; the two guard
premises are explicit rather than discharged by the fixed addresses:

```isabelle
lemma raw_sentinel_item_value_prefix_general:
  assumes "c_guard lp" and "c_guard (raw_end_item lp)"
  shows
    "xLIST_ITEM_C.xItemValue_C (h_val h (raw_end_item lp)) =
     xMINI_LIST_ITEM_C.xItemValue_C (xListEnd_C (h_val h lp))"

lemma raw_sentinel_next_prefix_general:
  assumes "c_guard lp" and "c_guard (raw_end_item lp)"
  shows
    "xLIST_ITEM_C.pxNext_C (h_val h (raw_end_item lp)) =
     xMINI_LIST_ITEM_C.pxNext_C (xListEnd_C (h_val h lp))"

lemma raw_sentinel_previous_prefix_general:
  assumes "c_guard lp" and "c_guard (raw_end_item lp)"
  shows
    "xLIST_ITEM_C.pxPrevious_C (h_val h (raw_end_item lp)) =
     xMINI_LIST_ITEM_C.pxPrevious_C (xListEnd_C (h_val h lp))"

lemma raw_end_mini_value_general:
  assumes "c_guard lp"
  shows "h_val h (raw_end_mini lp) = xListEnd_C (h_val h lp)"
```

Next expose both generated update views.  The following are theorem targets,
not claims that the fixed R3b theorems can simply be generalized by
metis.  Give analogous proofs for `pxPrevious_C`.

```isabelle
lemma raw_sentinel_whole_next_update_to_field_general:
  assumes "c_guard (raw_end_item lp)"
  shows
    "heap_update (raw_end_item lp)
       (xLIST_ITEM_C.pxNext_C_update (\<lambda>_. q)
         (h_val h (raw_end_item lp))) h =
     heap_update
       (PTR(xLIST_ITEM_C ptr)
         &(raw_end_item lp\<rightarrow>[''pxNext_C''])) q h"

lemma raw_sentinel_whole_previous_update_to_field_general:
  assumes "c_guard (raw_end_item lp)"
  shows
    "heap_update (raw_end_item lp)
       (xLIST_ITEM_C.pxPrevious_C_update (\<lambda>_. q)
         (h_val h (raw_end_item lp))) h =
     heap_update
       (PTR(xLIST_ITEM_C ptr)
         &(raw_end_item lp\<rightarrow>[''pxPrevious_C''])) q h"

lemma raw_sentinel_whole_next_update_to_list_general:
  assumes "c_guard lp" and "c_guard (raw_end_item lp)"
  shows
    "heap_update (raw_end_item lp)
       (xLIST_ITEM_C.pxNext_C_update (\<lambda>_. q)
         (h_val h (raw_end_item lp))) h =
     heap_update lp
       (xListEnd_C_update
         (\<lambda>_. xMINI_LIST_ITEM_C.pxNext_C_update (\<lambda>_. q)
           (h_val h (raw_end_mini lp)))
         (h_val h lp)) h"

lemma raw_sentinel_whole_previous_update_to_list_general:
  assumes "c_guard lp" and "c_guard (raw_end_item lp)"
  shows
    "heap_update (raw_end_item lp)
       (xLIST_ITEM_C.pxPrevious_C_update (\<lambda>_. q)
         (h_val h (raw_end_item lp))) h =
     heap_update lp
       (xListEnd_C_update
         (\<lambda>_. xMINI_LIST_ITEM_C.pxPrevious_C_update (\<lambda>_. q)
           (h_val h (raw_end_mini lp)))
         (h_val h lp)) h"
```

Finally formulate locality against only the field actually written.  This is
the reusable arbitrary-region form from which `heap_list`, `h_val`, canary,
and tail observations can be framed:

```isabelle
lemma raw_sentinel_whole_next_update_locality_general:
  assumes guard: "c_guard (raw_end_item lp)"
      and disjoint: "A \<inter> raw_sentinel_next_field_region lp = {}"
  shows
    "\<forall>a \<in> A.
       heap_update (raw_end_item lp)
         (xLIST_ITEM_C.pxNext_C_update (\<lambda>_. q)
           (h_val h (raw_end_item lp))) h a = h a"

lemma raw_sentinel_whole_previous_update_locality_general:
  assumes guard: "c_guard (raw_end_item lp)"
      and disjoint: "A \<inter> raw_sentinel_previous_field_region lp = {}"
  shows
    "\<forall>a \<in> A.
       heap_update (raw_end_item lp)
         (xLIST_ITEM_C.pxPrevious_C_update (\<lambda>_. q)
           (h_val h (raw_end_item lp))) h a = h a"
```

These locality targets deliberately do not demand separation from a fictitious
20-byte sentinel object.  Only the concrete four-byte target field is excluded;
all other framing premises are supplied by the observation being preserved.

## 3. Encode one finite cycle by edge pairs

For `e = raw_end_item lp` and `rs = ring xs`, use one list of directed cycle
edges:

```isabelle
definition raw_edge_pairs ::
  "xLIST_C ptr \<Rightarrow> raw_node_id list \<Rightarrow>
   (raw_node_id \<times> raw_node_id) list"
where
  "raw_edge_pairs lp rs = zip (raw_end_item lp # rs) (rs @ [raw_end_item lp])"

definition raw_ring_links ::
  "heap_mem \<Rightarrow> xLIST_C ptr \<Rightarrow> raw_node_id list \<Rightarrow> bool"
where
  "raw_ring_links h lp rs \<longleftrightarrow>
     list_all
       (\<lambda>(p,q). raw_next_at h lp p = q \<and> raw_prev_at h lp q = p)
       (raw_edge_pairs lp rs)"
```

This single definition handles all alias cases.

```text
rs = []       edges = [(e,e)]
rs = [x]      edges = [(e,x),(x,e)]
rs = [x,y]    edges = [(e,x),(x,y),(y,e)]
```

Consequently the empty case demands both sentinel self-links, while the
singleton demands exactly the four checked R3f links.  It does not assume that
predecessor, successor, sentinel, and inserted node are pairwise distinct.

## 4. Address layout, semantic view, and the minimal relation

### 4.1 Address-only layout

Keep guards and object separation independent of heap contents:

```isabelle
definition raw_list_region :: "xLIST_C ptr \<Rightarrow> addr set" where
  "raw_list_region lp = {ptr_val lp..+size_of TYPE(xLIST_C)}"

definition raw_item_region :: "raw_node_id \<Rightarrow> addr set" where
  "raw_item_region p = {ptr_val p..+size_of TYPE(xLIST_ITEM_C)}"

definition raw_xlist_layout ::
  "xLIST_C ptr \<Rightarrow> raw_node_id list \<Rightarrow> bool"
where
  "raw_xlist_layout lp rs \<longleftrightarrow>
     c_guard lp \<and>
     c_guard (raw_end_item lp) \<and>
     raw_end_item lp \<notin> set rs \<and>
     (\<forall>p \<in> set rs.
        c_guard p \<and>
        raw_item_region p \<inter> raw_list_region lp = {}) \<and>
     (\<forall>p \<in> set rs. \<forall>q \<in> set rs.
        p \<noteq> q \<longrightarrow> raw_item_region p \<inter> raw_item_region q = {})"
```

Pointer inequality alone is insufficient: two aligned 20-byte roots at
addresses four bytes apart are distinct but overlap.  The sentinel is excluded
as a real root; its permitted mini-prefix alias is already inside the list
region.

### 4.2 Semantic view

```isabelle
definition raw_xlist_view ::
  "heap_mem \<Rightarrow> xLIST_C ptr \<Rightarrow>
   (raw_node_id, raw_key) xlist_abs \<Rightarrow> bool"
where
  "raw_xlist_view h lp xs \<longleftrightarrow>
     xlist_wf xs \<and>
     unat (uxNumberOfItems_C (h_val h lp)) = length (ring xs) \<and>
     cursor xs = raw_cursor_at h lp \<and>
     raw_ring_links h lp (ring xs) \<and>
     (\<forall>p \<in> set (ring xs).
        item_key xs p = raw_key_at h p \<and>
        pvContainer_C (h_val h p) =
          PTR_COERCE(xLIST_C \<rightarrow> unit) lp)"
```

Using `unat count = length ring` is stronger and safer than only
`count = of_nat (length ring)`: it rules out an abstract length that was
silently reduced modulo `2^32`.

The minimum raw-heap relation is:

```isabelle
definition raw_xlist_rel ::
  "heap_mem \<Rightarrow> xLIST_C ptr \<Rightarrow>
   (raw_node_id, raw_key) xlist_abs \<Rightarrow> bool"
where
  "raw_xlist_rel h lp xs \<longleftrightarrow>
     raw_xlist_layout lp (ring xs) \<and> raw_xlist_view h lp xs"
```

This relation contains exactly what is needed by `xlist_abs` and the local
list operations: finite ordered membership, cursor, live keys, live
containers, guards, and non-overlap.  Finiteness comes from the finite list
`ring`; no separately quantified finite set is introduced.

### 4.3 Deliberate extensions, not hidden conjuncts

The sentinel's maximum key is needed by ordered insertion but not by
`xlist_abs` or `vListInsertEnd`:

```isabelle
definition raw_sentinel_header :: "heap_mem \<Rightarrow> xLIST_C ptr \<Rightarrow> bool"
where
  "raw_sentinel_header h lp \<longleftrightarrow>
     xMINI_LIST_ITEM_C.xItemValue_C
       (xListEnd_C (h_val h lp)) = 0xFFFFFFFF"
```

Define `raw_xlist_ordered_ready` as `raw_xlist_rel AND
raw_sentinel_header` when proving `vListInsert`.

`pvOwner_C` has no component in `xlist_abs`; retain it through an explicit
scheduler-facing map:

```isabelle
definition raw_owner_agrees ::
  "heap_mem \<Rightarrow> (raw_node_id \<Rightarrow> unit ptr) \<Rightarrow>
   (raw_node_id, raw_key) xlist_abs \<Rightarrow> bool"
where
  "raw_owner_agrees h owners xs \<longleftrightarrow>
     (\<forall>p \<in> set (ring xs). pvOwner_C (h_val h p) = owners p)"
```

The base relation requires that each member points to this list, but it cannot
soundly assert the converse over every address in the total byte heap.  For a
known allocated node universe `U`, add:

```isabelle
definition raw_container_closed ::
  "raw_node_id set \<Rightarrow> heap_mem \<Rightarrow> xLIST_C ptr \<Rightarrow>
   (raw_node_id, raw_key) xlist_abs \<Rightarrow> bool"
where
  "raw_container_closed U h lp xs \<longleftrightarrow>
     set (ring xs) \<subseteq> U \<and>
     (\<forall>p \<in> U.
       (pvContainer_C (h_val h p) =
          PTR_COERCE(xLIST_C \<rightarrow> unit) lp) =
       (p \<in> set (ring xs)))"
```

Without `U`, arbitrary unallocated bytes can decode to a coincidental
container pointer, so a global converse would be false or meaningless.

The total `item_key` function is constrained only on live ring nodes.  Thus an
empty heap view relates to many abstract key maps.  This is intentional:
`vListInitialise` does not rewrite old detached nodes.  If later proofs need a
functional abstraction over all allocated items, add a node-universe key
agreement predicate rather than strengthening the base relation silently.
The exact observable equality is:

```isabelle
definition raw_live_xlist_eq ::
  "(raw_node_id, raw_key) xlist_abs \<Rightarrow>
   (raw_node_id, raw_key) xlist_abs \<Rightarrow> bool"
where
  "raw_live_xlist_eq xs ys \<longleftrightarrow>
     ring xs = ring ys \<and>
     cursor xs = cursor ys \<and>
     (\<forall>p \<in> set (ring xs). item_key xs p = item_key ys p)"

lemma raw_xlist_rel_observable_deterministic:
  assumes xs: "raw_xlist_rel h lp xs"
      and ys: "raw_xlist_rel h lp ys"
  shows "raw_live_xlist_eq xs ys"
```

The proof target compares the two walks from the common sentinel.  Count
equality gives equal lengths; the exact walk/nth lemma below then gives equal
ordered rings, after which the cursor and live keys follow directly from the
two views.  Its walk argument depends on
`distinct (raw_end_item lp # ring xs)`, obtained only by combining
`xlist_wf xs` with sentinel exclusion from `raw_xlist_layout`.

Do not strengthen this lemma to `xs = ys`: choose any `p` outside the common
ring and change only `item_key xs p` to obtain an immediate counterexample.
Thus the relation is deterministic only on source-observable abstract fields,
not on the total record function.

## 5. `hrs_htd` and tail bytes are separate layers

Raw `skip_heap_abs` execution reads and writes `hrs_mem`; it does not consult
`hrs_htd`.  Define a safety envelope separately:

```isabelle
definition raw_xlist_allocated ::
  "heap_typ_desc \<Rightarrow> xLIST_C ptr \<Rightarrow>
   raw_node_id list \<Rightarrow> bool"
where
  "raw_xlist_allocated d lp rs \<longleftrightarrow>
     root_ptr_valid d lp \<and>
     (\<forall>p \<in> set rs. root_ptr_valid d p)"
```

The implementation must use the exact generated `valid_footprint` or
`root_ptr_valid` spelling available in the raw session.  There is deliberately
no allocation conjunct for `raw_end_item lp :: xLIST_ITEM_C ptr`.  Only the
list root, its embedded mini field, and real item roots are typed.

A full state envelope may then be defined as:

```text
raw_xlist_safe_state s lp xs =
  raw_xlist_rel (hrs_mem (t_hrs_' s)) lp xs AND
  raw_xlist_allocated (hrs_htd (t_hrs_' s)) lp (ring xs)
```

The concrete descriptor witness is

```text
ptr_retyp raw_item_ptr (ptr_retyp raw_list_ptr empty_htd)
```

with no `ptr_retyp` at `0x1008`.

The trailing eight total-heap bytes are an operation frame observation, not a
one-state representation invariant:

```isabelle
definition raw_tail8 :: "heap_mem \<Rightarrow> xLIST_C ptr \<Rightarrow> byte list"
where
  "raw_tail8 h lp = heap_list h 8 (ptr_val lp + 20)"

definition raw_tail8_frame ::
  "heap_mem \<Rightarrow> heap_mem \<Rightarrow> xLIST_C ptr \<Rightarrow> bool"
where
  "raw_tail8_frame h h' lp \<longleftrightarrow> raw_tail8 h' lp = raw_tail8 h lp"
```

For `raw_list_ptr`, the start is the checked
`raw_sentinel_tail_addr = 0x1014`.  The relation places no constraint on those
eight values.  R3b shows
that each dangerous whole-sentinel next/previous update preserves them.  The
checker-green `raw_vListInsertEnd_empty_master` now composes those facts into a
whole-operation tail8 frame for the fixed witness and also provides the
two-state `hrs_htd` frame.  Neither observation becomes a one-state conjunct
of `raw_xlist_rel`.

For a general address layout, a whole-operation tail frame additionally needs
the observed eight-byte region to be disjoint from every real object that the
operation legitimately updates.  An allocator could place another item
immediately after the 20-byte list object.  The fixed witness satisfies this
separation (`0x1014..0x101B` versus item `0x2000`); without it, retain only the
unconditional field-local fact that a cast-sentinel read/modify/write preserves
its non-target trailing bytes.

## 6. Expansion lemmas for empty and singleton

Define abstract witnesses without fixing irrelevant off-ring keys:

```isabelle
definition raw_empty_abs ::
  "(raw_node_id \<Rightarrow> raw_key) \<Rightarrow>
   (raw_node_id, raw_key) xlist_abs"
where
  "raw_empty_abs keys =
     \<lparr>ring = [], cursor = None, item_key = keys\<rparr>"

definition raw_singleton_abs ::
  "raw_node_id \<Rightarrow> (raw_node_id \<Rightarrow> raw_key) \<Rightarrow>
   raw_key \<Rightarrow>
   (raw_node_id, raw_key) xlist_abs"
where
  "raw_singleton_abs p keys k =
     list_insert_end_abs p k (raw_empty_abs keys)"
```

First check the pure expansion:

```isabelle
lemma raw_singleton_abs_fields[simp]:
  "ring (raw_singleton_abs p keys k) = [p] \<and>
   cursor (raw_singleton_abs p keys k) = Some p \<and>
   item_key (raw_singleton_abs p keys k) p = k"
  by (simp add: raw_singleton_abs_def raw_empty_abs_def
      list_insert_end_abs_def)
```

Then prove two relation introduction rules.  Their premises should be only the
source-level fields shown here plus address layout.

```text
raw_xlist_rel_emptyI
  count = 0
  index = sentinel
  sentinel.next = sentinel
  sentinel.previous = sentinel
  raw_xlist_layout lp []
  --------------------------------------------------
  raw_xlist_rel h lp (raw_empty_abs keys)

raw_xlist_rel_singletonI
  count = 1
  index = item
  sentinel.next = item
  sentinel.previous = item
  item.next = sentinel
  item.previous = sentinel
  item.key = k
  item.container = coerced lp
  raw_xlist_layout lp [item]
  --------------------------------------------------
  raw_xlist_rel h lp (raw_singleton_abs item keys k)
```

These rules unfold the `zip` cycle only for lengths zero and one.  They avoid
starting the general reachability proof before the fixed refinement needle is
green.

## 7. Concrete empty preimage and detached item

Let

```text
s0 = raw_insert_end_prestate base d h k owner
xs0 = raw_empty_abs keys
```

The checker-green `raw_insert_end_prestate_fields` supplies the five empty list
fields and the five detached-item fields.  Together with R0/R2 address facts it
should give, without symbolic execution:

```isabelle
lemma raw_insert_end_prestate_rep_empty:
  "raw_xlist_rel
     (hrs_mem (t_hrs_'
       (raw_insert_end_prestate base d h k owner)))
     raw_list_ptr (raw_empty_abs keys)"
```

The detached item is operation input, not an empty-ring member:

```isabelle
definition raw_detached_item ::
  "heap_mem \<Rightarrow> xLIST_C ptr \<Rightarrow> raw_node_id \<Rightarrow>
   raw_key \<Rightarrow> unit ptr \<Rightarrow> bool"
where
  "raw_detached_item h lp p k owner \<longleftrightarrow>
     c_guard p \<and>
     p \<noteq> raw_end_item lp \<and>
     raw_item_region p \<inter> raw_list_region lp = {} \<and>
     raw_key_at h p = k \<and>
     pvOwner_C (h_val h p) = owner \<and>
     pvContainer_C (h_val h p) = NULL"

lemma raw_insert_end_prestate_detached:
  "raw_detached_item
     (hrs_mem (t_hrs_'
       (raw_insert_end_prestate base d h k owner)))
     raw_list_ptr raw_item_ptr k owner"
```

The prestate also happens to give sentinel next/previous links in the detached
item, but those are not necessary in the general insert contract because the C
body overwrites both.

For allocation non-vacuity instantiate

```text
d0 = ptr_retyp raw_item_ptr (ptr_retyp raw_list_ptr empty_htd)
```

and prove the list and real-item root footprints separately.  The already
checked `raw_insert_end_prestate_htd` then identifies the state's descriptor
with `d0`.  The semantic relation theorem itself remains valid for arbitrary
`d`, which accurately reflects raw execution.

## 8. Current R3 evidence and the checker-green master

At this design point the following fixed-witness rungs are checker-green under
`quick_and_dirty=false`:

| Evidence | Relation contribution |
|---|---|
| `raw_insert_end_prestate_fields` | satisfiable empty relation and detached item |
| `raw_vListInsertEnd_empty_result` | positive normal execution |
| `raw_vListInsertEnd_empty_count_index` | singleton count and cursor |
| `raw_vListInsertEnd_empty_sentinel_links` | first/last sentinel edges |
| `raw_vListInsertEnd_empty_item_links` | real-node edges |
| `raw_vListInsertEnd_empty_container` | live membership container |
| `raw_vListInsertEnd_empty_key_owner` | live key and optional owner map; run `20260731Tlist-raw-r3g-03-key-owner`, exit zero in 23.763 s |
| R3a prefix facts | cast-to-mini observation bridge |
| R3b update/tail facts | local alias and trailing-byte safety |
| `raw_vListInsertEnd_empty_master` | mechanically conjoins count/index, four links, container, key/owner, tail8, canary, and `hrs_htd`; run `20260731Tlist-raw-r3-master-01`, exit zero, `quick_and_dirty=false` |

The heap-view singleton field gate is therefore complete.  The master also
closes the fixed-witness whole-operation tail8, canary, and `hrs_htd` frames.
Owner is useful for `raw_owner_agrees` but is not required by `raw_xlist_rel`.
Allocation remains a separate, descriptor-conditional gate.

The independently checked postconditions were bundled with the library theorem

```isabelle
runs_to_conj:
  "(f \<bullet> s \<lbrace>\<lambda>r t. P r t \<and> Q r t\<rbrace>) \<longleftrightarrow>
   ((f \<bullet> s \<lbrace>P\<rbrace>) \<and> (f \<bullet> s \<lbrace>Q\<rbrace>))"
```

rather than by re-running the seven-write VCG.  This composition has now been
checked as `raw_vListInsertEnd_empty_master`.  R5 should use that theorem
directly and weaken its postcondition to the singleton relation; it should not
create another VCG-shaped bundle.

## 9. Fixed empty-insert refinement staircase

The first source-to-model theorem should be built in this order.

### P0: pure operation equation

```isabelle
lemma raw_empty_insert_abs:
  "list_insert_end_abs raw_item_ptr k (raw_empty_abs keys) =
   raw_singleton_abs raw_item_ptr keys k"
  by (simp add: raw_singleton_abs_def)
```

### P1: preimage is satisfiable

Prove `raw_insert_end_prestate_rep_empty` and
`raw_insert_end_prestate_detached` for the explicit encoded state.  Also retain
`raw_vListInsertEnd_empty_result`; a conditional refinement theorem whose
representation premise has no witness is not accepted.

### P2: post fields imply singleton relation

Use `raw_xlist_rel_singletonI`.  Address layout is static:

- the R0 guards discharge list, item, and sentinel guards;
- `raw_list_item_intervals_disjoint` supplies list/item separation;
- the singleton is distinct and excludes the sentinel by fixed addresses; and
- the bundled R3 post supplies every heap-dependent relation field.

### P3: one relation-valued postcondition

```isabelle
theorem raw_vListInsertEnd_empty_refines:
  "vListInsertEnd' raw_list_ptr raw_item_ptr \<bullet>
     (raw_insert_end_prestate base d h k owner)
   \<lbrace>\<lambda>r t.
      r = Result () \<and>
      raw_xlist_rel (hrs_mem (t_hrs_' t)) raw_list_ptr
        (list_insert_end_abs raw_item_ptr k (raw_empty_abs keys))
    \<rbrace>"
```

The proof should be `runs_to_weaken[OF
raw_vListInsertEnd_empty_master]`, the singleton intro rule, and
`raw_empty_insert_abs`.  The master has already performed the `runs_to_conj`
composition.  R5 should not unfold `vListInsertEnd'_def` again.

This theorem is also the concrete singleton witness: it starts from the
constructor whose empty relation has been proved, guarantees a positive
`Result ()` run, and requires every result heap to represent
`raw_singleton_abs raw_item_ptr keys k`.  A separately encoded singleton heap may be kept as
a fast `simp`/evaluation smoke test, but it is not a replacement for this
reachable witness.

### P4: orthogonal strengthened corollaries

After P3, add separate postconditions rather than changing the relation:

```text
raw_owner_agrees post (owners(raw_item_ptr := owner)) singleton
raw_sentinel_header post raw_list_ptr
raw_tail8_frame pre_mem post_mem raw_list_ptr
hrs_htd post = hrs_htd pre
external canary unchanged
raw_xlist_allocated post_htd raw_list_ptr [raw_item_ptr]
```

The master now supplies the fixed-witness whole-operation tail8, canary, and
`hrs_htd` equalities, so those P4 corollaries need only postcondition weakening
and predicate repackaging.  `raw_sentinel_header` preservation and
`raw_xlist_allocated` still require their own premises or checked bridge; do not
silently infer allocation from an arbitrary descriptor `d`.

## 10. General `N`-node relation lemma graph

Do not generalize the raw VCG first.  Generalize the pure edge/sequence layer,
then expose only the source reads and writes needed by the program.

The general insert contract must add a fresh guarded real item, disjoint from
the list and all current real nodes, with
`new \<noteq> raw_end_item lp`, `new \<notin> set (ring xs)`, and `c_guard new`.
Require
`length (ring xs) < unat (max_word :: 32 word)` so the count increment cannot
wrap.  Its abstract key argument is exactly `raw_key_at h new`; the source may
overwrite the new item's links and container, but must frame its key and
owner.

Package those obligations without hiding any of them:

```isabelle
definition raw_fresh_for_insert ::
  "xLIST_C ptr \<Rightarrow> raw_node_id list \<Rightarrow> raw_node_id \<Rightarrow> bool"
where
  "raw_fresh_for_insert lp rs new \<longleftrightarrow>
     new \<noteq> raw_end_item lp \<and>
     new \<notin> set rs \<and>
     c_guard new \<and>
     raw_item_region new \<inter> raw_list_region lp = {} \<and>
     (\<forall>p \<in> set rs.
        raw_item_region new \<inter> raw_item_region p = {}) \<and>
     length rs < unat (max_word :: 32 word)"
```

The general theorem assumes both `raw_xlist_rel h lp xs` and
`raw_fresh_for_insert lp (ring xs) new`.  The former supplies the old layout;
the latter separately supplies `new \<noteq> e` (which does not follow from
`new \<notin> set (ring xs)`), guard, separation from the list and every old
real object, and the exact no-wrap bound.  Since the embedded sentinel lies
inside `raw_list_region lp`, the list/new disjointness also protects its real
prefix without postulating a separate 20-byte sentinel object.

```text
D0  raw accessors and raw_edge_pairs length/empty/singleton equations

W0  xlist_wf gives distinct ring and a valid abstract cursor
 + sentinel exclusion
 -> W1  distinct (raw_end_item lp # ring xs)

D0 + W1
 -> E0  exact nth source/target equations for every zipped edge
 -> E1  every cycle node occurs as exactly one edge source and target
 -> E2  raw_ring_links gives next/previous mutual inverse on e union ring
 -> E3  for n < Suc(length ring),
          (raw_next_at h lp ^^ n) e = (e # ring) ! n
 -> E4  step Suc(length ring) first returns to e, with no earlier return
          and no duplicate visit
 -> E5  the reachable real-node set is exactly set ring

W0 + raw_cursor_at definition
 -> C0  index=e iff cursor=None; index=p iff cursor=Some p

unat count = length ring
 -> C1  concrete count bound
 -> C2  membership implies nonzero count; fresh insert bound prevents wrap

live projection conjuncts
 -> K0  member key/container facts
 + raw_container_closed U
 -> K1  owning list is unique inside the chosen allocated universe U

U0  generic prefix reads for arbitrary lp (not only raw_list_ptr)
 -> U1  generic whole-sentinel next/previous update-to-field/list facts
 -> U2  generic field frames from symbolic region separation

L0  guards and pairwise byte-region separation
 + U2
 -> L1  h_val frames for writes to distinct real nodes or sentinel fields
 -> L2  exact frames for count/index/key/owner/container
 -> L3  hrs_htd and conditional external/tail frame composition

F0  raw_fresh_for_insert lp (ring xs) new
    (new!=e, nonmembership, guard, exact region separation, count non-wrap)
 + C0
 -> I0  cursor determines concrete predecessor pred
 + E0/E2
 -> I1  raw_ring_links determines succ and every generated dynamic guard
 -> I2  pure ring decomposition:
          cursor=None, split empty/nonempty alias cases;
          cursor=Some c, first derive c in set ring
 -> I3  alias-aware replacement of edge pred->succ by pred->new->succ
 -> I4  every untouched edge survives the exact C write set
 -> I5  resulting edge order equals ring(list_insert_end_abs new key xs)
 -> I6  count/index/live-key/container post equations
 -> I7  raw_xlist_layout extends with new
 -> I8  pack raw_xlist_rel and prove general insert-end simulation

R0  member x determines concrete next and previous edges
 -> R1  unlink writes preserve every untouched cycle edge
 -> R2a singleton alias: next=previous=e
 -> R2b two-real-node alias: next=previous=the other real node
 -> R3  concrete previous maps to predecessor x (ring xs)
 -> R4  cursor-equal and cursor-unequal branches
 -> R5  count decrement agrees with length (remove1 x ring)
 -> R6  removed container is NULL; remaining containers stay owned
 -> R7  pack raw_xlist_rel and prove general remove simulation
```

E0--E5 are not discharged by a vague reachability argument.  Their public
theorem targets should expose the exact visit index and the first return to the
sentinel.  Start by recording the dependency that makes the zipped edge list a
cycle rather than merely a bag of edge constraints:

```isabelle
lemma raw_cycle_nodes_distinct:
  assumes "raw_xlist_rel h lp xs"
  shows "distinct (raw_end_item lp # ring xs)"

lemma raw_cycle_walk_nth:
  assumes rel: "raw_xlist_rel h lp xs"
      and n: "n < Suc (length (ring xs))"
  shows
    "((raw_next_at h lp) ^^ n) (raw_end_item lp) =
     (raw_end_item lp # ring xs) ! n"

lemma raw_cycle_walk_closes:
  assumes "raw_xlist_rel h lp xs"
  shows
    "((raw_next_at h lp) ^^ Suc (length (ring xs)))
       (raw_end_item lp) = raw_end_item lp"

lemma raw_cycle_walk_first_return:
  assumes rel: "raw_xlist_rel h lp xs"
      and positive: "0 < n"
      and bounded: "n \<le> Suc (length (ring xs))"
  shows
    "(((raw_next_at h lp) ^^ n) (raw_end_item lp) =
       raw_end_item lp) =
     (n = Suc (length (ring xs)))"

lemma raw_cycle_walk_injective_before_return:
  assumes rel: "raw_xlist_rel h lp xs"
      and ij: "i < j"
      and j: "j < Suc (length (ring xs))"
  shows
    "((raw_next_at h lp) ^^ i) (raw_end_item lp) \<noteq>
     ((raw_next_at h lp) ^^ j) (raw_end_item lp)"

lemma raw_cycle_reachable_prefix:
  assumes "raw_xlist_rel h lp xs"
  shows
    "{p. \<exists>n < Suc (length (ring xs)).
          ((raw_next_at h lp) ^^ n) (raw_end_item lp) = p} =
     insert (raw_end_item lp) (set (ring xs))"

lemma raw_cycle_reachable_real:
  assumes "raw_xlist_rel h lp xs"
  shows
    "{p. \<exists>n. 0 < n \<and> n < Suc (length (ring xs)) \<and>
          ((raw_next_at h lp) ^^ n) (raw_end_item lp) = p} =
     set (ring xs)"
```

`raw_cycle_nodes_distinct` unfolds the relation only far enough to combine
`xlist_wf`'s `distinct (ring xs)` fact with the layout's sentinel exclusion.
That lemma is an explicit premise of the edge source/target uniqueness and
walk inductions.  `raw_cycle_walk_first_return` rules out every positive
sentinel return before the closing step; the injectivity lemma separately
rules out duplicate non-sentinel visits.  The two set equalities are then
corollaries of the indexed walk, not substitutes for it.

The existing R3a/R3b prefix and update facts are fixed at
`raw_list_ptr = 0x1000`.  They establish the concrete needle but cannot be
cited as arbitrary-`lp` theorems.  General `N` work must first replay their
layout argument symbolically under the general guards and region-separation
premises in U0--U2.

The critical general insert sequence lemma is not merely a set equality.  It
must show that replacing the two concrete edges

```text
pred -> succ
```

by

```text
pred -> new -> succ
```

produces exactly the ordered list in `list_insert_end_abs`: `new # ring` when
the cursor is `None`, and `insert_after c new ring` when it is `Some c`.
Set/cardinality facts alone lose the FIFO order.

For multiple scheduler lists, add a global node universe and pairwise list
separation after the single-list graph is green.  The scheduler layer then
relates role-specific item pointers and `pvOwner_C` values to task IDs; it does
not change the node identity used here.

## 11. Adversarial and non-vacuity gates

Before accepting the relation, preserve these checks.

- Requiring `root_ptr_valid` for the cast sentinel makes the intended stock
  layout impossible; only the list root and real items are typed.
- Omitting `raw_end_item lp \<notin> set ring` permits the sentinel to count as
  a real member while also representing `None`.
- For insertion, `new \<notin> set ring` still permits `new = raw_end_item lp`;
  sentinel inequality is a separate freshness conjunct.
- Distinct pointer values without byte-region separation permit overlapping
  real item roots.
- Count equality modulo `2^32` admits abstract rings longer than the concrete
  count; use `unat` equality.
- Forward links alone admit inconsistent reverse links.  Each zipped edge must
  constrain both `next p=q` and `previous q=p`.
- Cursor `None` does not imply an empty ring.  Ordered insertion can leave a
  nonempty list indexed at the sentinel.
- Live-node key agreement must not be silently generalized to every decoded
  address in the total heap.
- Two abstract records related to the same heap may disagree on off-ring key
  values; only `raw_live_xlist_eq`, not literal record equality, is determined.
- Container completeness without a finite allocated universe mistakes random
  bytes for list membership.
- Owner is not a node ID and is not part of `xlist_abs`.
- A tail-byte equality is a two-state frame, not permission to allocate a
  nonexistent full sentinel item.

Add two small rejection witnesses beside the positive witnesses:

```text
singleton with item.previous != sentinel  does not satisfy raw_xlist_rel
singleton with count = 0                 does not satisfy raw_xlist_rel
```

Finally prove both an empty preimage and a singleton postimage using the
concrete encoded state.  A preservation theorem with only abstract premises,
without these witnesses and the positive `Result ()` run, is not evidence of a
non-vacuous source-to-model refinement.
