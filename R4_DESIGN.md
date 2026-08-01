# R4 design: singleton `vListRemove` staircase

Status: `DESIGN_ONLY_NOT_CHECKER_GREEN`

This is the proposed raw-heap rung after the R3 empty-to-singleton
`vListInsertEnd'` theorem.  It uses only the unmodified V6.1.1 source, the
checker-generated raw `vListRemove'_def`, and the blind R0--R3 artifacts.  No
original formalization was consulted.  The Isabelle snippets below are target
statements and proof skeletons; this design pass did not run Isabelle.

The acceptance path is deliberately narrow:

```text
canonical empty list
  -- vListInsertEnd(raw_item_ptr) --> canonical singleton
  -- vListRemove(raw_item_ptr)    --> canonical empty list
```

R4 does not yet claim arbitrary-ring removal.  The singleton is the smallest
path that exercises both reverse-link writes, the cursor-repair branch, the
container clear, and the count decrement.

## 1. Exact generated source order

The raw `vListRemove'_def` performs the following actions, in this order:

1. guard `c_guard(item.next)`;
2. guard `c_guard(item)`;
3. write `item.next->previous := item.previous`;
4. guard `c_guard(item.previous)`;
5. write `item.previous->next := item.next`;
6. read `list := PTR_COERCE(unit -> xLIST_C) item.container`;
7. guard `c_guard(list)`;
8. if `list.index = item`, write `list.index := item.previous`;
9. write `item.container := NULL`;
10. write `list.count := list.count - 1`.

Two details are load-bearing.

- The two unlink writes in the generated raw term are already direct
  field-lvalue `heap_update`s.  They are not whole-`xLIST_ITEM_C` updates.
- The source first uses `pvContainer_C` to recover the owning list and later
  explicitly clears it to `NULL`.  It does not clear the removed item's
  `pxNext_C`, `pxPrevious_C`, key, or owner.

For the fixed singleton witness, all source operands reduce as follows:

| Source expression | Singleton value | Target address |
|---|---|---:|
| `item.next` | cast sentinel | - |
| `item.next->previous` | sentinel previous | `0x1010 ..+ 4` |
| `item.previous` | cast sentinel | - |
| `item.previous->next` | sentinel next | `0x100C ..+ 4` |
| `list.index` | item | `0x1004 ..+ 4` |
| `item.container` | coerced list | `0x2010 ..+ 4` |
| `list.count` | `1` | `0x1000 ..+ 4` |

After normalizing the three later root-record updates, remove therefore has
exactly five four-byte writes, in this order:

```text
0x1010  sentinel.previous := sentinel
0x100C  sentinel.next     := sentinel
0x1004  list.index        := sentinel
0x2010  item.container    := NULL
0x1000  list.count        := 0
```

There are no writes to the item's key (`0x2000`), next (`0x2004`), previous
(`0x2008`), or owner (`0x200C`).  The sentinel trailing region remains
`0x1014 ..+ 8`.

## 2. Freeze the R3/R4 interface

R3 should export one structural singleton predicate.  Keeping the predicate at
the memory level makes the R4 locality bricks independent of the globals
record:

```isabelle
definition raw_singleton_heap_fields :: "heap_mem \<Rightarrow> bool" where
  "raw_singleton_heap_fields h \<longleftrightarrow>
     uxNumberOfItems_C (h_val h raw_list_ptr) = 1 \<and>
     pxIndex_C (h_val h raw_list_ptr) = raw_item_ptr \<and>
     xMINI_LIST_ITEM_C.xItemValue_C
       (xListEnd_C (h_val h raw_list_ptr)) = 0xFFFFFFFF \<and>
     xMINI_LIST_ITEM_C.pxNext_C
       (xListEnd_C (h_val h raw_list_ptr)) = raw_item_ptr \<and>
     xMINI_LIST_ITEM_C.pxPrevious_C
       (xListEnd_C (h_val h raw_list_ptr)) = raw_item_ptr \<and>
     xLIST_ITEM_C.pxNext_C (h_val h raw_item_ptr) =
       raw_sentinel_ptr raw_list_ptr \<and>
     xLIST_ITEM_C.pxPrevious_C (h_val h raw_item_ptr) =
       raw_sentinel_ptr raw_list_ptr \<and>
     pvContainer_C (h_val h raw_item_ptr) =
       PTR_COERCE(xLIST_C \<rightarrow> unit) raw_list_ptr"

definition raw_singleton_fields :: "globals \<Rightarrow> bool" where
  "raw_singleton_fields s \<longleftrightarrow>
     raw_singleton_heap_fields (hrs_mem (t_hrs_' s))"
```

The key and owner are intentionally not fixed by this predicate.  R4 frames
their values from the prestate.  The fixed addresses and R0 guards imply that
the real item, list, and cast sentinel are distinct and guarded; no full
sentinel allocation premise is added.

Likewise freeze the canonical empty interface once, rather than repeating the
five R1 equations in every theorem:

```isabelle
definition raw_empty_heap_fields :: "heap_mem \<Rightarrow> bool" where
  "raw_empty_heap_fields h \<longleftrightarrow>
     uxNumberOfItems_C (h_val h raw_list_ptr) = 0 \<and>
     pxIndex_C (h_val h raw_list_ptr) =
       raw_sentinel_ptr raw_list_ptr \<and>
     xMINI_LIST_ITEM_C.xItemValue_C
       (xListEnd_C (h_val h raw_list_ptr)) = 0xFFFFFFFF \<and>
     xMINI_LIST_ITEM_C.pxNext_C
       (xListEnd_C (h_val h raw_list_ptr)) =
       raw_sentinel_ptr raw_list_ptr \<and>
     xMINI_LIST_ITEM_C.pxPrevious_C
       (xListEnd_C (h_val h raw_list_ptr)) =
       raw_sentinel_ptr raw_list_ptr"
```

If R3 freezes equivalent names first, R4 should import those names instead of
duplicating these definitions.

### Direct singleton witness for smoke tests

The acceptance theorem must consume the R3 singleton post.  A separately
encoded singleton is still useful for fast evaluation and for isolating R4
from a red R3 VCG:

```isabelle
definition raw_singleton_list_value :: xLIST_C where
  "raw_singleton_list_value =
     uxNumberOfItems_C_update (\<lambda>_. 1)
      (pxIndex_C_update (\<lambda>_. raw_item_ptr)
       (xListEnd_C_update
         (\<lambda>e.
           xMINI_LIST_ITEM_C.pxNext_C_update (\<lambda>_. raw_item_ptr)
            (xMINI_LIST_ITEM_C.pxPrevious_C_update
              (\<lambda>_. raw_item_ptr) e))
         raw_empty_list_value))"

definition raw_linked_item_value ::
  "32 word \<Rightarrow> unit ptr \<Rightarrow> xLIST_ITEM_C"
where
  "raw_linked_item_value k owner =
     pvContainer_C_update
       (\<lambda>_. PTR_COERCE(xLIST_C \<rightarrow> unit) raw_list_ptr)
       (raw_fresh_item_value k owner)"
```

Encoding these two disjoint values over an arbitrary base heap gives a direct
non-vacuous R4 prestate.  It is a smoke witness, not a substitute for composing
R3 and R4.

## 3. First locality bricks

R4 should begin with pointer reduction and read-after-write, before invoking
the generated monad.

### R4.1 Resolve the two unlink targets

```isabelle
lemma raw_remove_successor_previous_field_at_singleton:
  assumes "raw_singleton_heap_fields h"
  shows
   "PTR(xLIST_ITEM_C ptr)
      &(xLIST_ITEM_C.pxNext_C (h_val h raw_item_ptr)
          \<rightarrow>[''pxPrevious_C'']) =
    (Ptr 0x1010 :: xLIST_ITEM_C ptr ptr)"
  using assms
  unfolding raw_singleton_heap_fields_def
  by (simp add: field_lvalue_def xLIST_ITEM_C_pxPrevious_C_fl)

lemma raw_remove_predecessor_next_field_at_singleton:
  assumes "raw_singleton_heap_fields h"
  shows
   "PTR(xLIST_ITEM_C ptr)
      &(xLIST_ITEM_C.pxPrevious_C (h_val h raw_item_ptr)
          \<rightarrow>[''pxNext_C'']) =
    (Ptr 0x100C :: xLIST_ITEM_C ptr ptr)"
  using assms
  unfolding raw_singleton_heap_fields_def
  by (simp add: field_lvalue_def xLIST_ITEM_C_pxNext_C_fl)
```

For the second statement as used by the program, the heap is already after the
first unlink write.  Thus first prove that the `0x1010` write frames the whole
real item at `0x2000`, then instantiate this lemma on that heap.

### R4.2 One generic disjoint-read helper

Reuse or land the following byte-locality lemma once:

```isabelle
lemma raw_h_val_after_disjoint_update:
  assumes
    "{ptr_val p..+size_of TYPE('a)} \<inter>
     {ptr_val q..+size_of TYPE('b)} = {}"
  shows
    "h_val (heap_update p (v :: 'a::mem_type) h)
       (q :: 'b::mem_type ptr) = h_val h q"
```

Its proof is `h_val_def` plus `heap_list_update_disjoint_same`, exactly as in
R2.  Instantiate it only on fixed four-byte fields.  In particular export:

```text
sentinel.previous write frames the whole real item
sentinel.next write frames the whole real item
both sentinel-link writes frame list.count and list.index
sentinel.previous write frames sentinel.next and sentinel.key
sentinel.next write frames sentinel.previous and sentinel.key
list.index write frames both sentinel links and list.count
item.container write frames all list fields and item key/next/previous/owner
list.count write frames list.index, both sentinel links, and the whole item
```

The arbitrary-heap R3 common-prefix facts remain the bridge from the cast
sentinel selectors to the embedded mini item:

```text
raw_sentinel_item_value_prefix
raw_sentinel_next_prefix
raw_sentinel_previous_prefix
```

They are used to observe the poststate, not to justify a 20-byte sentinel
allocation.

### R4.3 Normalize only the three root-record updates

The generated unlink writes need no normalizer.  The later updates do:

| Generated update | Conversion fact | Direct address |
|---|---|---:|
| list `pxIndex_C_update` | `xLIST_C_heap_update_fields(2)` | `0x1004` |
| item `pvContainer_C_update` | `xLIST_ITEM_C_heap_update_fields(5)` | `0x2010` |
| list `uxNumberOfItems_C_update` | `xLIST_C_heap_update_fields(1)` | `0x1000` |

Give each conversion a directed wrapper, using the R0 guard and the symmetric
orientation of the generated theorem.  Do not unfold record codecs:

```isabelle
lemma raw_list_index_update_to_field:
  "heap_update raw_list_ptr
      (pxIndex_C_update (\<lambda>_. q) (h_val h raw_list_ptr)) h =
   heap_update
      (PTR(xLIST_ITEM_C ptr)
        &(raw_list_ptr\<rightarrow>[''pxIndex_C''])) q h"

lemma raw_item_container_update_to_field:
  "heap_update raw_item_ptr
      (pvContainer_C_update (\<lambda>_. q) (h_val h raw_item_ptr)) h =
   heap_update
      (PTR(unit ptr)
        &(raw_item_ptr\<rightarrow>[''pvContainer_C''])) q h"

lemma raw_list_count_update_to_field:
  "heap_update raw_list_ptr
      (uxNumberOfItems_C_update (\<lambda>_. q)
        (h_val h raw_list_ptr)) h =
   heap_update
      (PTR(32 word)
        &(raw_list_ptr\<rightarrow>[''uxNumberOfItems_C''])) q h"
```

Before adopting the last two pretty-printed pointer types, the implementation
theory should `print_statement` the indexed generated facts and use their exact
types.

## 4. The three source-order obligations

Name the heaps after the two direct unlink writes:

```text
h0 = prestate memory
h1 = write 0x1010 sentinel.previous := sentinel to h0
h2 = write 0x100C sentinel.next     := sentinel to h1
```

Then prove three small packages.

### Cursor repair

```isabelle
lemma raw_remove_singleton_cursor_branch:
  assumes "raw_singleton_heap_fields h0"
    and "h1 = heap_update
          (Ptr 0x1010 :: xLIST_ITEM_C ptr ptr)
          (raw_sentinel_ptr raw_list_ptr) h0"
    and "h2 = heap_update
          (Ptr 0x100C :: xLIST_ITEM_C ptr ptr)
          (raw_sentinel_ptr raw_list_ptr) h1"
  shows
    "pxIndex_C (h_val h2 raw_list_ptr) = raw_item_ptr \<and>
     xLIST_ITEM_C.pxPrevious_C (h_val h2 raw_item_ptr) =
       raw_sentinel_ptr raw_list_ptr"
```

This makes the generated condition take its true branch and makes the assigned
value exactly the sentinel.  For a singleton this is the concrete counterpart
of

```text
predecessor raw_item_ptr [raw_item_ptr] = None.
```

The false cursor branch is intentionally deferred to general-ring R5.

### Owning-list recovery and container clear

```isabelle
lemma raw_remove_singleton_container_read:
  assumes "raw_singleton_heap_fields h0"
    and h1_h2: "...the two unlink writes above..."
  shows
    "PTR_COERCE(unit \<rightarrow> xLIST_C)
       (pvContainer_C (h_val h2 raw_item_ptr)) = raw_list_ptr"
```

The proof uses the whole-item frame across the two list-field writes and the
pointer-coercion simp rule.  This fact discharges the generated list guard.

The exact source post is:

```text
item.container = NULL
item.next      = sentinel       (unchanged, not cleared)
item.previous  = sentinel       (unchanged, not cleared)
item.key       = old item.key   (unchanged)
item.owner     = old item.owner (unchanged)
```

Do not state that a removed item is byte-zeroed, self-linked, or has null
next/previous pointers.  Those are false source claims.

### Count decrement

Prove that the first four writes frame count and that count is still one just
before the final update.  Then close the fixed-width arithmetic separately:

```isabelle
lemma raw_remove_count_one_to_zero:
  "((1 :: 32 word) - 1) = 0"
  by simp
```

Membership/count consistency is a real precondition.  Raw guards alone allow
a state with count zero and valid links/container; the generated subtraction
would wrap to `0xFFFFFFFF`.  No general remove theorem may omit the positive
count or representation premise.

## 5. Exact five-write normal form

Define the post-memory independently of the monad:

```isabelle
definition raw_remove_singleton_nf :: "heap_mem \<Rightarrow> heap_mem" where
  "raw_remove_singleton_nf h =
     heap_update (Ptr 0x1000 :: 32 word ptr) 0
      (heap_update (Ptr 0x2010 :: unit ptr ptr) NULL
       (heap_update (Ptr 0x1004 :: xLIST_ITEM_C ptr ptr)
         (raw_sentinel_ptr raw_list_ptr)
        (heap_update (Ptr 0x100C :: xLIST_ITEM_C ptr ptr)
          (raw_sentinel_ptr raw_list_ptr)
         (heap_update (Ptr 0x1010 :: xLIST_ITEM_C ptr ptr)
           (raw_sentinel_ptr raw_list_ptr) h))))"
```

First prove pure projections of this definition:

```isabelle
lemma raw_remove_singleton_nf_fields:
  assumes "raw_singleton_heap_fields h"
  shows
    "raw_empty_heap_fields (raw_remove_singleton_nf h) \<and>
     xLIST_ITEM_C.xItemValue_C
       (h_val (raw_remove_singleton_nf h) raw_item_ptr) =
       xLIST_ITEM_C.xItemValue_C (h_val h raw_item_ptr) \<and>
     xLIST_ITEM_C.pxNext_C
       (h_val (raw_remove_singleton_nf h) raw_item_ptr) =
       raw_sentinel_ptr raw_list_ptr \<and>
     xLIST_ITEM_C.pxPrevious_C
       (h_val (raw_remove_singleton_nf h) raw_item_ptr) =
       raw_sentinel_ptr raw_list_ptr \<and>
     pvOwner_C (h_val (raw_remove_singleton_nf h) raw_item_ptr) =
       pvOwner_C (h_val h raw_item_ptr) \<and>
     pvContainer_C
       (h_val (raw_remove_singleton_nf h) raw_item_ptr) = NULL"
```

Only after this ledger is green should the generated monad be opened once:

```isabelle
theorem raw_vListRemove_singleton_normal_form:
  assumes "raw_singleton_fields s"
  shows
  "vListRemove' raw_item_ptr \<bullet> s
   \<lbrace>\<lambda>r t.
      r = Result () \<and>
      hrs_mem (t_hrs_' t) =
        raw_remove_singleton_nf (hrs_mem (t_hrs_' s)) \<and>
      hrs_htd (t_hrs_' t) = hrs_htd (t_hrs_' s)
    \<rbrace>"
```

Suggested proof architecture:

1. unfold only `vListRemove'_def`, `raw_singleton_fields_def`, and the normal
   form at the final equality;
2. run `runs_to_vcg` once;
3. resolve the two target pointers with R4.1;
4. use R4.2 to retain item operands, index, container, and count after each
   preceding write;
5. force the true cursor branch with the cursor lemma;
6. normalize index, container, and count with the three generated field facts;
7. finish `1 - 1` separately.

Derive the public exact-post theorem from the normal form without a second VCG:

```isabelle
corollary raw_vListRemove_singleton_exact_post:
  assumes "raw_singleton_fields s"
  shows
  "vListRemove' raw_item_ptr \<bullet> s
   \<lbrace>\<lambda>r t.
      r = Result () \<and>
      raw_empty_heap_fields (hrs_mem (t_hrs_' t)) \<and>
      xLIST_ITEM_C.xItemValue_C
        (h_val (hrs_mem (t_hrs_' t)) raw_item_ptr) =
        xLIST_ITEM_C.xItemValue_C
          (h_val (hrs_mem (t_hrs_' s)) raw_item_ptr) \<and>
      xLIST_ITEM_C.pxNext_C
        (h_val (hrs_mem (t_hrs_' t)) raw_item_ptr) =
        raw_sentinel_ptr raw_list_ptr \<and>
      xLIST_ITEM_C.pxPrevious_C
        (h_val (hrs_mem (t_hrs_' t)) raw_item_ptr) =
        raw_sentinel_ptr raw_list_ptr \<and>
      pvOwner_C (h_val (hrs_mem (t_hrs_' t)) raw_item_ptr) =
        pvOwner_C (h_val (hrs_mem (t_hrs_' s)) raw_item_ptr) \<and>
      pvContainer_C
        (h_val (hrs_mem (t_hrs_' t)) raw_item_ptr) = NULL \<and>
      heap_list (hrs_mem (t_hrs_' t)) 8 raw_sentinel_tail_addr =
        heap_list (hrs_mem (t_hrs_' s)) 8 raw_sentinel_tail_addr \<and>
      hrs_mem (t_hrs_' t) raw_canary_addr =
        hrs_mem (t_hrs_' s) raw_canary_addr \<and>
      hrs_htd (t_hrs_' t) = hrs_htd (t_hrs_' s)
    \<rbrace>"
```

## 6. Trailing-eight and external frames

Record the byte ledger explicitly:

```isabelle
definition raw_remove_write_bytes :: "addr set" where
  "raw_remove_write_bytes =
     {(0x1010 :: addr)..+4} \<union>
     {(0x100C :: addr)..+4} \<union>
     {(0x1004 :: addr)..+4} \<union>
     {(0x2010 :: addr)..+4} \<union>
     {(0x1000 :: addr)..+4}"

lemma raw_remove_write_bytes_tail_disjoint:
  "raw_remove_write_bytes \<inter>
    {raw_sentinel_tail_addr..+8} = {}"

lemma raw_remove_singleton_nf_tail8:
  "heap_list (raw_remove_singleton_nf h) 8 raw_sentinel_tail_addr =
   heap_list h 8 raw_sentinel_tail_addr"

lemma raw_remove_singleton_nf_canary:
  "raw_remove_singleton_nf h raw_canary_addr = h raw_canary_addr"
```

These lemmas quantify over arbitrary heaps.  The tail bytes need not be typed
or allocated.  R4's first two writes are already four-byte field writes, so
the proof does not use a fictional full sentinel object.  The R3 whole-update
tail lemmas remain necessary for insert, but remove should not be rewritten
into a whole-item update merely to reuse them.

## 7. Empty-to-singleton-to-empty composite

Define the raw needle using the four checked/generated operations:

```isabelle
definition raw_list_insert_remove_needle where
  "raw_list_insert_remove_needle = do {
     vListInitialise' raw_list_ptr;
     vListInitialiseItem' raw_item_ptr;
     vListInsertEnd' raw_list_ptr raw_item_ptr;
     vListRemove' raw_item_ptr
   }"
```

Compose existing runs-to theorems; do not symbolically execute all four bodies
again.  The composite post should say:

```text
list fields                 = canonical empty fields
item.container              = NULL
item.next, item.previous    = sentinel
item.key, item.owner        = their initial values
sentinel trailing 8 bytes   = initial bytes
external canary 0x3000      = initial byte
hrs_htd                     = initial descriptor
```

To obtain the composite tail frame, add the small missing per-operation frames
rather than a second monolithic VCG:

1. `vListInitialise'` writes exactly the 20-byte list region ending at
   `0x1014`;
2. `vListInitialiseItem'` writes the disjoint item region;
3. R3 supplies the insert trailing-eight frame;
4. R4 supplies the remove trailing-eight frame.

On the direct value witness where the pre-list is already canonical empty and
the pre-item already has sentinel links and a null container, the final typed
list and item values equal the initial values.  This byte/value round trip is
a witness-specific corollary, not the general API specification.

## 8. Abstract remove simulation boundary

For the checked pure model, the singleton calculation is exact:

```isabelle
lemma list_insert_remove_singleton_view:
  assumes "ring xs = []" "cursor xs = None"
  shows
    "ring (list_remove_abs x (list_insert_end_abs x k xs)) = [] \<and>
     cursor (list_remove_abs x (list_insert_end_abs x k xs)) = None \<and>
     item_key (list_remove_abs x (list_insert_end_abs x k xs)) x = k"
  using assms
  unfolding list_insert_end_abs_def list_remove_abs_def
  by simp

lemma list_insert_remove_singleton_identity:
  assumes "ring xs = []" "cursor xs = None" "item_key xs x = k"
  shows "list_remove_abs x (list_insert_end_abs x k xs) = xs"
```

The key premise in the second theorem is essential.  `list_remove_abs` removes
membership and repairs the cursor but deliberately leaves the total
`item_key` map unchanged; the C source likewise leaves the detached item's key
unchanged.  Without `item_key xs x = k`, the composite restores the empty
membership/cursor view but is not necessarily record-equal to `xs`.

Once the raw representation relation exists, R4 supports only the following
singleton simulation:

```isabelle
raw_rep s xs
raw_singleton_fields s
ring xs = [raw_item_id]
cursor xs = Some raw_item_id
------------------------------------------------------------
vListRemove' raw_item_ptr transforms s to some t such that
raw_rep t (list_remove_abs raw_item_id xs)
```

This still requires the representation bridge to state that:

- the sentinel encodes `None`;
- `raw_item_ptr` encodes `raw_item_id`;
- concrete count equals `length (ring xs)`;
- concrete index agrees with `cursor xs`;
- real/sentinel next and previous links implement the singleton ring;
- the item's container names this list before remove and is null afterwards;
- concrete item key agrees with `item_key xs raw_item_id`.

The R4 field theorem alone is not a source-to-abstract refinement theorem.

General-ring removal is a later rung.  It additionally needs a checked bridge
from concrete `item.previous` to `predecessor x (ring xs)`, both cursor
branches, mutual-link preservation for arbitrary neighbors, ownership and
separation for all nodes, and count/length consistency.  The singleton proof
must not be advertised as covering those obligations.

## 9. Adversarial checks and build order

Before the master VCG, retain these source-shaped counterchecks:

- count `0` with otherwise valid singleton pointers makes the raw subtraction
  wrap; guards do not imply count consistency;
- a wrong but guarded `pvContainer_C` makes remove update the wrong list;
- remove leaves stale next/previous links in a detached item;
- when index is not the removed item, source leaves index unchanged;
- no R4 statement may assume a typed 20-byte object at the 12-byte sentinel.

Recommended checker staircase:

1. two unlink-target pointer reductions;
2. direct-field interval/address facts and the generic disjoint-read helper;
3. unlink operand/item frames;
4. cursor branch, container recovery, and count-before-decrement;
5. three generated root-to-field normalizers;
6. `raw_remove_singleton_nf` field/tail/canary lemmas;
7. one `vListRemove'` normal-form VCG;
8. exact-post corollary;
9. composition with R3; and only then
10. the singleton `raw_rep`/`list_remove_abs` simulation.

Suitable direct evaluation targets are the two field addresses, the five-write
normal form on a zero/base heap, and the concrete direct singleton witness.
Arbitrary-heap locality, tail preservation, `runs_to`, and representation
simulation remain symbolic proof obligations.
