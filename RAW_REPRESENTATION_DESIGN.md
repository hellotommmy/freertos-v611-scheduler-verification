# Raw-heap representation design for `xList`

Status: `DESIGN_ONLY_NOT_CHECKER_GREEN`

This note fixes the intended bridge from the `skip_heap_abs` AutoCorres state
to the checker-green pure `('id, 'key) xlist_abs` model.  It was derived from
the stock FreeRTOS V6.1.1 `list.c`, the generated raw final definitions, and
the generated C layout.  It does not use the sealed original formalization.
No theorem in this note is claimed as checked until it is moved, one brick at
a time, into a registered theory and built with `quick_and_dirty=false`.

The central rule is that three different notions must not be collapsed:

1. `c_guard p` says that `p` is aligned and its C-sized interval avoids null;
2. allocation/typing says that the relevant bytes have an object certificate
   in `hrs_htd`, with disjoint real-object regions; and
3. the abstraction relation says that the bytes in `hrs_mem` encode a
   particular ring, cursor, key map, count, and container relation.

In particular, `h_val` is a total decoder over the total byte heap.  The fact
that `h_val h p` produces a value does **not** imply that `p` denotes an
allocated object.

## 1. Concrete vocabulary and frozen layout

For an AutoCorres state `s`, use the following abbreviations in the bridge:

```text
mem s = hrs_mem (t_hrs_' s)
htd s = hrs_htd (t_hrs_' s)
listval s lp = h_val (mem s) lp
itemval s p  = h_val (mem s) p
```

For `lp :: xLIST_C ptr`, define two pointers at the same address:

```text
end_mini lp :: xMINI_LIST_ITEM_C ptr
  = &(lp->xListEnd_C)

end_item lp :: xLIST_ITEM_C ptr
  = PTR(xLIST_ITEM_C) &(lp->xListEnd_C)
```

The existing checked witness establishes `end_item (Ptr 0x1000) = Ptr
0x1008`.  The generated 32-bit layout to freeze as small layout lemmas is:

| Object/field | Offset | Size |
|---|---:|---:|
| `xLIST_C.uxNumberOfItems_C` | 0 | 4 |
| `xLIST_C.pxIndex_C` | 4 | 4 |
| `xLIST_C.xListEnd_C` | 8 | 12 |
| `xMINI_LIST_ITEM_C.xItemValue_C` | 0 | 4 |
| `xMINI_LIST_ITEM_C.pxNext_C` | 4 | 4 |
| `xMINI_LIST_ITEM_C.pxPrevious_C` | 8 | 4 |
| `xLIST_ITEM_C.xItemValue_C` | 0 | 4 |
| `xLIST_ITEM_C.pxNext_C` | 4 | 4 |
| `xLIST_ITEM_C.pxPrevious_C` | 8 | 4 |
| `xLIST_ITEM_C.pvOwner_C` | 12 | 4 |
| `xLIST_ITEM_C.pvContainer_C` | 16 | 4 |

Thus `size_of xLIST_C = 20`, `size_of xMINI_LIST_ITEM_C = 12`, and
`size_of xLIST_ITEM_C = 20`.  The sentinel's allocated prefix is exactly the
12 bytes `[lp+8, lp+20)`.  Treating `end_item lp` as a full item would instead
claim the 20-byte region `[lp+8, lp+28)`, eight bytes beyond the list object.
That full-item allocation claim is deliberately forbidden.

The representation should expose prefix accessors instead of repeatedly
projecting a fictitious full sentinel item:

```text
next_at s lp p =
  if p = end_item lp
  then xMINI_LIST_ITEM_C.pxNext_C (xListEnd_C (listval s lp))
  else xLIST_ITEM_C.pxNext_C (itemval s p)

prev_at s lp p =
  if p = end_item lp
  then xMINI_LIST_ITEM_C.pxPrevious_C (xListEnd_C (listval s lp))
  else xLIST_ITEM_C.pxPrevious_C (itemval s p)

key_at s lp p =
  if p = end_item lp
  then xMINI_LIST_ITEM_C.xItemValue_C (xListEnd_C (listval s lp))
  else xLIST_ITEM_C.xItemValue_C (itemval s p)
```

The generated raw definition of `vListInsertEnd'` nevertheless evaluates
`xLIST_ITEM_C.pxNext_C (h_val (mem s) (end_item lp))` when the cursor is the
sentinel.  The bridge therefore needs common-prefix read and update lemmas;
it must not add a false full-item allocation premise for the sentinel.

## 2. Three predicate layers

### 2.1 Pointer-guard layer

The proposed predicate `raw_xlist_guards lp xs` contains only:

```text
c_guard lp
c_guard (end_item lp)
for every p in set (ring xs): c_guard p
```

Operation-specific fresh pointers are added at the call site.  For example,
`vListInsertEnd'` also requires `c_guard new`.  The ring relation derives the
guards for the dynamic `pxIndex`, successor, and predecessor values that the
generated monad checks.

These facts are arithmetic facts about addresses.  They do not state that
any byte is allocated, readable, writable, correctly typed, or owned by this
list.  A concrete countermodel is `empty_htd` paired with the already checked
guarded addresses `0x1000`, `0x1008`, and `0x2000`.

### 2.2 Allocation and separation layer

Use `hrs_htd (t_hrs_' s)` as an allocation/type certificate even though the
raw generated functions do not consult it.  For a real object `p :: T ptr`,
the allocation atom should be the `valid_footprint` half of

```text
htd s, c_guard |-t p
```

whose definition is `valid_footprint ... AND c_guard p`.  Keeping the two
halves named separately makes it impossible to cite a guard as allocation.

For a list with real-node set `R`, `raw_xlist_allocated s lp R` requires:

- a valid `xLIST_C` footprint at `lp`;
- a valid `xLIST_ITEM_C` footprint at every `p in R`;
- pairwise-disjoint byte spans for the list root and all real item roots;
- no real item at `end_item lp`; and
- the generated nested-field typing needed for `end_mini lp`, derived from
  the valid list object and the `xListEnd_C` field layout.

Address-level disjointness is intentional.  Under the guards, it implies the
needed disjointness of `s_footprint`s without hiding modular wraparound in a
set-of-tags argument.  The one permitted alias is:

```text
bytes(end_mini lp) subset bytes(lp)
```

There is no allocation atom for `end_item lp :: xLIST_ITEM_C ptr`.  The raw
cast is justified by common-prefix lemmas, not by pretending that the
embedded `xMINI_LIST_ITEM_C` is a 20-byte root.

All three list operations considered here update only `hrs_mem`; the raw
definitions use `hrs_mem_update`, and `hrs_htd_mem_update` leaves `hrs_htd`
unchanged.  Allocation preservation should therefore be discharged once,
then reused as a frame fact.

### 2.3 Heap-shape and abstract-view layer

Let `R = ring xs` and `e = end_item lp`.  Define the mathematical cyclic
successor and predecessor functions over `e # R` as follows:

- on an empty ring, both successor and predecessor of `e` are `e`;
- on a nonempty ring, successor of `e` is `hd R` and predecessor of `e` is
  `last R`;
- a real node's successor is the next real node, or `e` at the tail; and
- a real node's predecessor is the preceding real node, or `e` at the head.

The proposed `raw_xlist_view s lp xs` requires:

1. `xlist_wf xs`, hence `distinct (ring xs)` and a cursor that is either the
   sentinel (`None`) or a member (`Some p`);
2. `uxNumberOfItems_C (listval s lp) = of_nat (length R)` and
   `length R < 2^32`;
3. `pxIndex_C (listval s lp)` equals `e` for `cursor xs = None`, and equals
   `p` for `cursor xs = Some p`;
4. `key_at s lp e = 0xFFFFFFFF`;
5. `next_at` and `prev_at` equal the cyclic successor and predecessor on every
   node in `{e} union set R`;
6. for every real member `p`,
   `pvContainer_C (itemval s p) = PTR_COERCE(xLIST_C -> unit) lp`; and
7. for every real member `p`, `item_key xs p = key_at s lp p`.

No condition is imposed on `pvOwner_C`; list operations preserve it.  No
condition is imposed on keys or containers of nonmembers.  In particular,
reinitialising a list does not rewrite the old nodes, and the empty abstract
view must not claim that it does.

The complete candidate relation is factored, not monolithic:

```text
raw_xlist_rep s lp xs =
  raw_xlist_guards lp xs AND
  raw_xlist_allocated s lp (set (ring xs)) AND
  raw_xlist_view s lp xs
```

Proofs should normally open exactly one conjunct.  This keeps failures in
address arithmetic, allocation, cyclic shape, and abstract observation
separate.

## 3. Common-prefix obligations

The raw final definitions expose four facts that must be proved directly from
the generated serializers and field layout.

### Prefix reads

For arbitrary byte heap `h`, the following projections must depend only on
the 12-byte common prefix:

```text
xLIST_ITEM_C.xItemValue_C (h_val h (end_item lp))
  = xMINI_LIST_ITEM_C.xItemValue_C (xListEnd_C (h_val h lp))

xLIST_ITEM_C.pxNext_C (h_val h (end_item lp))
  = xMINI_LIST_ITEM_C.pxNext_C (xListEnd_C (h_val h lp))

xLIST_ITEM_C.pxPrevious_C (h_val h (end_item lp))
  = xMINI_LIST_ITEM_C.pxPrevious_C (xListEnd_C (h_val h lp))
```

These should be unconditional byte-layout lemmas.  Requiring allocation here
would obscure the real issue: `h_val` reads a total heap and the projections
must be independent of the eight trailing bytes.

### Prefix updates

`vListInsertEnd'` updates `pxIndex->pxNext` with a whole-structure
`heap_update pxIndex (...)`.  When `pxIndex = end_item lp`, prove:

- the allocated list bytes see exactly the corresponding update of
  `xListEnd_C.pxNext_C`;
- every byte outside the four-byte sentinel-next field is unchanged; and
- in particular, the unallocated eight-byte tail `[lp+20, lp+28)` is written
  back byte-for-byte unchanged by the read-modify-write encoding.

The last fact is a frame property, not an allocation of the tail.  It is what
makes the raw total-heap encoding compatible with the source-level field
write.

The same field-locality lemma should be generic enough to recover precise
frames from full-structure updates to a real item or the list root.  A coarse
"outside the 20-byte object" frame is useful for early symbolic execution,
but it is not the final source-level frame for the sentinel cast.

## 4. Nonempty concrete witness

Use the following fixed addresses, already compatible with the checked guard
arithmetic:

```text
lp = Ptr 0x1000 :: xLIST_C ptr
e  = Ptr 0x1008 :: xLIST_ITEM_C ptr
i  = Ptr 0x2000 :: xLIST_ITEM_C ptr
```

Construct the type descriptor from disjoint roots, conceptually:

```text
d = ptr_retyp i (ptr_retyp lp empty_htd)
```

The list root and real item are typed; `end_mini lp` is the nested field of
the typed list root.  The full item type at `e` is not retyped.

For any key `k` and owner pointer `o`, encode this memory:

| Location | Field | Value |
|---|---|---|
| `lp+0` | count | `1` |
| `lp+4` | cursor | `i` |
| `lp+8` | sentinel key | `0xFFFFFFFF` |
| `lp+12` | sentinel next | `i` |
| `lp+16` | sentinel previous | `i` |
| `i+0` | item key | `k` |
| `i+4` | item next | `e` |
| `i+8` | item previous | `e` |
| `i+12` | item owner | `o` |
| `i+16` | item container | `PTR_COERCE lp` |

The eight total-heap bytes `[0x1014,0x101C)` are arbitrary and **not** in the
allocated list footprint.  Prefix-read independence ensures they do not
affect the sentinel key/next/previous observations.

This state represents:

```text
ring = [i]
cursor = Some i
item_key i = k
```

It is the desired nonempty witness, and it also gives an end-to-end needle:

1. an empty state at the same `lp` has count zero, cursor `e`, and sentinel
   self-links;
2. `vListInsertEnd' lp i` produces the singleton state above; and
3. `vListRemove' i` restores the empty ring, cursor `e`, count zero, and null
   item container while preserving `k`, `o`, the item's next/previous fields,
   the eight unallocated tail bytes, and the external frame.

This sequence is a proof target, not yet checked evidence.

## 5. Operation obligations and frames

Define a field footprint as the exact four-byte address range of the field,
not the enclosing structure's full 20-byte span.  Each operation has a
source-level write set and a generated-encoding proof obligation.

### 5.1 `vListInitialise`

Preconditions:

- `c_guard lp`;
- a valid allocated `xLIST_C` footprint at `lp`; and
- an arbitrary disjoint external frame.

No pre-existing list representation is necessary: this is an initializer.
The postcondition relates the result to any empty abstract state with
`ring = []` and `cursor = None`; its out-of-ring `item_key` values are
unobservable.

Exact write set:

```text
lp.{uxNumberOfItems, pxIndex,
    xListEnd.xItemValue, xListEnd.pxNext, xListEnd.pxPrevious}
```

This happens to cover all 20 list bytes in this no-padding layout.  The proof
must show:

- count is zero;
- cursor is `end_item lp`;
- the sentinel value is `0xFFFFFFFF`;
- sentinel next and previous are self-links;
- `hrs_htd` is unchanged; and
- every byte outside the list root is unchanged.

It must not claim that old nodes formerly linked from this list were modified
or had their containers cleared.

### 5.2 `vListInsertEnd`

Preconditions:

- `raw_xlist_rep s lp xs`;
- `new` has a guarded, valid full-item footprint;
- `new` is not in `set (ring xs)` and is disjoint from the list root and every
  current real item;
- `length (ring xs) < 2^32 - 1`, so the 32-bit count increment does not wrap;
  and
- the key argument to the pure operation is
  `xLIST_ITEM_C.xItemValue_C (itemval s new)`.

The C body overwrites the new item's next, previous, and container fields, so
`pvContainer_C new = NULL` is a useful API discipline but is not necessary for
the local simulation theorem.  Fresh allocation and nonmembership are
necessary.

Let `pred` be the concrete cursor and `succ = next_at s lp pred`.  The relation
must derive every generated guard for `lp`, `new`, `pred`, and `succ`.

Exact write set:

```text
new.{pxNext, pxPrevious, pvContainer}
succ.pxPrevious
pred.pxNext
lp.{pxIndex, uxNumberOfItems}
```

When `pred` or `succ` is the sentinel, the corresponding field footprint is
the embedded mini field inside `lp`.  The proof may not use a full sentinel
allocation.  `pred` and `succ` are also not universally distinct: the empty
ring has both equal to the sentinel.

The postcondition is:

```text
raw_xlist_rep s' lp (list_insert_end_abs new key xs)
```

plus preservation of the new item's key and owner, all old item keys/owners,
all bytes outside the exact write set, and `hrs_htd`.  The ring-splice proof
has two abstract branches matching the pure definition:

- `cursor xs = None`: insert immediately after the sentinel, so
  `ring' = new # ring xs`;
- `cursor xs = Some c`: insert immediately after `c`.

In both branches the post-cursor is `Some new`.

### 5.3 `vListRemove`

Preconditions:

- `raw_xlist_rep s lp xs`;
- `x in set (ring xs)`; and
- `lp` is recovered from `pvContainer_C (itemval s x)` using the pointer-coerce
  round-trip lemma.

Membership gives a nonzero count and prevents unsigned underflow.  Let
`next = next_at s lp x` and `previous = prev_at s lp x`.  The relation derives
the generated guards for `x`, `next`, `previous`, and `lp`.

Exact write set:

```text
next.pxPrevious
previous.pxNext
lp.pxIndex          (only if the old cursor is x)
x.pvContainer
lp.uxNumberOfItems
```

The proof must allow aliasing among neighbour roles:

- in a singleton ring, `next = previous = sentinel`;
- in a two-real-node ring, removing either node gives
  `next = previous = the other real node`.

The postcondition is:

```text
raw_xlist_rep s' lp (list_remove_abs x xs)
pvContainer_C (itemval s' x) = NULL
```

and an exact frame.  The removed item's key, owner, next, and previous fields
remain unchanged.  If the old cursor is `x`, a concrete previous pointer to
the sentinel maps to abstract `None`; otherwise it maps to `Some previous`.
This is precisely the pure model's `predecessor` branch.

## 6. Dependency-ordered lemma graph

The raw bridge should be developed as the following staircase.  Each node is
small enough to build independently after the current one-build exclusion is
lifted.

```text
R0  generated sizes, field offsets, pointer-coerce values
  -> R1  end_item address equation and c_guard arithmetic
  -> R2  h_val projection locality for ordinary fields
  -> R3  sentinel common-prefix read equations
  -> R4  heap_update field locality and exact byte frames
  -> R5  sentinel pxNext update equivalence + trailing-byte preservation

A0  valid_footprint / c_guard split of h_t_valid
  -> A1  disjoint list + real-item allocation certificate
  -> A2  embedded end_mini validity, but no end_item full validity
  -> A3  allocation and separation preserved by hrs_mem_update
  -> A4  concrete empty and singleton allocation witnesses

S0  cyclic successor/predecessor definitions over sentinel + ring
  -> S1  raw_xlist_view implies all dynamic pointer guards
  -> S2  raw_xlist_view implies mutual links, count bound, and containers
  -> S3  representation implies xlist_wf

I0  symbolic execution of vListInitialise'
  -> I1  empty raw_xlist_rep postcondition
  -> I2  exact initialise frame

E0  read phase of vListInsertEnd' identifies pred and succ
  -> E1  alias-aware four-link splice equations
  -> E2  count/cursor/container/key equations
  -> E3  raw representation preservation
  -> E4  exact insert-end frame
  -> E5  forward simulation to list_insert_end_abs

D0  read phase of vListRemove' identifies list/next/previous
  -> D1  alias-aware unlink equations
  -> D2  cursor-to-predecessor equation and count decrement
  -> D3  raw representation preservation
  -> D4  exact remove frame
  -> D5  forward simulation to list_remove_abs

I1 + E5 + D5 + A4
  -> N0  nonvacuous empty -> singleton -> empty raw execution witness
  -> N1  end-to-end frame and abstract round trip
```

`R3` and `R5` are the architectural needle.  If the generated serializer does
not admit prefix-read independence and field-local trailing-byte preservation,
then `skip_heap_abs` is not a faithful bridge for this cast and the target gate
should fail rather than allocating the nonexistent sentinel tail by assumption.

## 7. Adversarial checks before proof search

The following false shortcuts must remain in the failure/counterexample
corpus:

- `c_guard p` implies allocation: false with `empty_htd`.
- `h_val h p` implies allocation: false because `heap_mem` is total.
- the cast sentinel has a valid full `xLIST_ITEM_C` footprint: intentionally
  false for a stock `xMINI_LIST_ITEM_C` embedded at offset 8.
- cursor `None` implies an empty ring: false after ordered insertions, which do
  not move `pxIndex` away from the sentinel.
- `pred`, `succ`, and the modified node are always distinct: false for empty,
  singleton, and two-node rings.
- a whole-structure `heap_update` may be framed by assertion: false until the
  serializer/update locality lemma proves that non-target fields, especially
  the sentinel's unallocated trailing eight bytes, are unchanged.
- equality of full decoded sentinel items is meaningful: false; only the
  common key/next/previous prefix is represented.

These checks force the final bridge to justify exactly what the C program
uses, without turning arbitrary total-heap bytes into allocated objects.
