# R3 design: minimal `vListInsertEnd` staircase

Status: `DESIGN_ONLY_NOT_CHECKER_GREEN`

This is the proposed next rung after checker-green R2
`List_V611_Raw_R2_Init_Item`.  It uses only the stock `skip_heap_abs` final
definition and the blind reconstruction files.  No original formalization was
consulted.

At design time the stable imported facts are:

- R0 guards for list `0x1000`, item `0x2000`, and cast sentinel `0x1008`;
- R1 exact `vListInitialise'` fields and the byte canary at `0x3000`; and
- R2 item/list interval separation, item self-read-after-write, item-to-list
  frame, and exact `vListInitialiseItem'` fields/frames (run
  `20260731Tlist-raw-r2-04-init-item`, exit zero).

The R3 proof should first normalize every generated whole-record update to the
corresponding four-byte field update.  The generated theorem families already
support this:

| Structure | `h_val` field facts | `heap_update` field facts |
|---|---|---|
| `xLIST_C` | `xLIST_C_h_val_fields(1..3)` | `xLIST_C_heap_update_fields(1..3)` |
| `xLIST_ITEM_C` | `xLIST_ITEM_C_h_val_fields(1..5)` | `xLIST_ITEM_C_heap_update_fields(1..5)` |
| `xMINI_LIST_ITEM_C` | `xMINI_LIST_ITEM_C_h_val_fields(1..3)` | `xMINI_LIST_ITEM_C_heap_update_fields(1..3)` |

The field order is the source declaration order: list count/index/end; item
key/next/previous/owner/container; mini key/next/previous.  These facts are
generated from `h_val_field_from_bytes'` and
`heap_update_field_root_conv''`; the first R3 theory should `print_statement`
the six particular indexed facts it uses before attempting the proofs.

## 1. Fixed addresses and exact write set

Add only the mini pointer and field-address abbreviations; retain the R0 roots:

```isabelle
definition raw_sentinel_mini_ptr :: "xMINI_LIST_ITEM_C ptr" where
  "raw_sentinel_mini_ptr =
    PTR(xMINI_LIST_ITEM_C) &(raw_list_ptr\<rightarrow>[''xListEnd_C''])"

definition raw_sentinel_tail_addr :: addr where
  "raw_sentinel_tail_addr = 0x1014"
```

The fixed field locations are:

```text
list count       0x1000 ..+ 4
list index       0x1004 ..+ 4
sentinel next    0x100C ..+ 4
sentinel prev    0x1010 ..+ 4
sentinel tail    0x1014 ..+ 8   (not allocated as part of xLIST_C)
item next        0x2004 ..+ 4
item prev        0x2008 ..+ 4
item container   0x2010 ..+ 4
external canary  0x3000
```

After normalization, `vListInsertEnd' raw_list_ptr raw_item_ptr` has exactly
seven four-byte writes: item next, item previous, sentinel previous, sentinel
next, list index, item container, and list count.  The sentinel tail is not in
this set.

## 2. First four checker bricks

These are the first statements to land.  The snippets are proof skeletons,
not claims that the exact tactic text has already compiled.

### R3.1 Common-prefix next read

```isabelle
lemma raw_sentinel_next_prefix_read:
  "xLIST_ITEM_C.pxNext_C
      (h_val h (raw_sentinel_ptr raw_list_ptr)) =
   xMINI_LIST_ITEM_C.pxNext_C
      (xListEnd_C (h_val h raw_list_ptr))"
```

Proof route:

1. `xLIST_ITEM_C_h_val_fields(2)` turns the left selector into a read of the
   four-byte `pxNext_C` field at `0x100C`.
2. `xMINI_LIST_ITEM_C_h_val_fields(2)` turns the same four-byte read into the
   mini selector.
3. `xLIST_C_h_val_fields(3)` identifies the mini object at `0x1008` with
   `xListEnd_C (h_val h raw_list_ptr)`.
4. The remaining pointer equalities should close with
   `field_lvalue_def`, the three generated `_fl` facts, and the R0 pointer
   definitions.

Schematic proof shape:

```isabelle
  using xLIST_ITEM_C_h_val_fields(2)[of h]
        xMINI_LIST_ITEM_C_h_val_fields(2)[of h]
        xLIST_C_h_val_fields(3)[of h]
  unfolding raw_sentinel_ptr_def raw_sentinel_mini_ptr_def
            raw_list_ptr_def
  by (simp add: field_lvalue_def
      xLIST_C_xListEnd_C_fl
      xLIST_ITEM_C_pxNext_C_fl
      xMINI_LIST_ITEM_C_pxNext_C_fl)
```

Prove analogous previous and key facts only after this one is green.

### R3.2 Whole-item next update normalizes to one field write

```isabelle
lemma raw_sentinel_whole_next_update_to_field:
  "heap_update (raw_sentinel_ptr raw_list_ptr)
      (xLIST_ITEM_C.pxNext_C_update (\<lambda>_. q)
        (h_val h (raw_sentinel_ptr raw_list_ptr))) h =
   heap_update
      (PTR(xLIST_ITEM_C ptr)
        &(raw_sentinel_ptr raw_list_ptr\<rightarrow>[''pxNext_C''])) q h"
```

This is the symmetric orientation of
`xLIST_ITEM_C_heap_update_fields(2)`, discharged with the already checked
`raw_sentinel_ptr_guard`.  Do not unfold `to_bytes` unless the generated field
fact fails to instantiate.

The same one-line pattern should next produce normalizers for:

```text
xLIST_ITEM_C_heap_update_fields(2)  item.next
xLIST_ITEM_C_heap_update_fields(3)  item.previous
xLIST_ITEM_C_heap_update_fields(5)  item.container
xLIST_C_heap_update_fields(2)       list.index
xLIST_C_heap_update_fields(1)       list.count
```

The generated body already expresses successor.previous as a direct field
write, so it needs no root normalizer.

### R3.3 The trailing-eight-byte symbolic canary

```isabelle
lemma raw_sentinel_whole_next_update_tail8:
  "heap_list
     (heap_update (raw_sentinel_ptr raw_list_ptr)
       (xLIST_ITEM_C.pxNext_C_update (\<lambda>_. q)
         (h_val h (raw_sentinel_ptr raw_list_ptr))) h)
     8 raw_sentinel_tail_addr =
   heap_list h 8 raw_sentinel_tail_addr"
```

Proof route:

1. rewrite with `raw_sentinel_whole_next_update_to_field`;
2. prove the concrete intervals `{0x100C..+4}` and `{0x1014..+8}` are
   disjoint using the same `intvl_no_overflow_nat_conv` pattern as R2; and
3. apply `heap_list_update_disjoint_same` after unfolding only the four-byte
   field `heap_update`.

This theorem is the raw-alias gate.  It quantifies over arbitrary `h` and `q`;
it does not allocate `[0x1014,0x101C)`.  If it cannot be proved, R3 must stop
rather than assume a full sentinel item.

### R3.4 Whole-item next update as an embedded-list update

```isabelle
lemma raw_sentinel_whole_next_update_to_list:
  "heap_update (raw_sentinel_ptr raw_list_ptr)
      (xLIST_ITEM_C.pxNext_C_update (\<lambda>_. q)
        (h_val h (raw_sentinel_ptr raw_list_ptr))) h =
   heap_update raw_list_ptr
      (xListEnd_C_update
        (xMINI_LIST_ITEM_C.pxNext_C_update (\<lambda>_. q))
        (h_val h raw_list_ptr)) h"
```

Use three generated conversions, never a full sentinel allocation:

```text
whole xLIST_ITEM next update
  = direct four-byte next-field update          item heap_update_fields(2)
  = whole xMINI next update at 0x1008           mini heap_update_fields(2)
  = whole xLIST xListEnd update at 0x1000       list heap_update_fields(3)
```

The two intervening values are identified by the corresponding generated
`h_val_fields` facts.  This lemma immediately yields, via
`h_val_heap_update` and record selector simp rules:

```isabelle
lemma raw_sentinel_previous_survives_next_update:
  "xMINI_LIST_ITEM_C.pxPrevious_C
     (xListEnd_C
       (h_val
         (heap_update (raw_sentinel_ptr raw_list_ptr)
           (xLIST_ITEM_C.pxNext_C_update (\<lambda>_. q)
             (h_val h (raw_sentinel_ptr raw_list_ptr))) h)
         raw_list_ptr)) =
   xMINI_LIST_ITEM_C.pxPrevious_C
     (xListEnd_C (h_val h raw_list_ptr))"
```

It also proves that count, index, sentinel key, and sentinel previous survive
the generated whole-item update.  Keep the root-to-field and field-to-root
equalities out of the global simp set to avoid rewrite loops.

## 3. Concrete empty prestate

Construct the witness from values, then encode them into an arbitrary base
heap.  Using record updates from `undefined` avoids relying on constructor
argument order:

```isabelle
definition raw_empty_list_value :: xLIST_C where
  "raw_empty_list_value =
    uxNumberOfItems_C_update (\<lambda>_. 0)
     (pxIndex_C_update (\<lambda>_. raw_sentinel_ptr raw_list_ptr)
      (xListEnd_C_update (\<lambda>_.
        xMINI_LIST_ITEM_C.xItemValue_C_update (\<lambda>_. 0xFFFFFFFF)
         (xMINI_LIST_ITEM_C.pxNext_C_update
           (\<lambda>_. raw_sentinel_ptr raw_list_ptr)
          (xMINI_LIST_ITEM_C.pxPrevious_C_update
            (\<lambda>_. raw_sentinel_ptr raw_list_ptr)
            (undefined :: xMINI_LIST_ITEM_C))))
       (undefined :: xLIST_C)))"

definition raw_fresh_item_value ::
  "32 word \<Rightarrow> unit ptr \<Rightarrow> xLIST_ITEM_C"
where
  "raw_fresh_item_value k owner =
    xLIST_ITEM_C.xItemValue_C_update (\<lambda>_. k)
     (xLIST_ITEM_C.pxNext_C_update
       (\<lambda>_. raw_sentinel_ptr raw_list_ptr)
      (xLIST_ITEM_C.pxPrevious_C_update
        (\<lambda>_. raw_sentinel_ptr raw_list_ptr)
       (pvOwner_C_update (\<lambda>_. owner)
        (pvContainer_C_update (\<lambda>_. NULL)
          (undefined :: xLIST_ITEM_C)))))"

definition raw_insert_end_preheap ::
  "heap_mem \<Rightarrow> 32 word \<Rightarrow> unit ptr \<Rightarrow> heap_mem"
where
  "raw_insert_end_preheap base k owner =
    heap_update raw_item_ptr (raw_fresh_item_value k owner)
      (heap_update raw_list_ptr raw_empty_list_value base)"

definition raw_insert_end_prestate ::
  "globals \<Rightarrow> heap_typ_desc \<Rightarrow>
   heap_mem \<Rightarrow> 32 word \<Rightarrow> unit ptr \<Rightarrow> globals"
where
  "raw_insert_end_prestate base d h k owner =
    t_hrs_'_update
      (\<lambda>_. (raw_insert_end_preheap h k owner, d)) base"
```

The meaningful allocation witness should instantiate

```text
d = ptr_retyp raw_item_ptr (ptr_retyp raw_list_ptr empty_htd)
```

but no `ptr_retyp` is performed at the cast sentinel.  Raw execution does not
consult `d`; the allocation theorem is a separate non-vacuity certificate.

The prestate sanity theorem should be proved before symbolic execution:

```isabelle
lemma raw_insert_end_prestate_fields:
  defines "s0 \<equiv> raw_insert_end_prestate base d h k owner"
  shows
    "uxNumberOfItems_C (h_val (hrs_mem (t_hrs_' s0)) raw_list_ptr) = 0 \<and>
     pxIndex_C (h_val (hrs_mem (t_hrs_' s0)) raw_list_ptr) =
       raw_sentinel_ptr raw_list_ptr \<and>
     xMINI_LIST_ITEM_C.xItemValue_C
       (xListEnd_C (h_val (hrs_mem (t_hrs_' s0)) raw_list_ptr)) =
       0xFFFFFFFF \<and>
     xMINI_LIST_ITEM_C.pxNext_C
       (xListEnd_C (h_val (hrs_mem (t_hrs_' s0)) raw_list_ptr)) =
       raw_sentinel_ptr raw_list_ptr \<and>
     xMINI_LIST_ITEM_C.pxPrevious_C
       (xListEnd_C (h_val (hrs_mem (t_hrs_' s0)) raw_list_ptr)) =
       raw_sentinel_ptr raw_list_ptr \<and>
     xLIST_ITEM_C.xItemValue_C
       (h_val (hrs_mem (t_hrs_' s0)) raw_item_ptr) = k \<and>
     pvOwner_C (h_val (hrs_mem (t_hrs_' s0)) raw_item_ptr) = owner \<and>
     pvContainer_C (h_val (hrs_mem (t_hrs_' s0)) raw_item_ptr) = NULL"
```

Expected proof ingredients are only `h_val_heap_update`,
`raw_list_h_val_after_item_update`, the symmetric list-to-item frame lemma,
and record selector simp rules.

## 4. Normalized seven-write heap chain

For the empty witness, name the heaps after field normalization:

```text
h0 = mem s0
h1 = write item.next      := sentinel       to h0
h2 = write item.previous  := sentinel       to h1
h3 = write sentinel.prev  := item           to h2
h4 = write sentinel.next  := item           to h3
h5 = write list.index     := item           to h4
h6 = write item.container := PTR_COERCE list to h5
h7 = write list.count     := 1              to h6
```

Prove one small read-after-write theorem per dependency edge, not all pairs:

1. item writes preserve list.index and sentinel.next;
2. the item.previous write preserves the just-written item.next;
3. the sentinel.previous write preserves sentinel.next;
4. the sentinel.next write preserves the just-written sentinel.previous
   (`raw_sentinel_previous_survives_next_update`);
5. the list.index write preserves both sentinel links and item links;
6. the item.container write preserves all list fields and item links; and
7. the list.count write preserves list.index, both sentinel links, and all
   item fields.

All are consequences of same-field `h_val_heap_update` or disjoint four-byte
intervals.  A generic local helper is sufficient:

```isabelle
lemma raw_h_val_after_disjoint_field_update:
  assumes
    "{ptr_val p..+size_of TYPE('a)} \<inter>
     {ptr_val q..+size_of TYPE('b)} = {}"
  shows
    "h_val (heap_update p (v :: 'a::mem_type) h)
       (q :: 'b::mem_type ptr) = h_val h q"
```

Its proof is the same `h_val_def` plus `heap_list_update_disjoint_same` pattern
already used in R2.  Instantiate it only on the seven fixed field intervals.

## 5. One master VCG and exact postcondition

Run the program VCG only once, after R3.1--R3.4 and the seven-write heap-chain
facts are green.  The master theorem should contain every later projection:

```isabelle
theorem raw_vListInsertEnd_empty_master:
  assumes "raw_empty_fields s"
  shows
  "vListInsertEnd' raw_list_ptr raw_item_ptr \<bullet> s
   \<lbrace>\<lambda>r t.
      r = Result () \<and>
      uxNumberOfItems_C
        (h_val (hrs_mem (t_hrs_' t)) raw_list_ptr) = 1 \<and>
      pxIndex_C
        (h_val (hrs_mem (t_hrs_' t)) raw_list_ptr) = raw_item_ptr \<and>
      xMINI_LIST_ITEM_C.xItemValue_C
        (xListEnd_C (h_val (hrs_mem (t_hrs_' t)) raw_list_ptr)) =
          0xFFFFFFFF \<and>
      xMINI_LIST_ITEM_C.pxNext_C
        (xListEnd_C (h_val (hrs_mem (t_hrs_' t)) raw_list_ptr)) =
          raw_item_ptr \<and>
      xMINI_LIST_ITEM_C.pxPrevious_C
        (xListEnd_C (h_val (hrs_mem (t_hrs_' t)) raw_list_ptr)) =
          raw_item_ptr \<and>
      xLIST_ITEM_C.pxNext_C
        (h_val (hrs_mem (t_hrs_' t)) raw_item_ptr) =
          raw_sentinel_ptr raw_list_ptr \<and>
      xLIST_ITEM_C.pxPrevious_C
        (h_val (hrs_mem (t_hrs_' t)) raw_item_ptr) =
          raw_sentinel_ptr raw_list_ptr \<and>
      pvContainer_C
        (h_val (hrs_mem (t_hrs_' t)) raw_item_ptr) =
          PTR_COERCE(xLIST_C \<rightarrow> unit) raw_list_ptr \<and>
      xLIST_ITEM_C.xItemValue_C
        (h_val (hrs_mem (t_hrs_' t)) raw_item_ptr) =
      xLIST_ITEM_C.xItemValue_C
        (h_val (hrs_mem (t_hrs_' s)) raw_item_ptr) \<and>
      pvOwner_C (h_val (hrs_mem (t_hrs_' t)) raw_item_ptr) =
      pvOwner_C (h_val (hrs_mem (t_hrs_' s)) raw_item_ptr) \<and>
      heap_list (hrs_mem (t_hrs_' t)) 8 raw_sentinel_tail_addr =
      heap_list (hrs_mem (t_hrs_' s)) 8 raw_sentinel_tail_addr \<and>
      hrs_mem (t_hrs_' t) raw_canary_addr =
      hrs_mem (t_hrs_' s) raw_canary_addr \<and>
      hrs_htd (t_hrs_' t) = hrs_htd (t_hrs_' s)
    \<rbrace>"
```

`raw_empty_fields` is exactly the five R1 empty-list field equations; it adds
no full sentinel validity.  The fixed R0 guards discharge every generated
guard.  Suggested proof shape:

```isabelle
  unfolding vListInsertEnd'_def raw_empty_fields_def
  apply runs_to_vcg
  apply (simp only: hrs_mem_update hrs_htd_mem_update
      raw_sentinel_next_prefix_read
      raw_sentinel_whole_next_update_to_field
      raw_sentinel_whole_next_update_to_list
      raw_sentinel_whole_next_update_tail8
      raw_item_h_val_after_self_update
      raw_list_h_val_after_item_update
      raw_h_val_after_disjoint_field_update
      h_val_heap_update)
  (* finish record selectors and 32-bit 0 + 1 separately *)
  done
```

Do not run a second VCG for the tail, canary, key, owner, or allocation frame.
Derive narrower public theorems by weakening this master postcondition.

The abstract singleton corollary is then immediate: the post represents
`ring = [raw_item_ptr]`, `cursor = Some raw_item_ptr`, and the preserved item
key, which is `list_insert_end_abs raw_item_ptr key` applied to the empty pure
state.

## 6. What can be evaluated directly

Suitable concrete smoke checks, after defining `raw_insert_end_prestate`:

- the mini/sentinel/field addresses `0x1008`, `0x100C`, and `0x1010`;
- all conjuncts of `raw_insert_end_prestate_fields`;
- the seven direct field writes on a zero base heap and their singleton field
  observations; and
- two heaps equal on the allocated list/item bytes but with different
  eight-byte sentinel-tail patterns, checking that each pattern survives.

Use `by eval` only if the generated C record codecs have executable equations;
otherwise the same fixed goals should close by `simp`.  These cannot be
replaced by evaluation and require symbolic proofs:

- `raw_sentinel_next_prefix_read` for arbitrary heaps;
- update normalization as function equality;
- the arbitrary-heap trailing-eight-byte theorem;
- `runs_to` for the generated monad; and
- allocation/representation preservation.

The first R3 build should stop at the first of R3.1--R3.4 that fails.  In
particular, do not begin the master VCG before the tail theorem is green.
