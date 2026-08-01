# Scheduler translation-unit ABI bridge plan

Status: `DESIGN_ONLY__BOUNDED_ABI_BRIDGE__NO_ISABELLE_BUILD__NO_ORIGINAL_FORMALISATION`

This note fixes the shortest bounded route across the generated-type boundary
between the scheduler translation unit and the independently translated raw
list development.  It is a plan, not a checker result.  No Isabelle build or
proof search was run while preparing it, and no original formalisation was
opened.

The evidence labels used below are strict:

- **EXACT CONFIRMED** means the term, type, statement, or failure occurs in a
  checked theory or the retained final PIDE export.
- **NEEDS PRINT** means the generated entity or its statement has not yet been
  captured.  No fact name is guessed for it.
- **PLANNED** identifies a new definition, statement, or session role.  A
  planned label is not the name of an existing theorem.

## 1. Frozen diagnosis and reuse boundary

The final layout probe establishes the boundary exactly.

**EXACT CONFIRMED:**

```isabelle
raw_xlist_rel ::
  (32 word \<Rightarrow> 8 word) \<Rightarrow>
  List_V611_Raw_Skip_Translation.xLIST_C ptr \<Rightarrow>
  (List_V611_Raw_Skip_Translation.xLIST_ITEM_C ptr, 32 word)
    xlist_abs \<Rightarrow> bool
```

The scheduler heap can be passed as the first argument:

```isabelle
(\<lambda>c. raw_xlist_rel
  (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))
```

but a scheduler root or scheduler item cannot be passed directly.  The two
retained checker failures are:

```text
Clash of types "Scheduler_V611_Parse.xLIST_C"
and "List_V611_Raw_Skip_Translation.xLIST_C"

Clash of types "List_V611_Raw_Skip_Translation.xLIST_ITEM_C"
and "Scheduler_V611_Parse.xLIST_ITEM_C"
```

Thus the byte carrier is common and the generated C structure universes are
distinct.  Importing both theories does not identify the types.

The following split is binding for the bridge.

| Layer | Direct reuse? | Reason |
|---|---:|---|
| `heap_mem`, concretely `32 word \<Rightarrow> 8 word` | yes | exact common carrier accepted by the final probe |
| polymorphic pure `xlist_abs` operations | yes | independent of either generated C record type |
| `raw_xlist_rel` | yes, after coercing roots/items into the raw-list phantom universe | its heap argument is common, but its pointer arguments are not scheduler pointers |
| `xlist_relabel` and `sched_xlist_rel` in `Scheduler_Raw_List_Relabel` | yes, after the same root/item coercion | that checked theory deliberately consumes raw-list node identifiers |
| raw layout, ring, freshness, and relation lemmas | yes, on coerced raw-list pointers | they reason about the common byte heap through raw-list observations |
| pure transformer/projection theorems such as `raw_remove_effect_refines` and `raw_ordered_insert_empty_transformer_refines` | yes, after a scheduler source leaf produces the exact raw transformer heap | their conclusions mention only `heap_mem`, raw-list pointers, and the pure model |
| `raw_vListRemove_general_heap_effect` and `raw_vListInsert_ordered_empty_heap_effect` | no | each opens a different generated source constant over a different `globals` and struct universe |
| fixed raw-list prestates and fixed-address source theorems | no for scheduler execution | they are states of `List_V611_Raw_Skip_Translation.globals`, not `Scheduler_V611_Parse.globals` |
| generated selectors, record updates, `h_val` record values, or `c_guard` facts | no by type equality | each translation owns distinct generated record types; compatibility must be proved field by field |
| `scheduler_translation_unit_global_addresses.all_distinct` | no for object separation | its printed conclusion is about translated function addresses, not the scheduler list objects or ready-array elements |

There must be no attempted equality between a scheduler `xLIST_C` record and a
raw-list `xLIST_C` record.  The bridge is observational: same address, same
bytes, corresponding field reads, and corresponding field writes.

## 2. Pointer coercions and the raw-byte lens

### 2.1 Planned coercion definitions

The first bridge theory should introduce only two directional coercions from
scheduler pointers into the raw-list phantom universe.  The names below are
**PLANNED definitions**, not existing facts:

```isabelle
definition scheduler_root_as_raw ::
  "Scheduler_V611_Parse.xLIST_C ptr \<Rightarrow>
   List_V611_Raw_Skip_Translation.xLIST_C ptr"
where
  "scheduler_root_as_raw p =
     PTR_COERCE(Scheduler_V611_Parse.xLIST_C \<rightarrow>
       List_V611_Raw_Skip_Translation.xLIST_C) p"

definition scheduler_item_as_raw ::
  "Scheduler_V611_Parse.xLIST_ITEM_C ptr \<Rightarrow>
   List_V611_Raw_Skip_Translation.xLIST_ITEM_C ptr"
where
  "scheduler_item_as_raw p =
     PTR_COERCE(Scheduler_V611_Parse.xLIST_ITEM_C \<rightarrow>
       List_V611_Raw_Skip_Translation.xLIST_ITEM_C) p"
```

The `PTR_COERCE` spelling is **EXACT CONFIRMED** generated syntax.  These two
cross-universe instantiations are **NEEDS TERM CHECK**.  Inverses should remain
inline `PTR_COERCE` terms until a checked need for named definitions appears.

The scheduler-level list wrapper can then be defined by composition rather
than by cloning `raw_xlist_rel`:

```isabelle
raw_xlist_rel h (scheduler_root_as_raw lp) rx
```

and a decoder for `Generic t`/`Event t` should consume
`scheduler_item_as_raw` applied to the corresponding embedded scheduler item
address.  This preserves the already checked raw-node type used by
`Scheduler_Raw_List_Relabel`.

### 2.2 Pointer laws required before any relation theorem

The first proof leaf must establish the following statements.  Labels B1--B8
are statement identifiers in this plan, not lemma names.

1. **B1, address preservation:** both coercions preserve `ptr_val`.
2. **B2, round trip:** coercing to the raw universe and back to the matching
   scheduler type returns the original pointer.
3. **B3, injectivity/equality reflection:** equality of coerced roots/items is
   equivalent to equality of the scheduler roots/items.
4. **B4, NULL preservation:** coercion maps NULL to NULL and reflects NULL.
5. **B5, guard transport:** scheduler and raw-list `c_guard` predicates are
   equivalent for corresponding roots and items.  This statement is proved
   only after the size and alignment equalities below.
6. **B6, root-region equality:** the scheduler `xLIST_C` byte interval and
   `raw_list_region (scheduler_root_as_raw lp)` are the same set.
7. **B7, item-region equality:** the scheduler `xLIST_ITEM_C` byte interval and
   `raw_item_region (scheduler_item_as_raw p)` are the same set.
8. **B8, sentinel commutation:** coercing
   `PTR(Scheduler_V611_Parse.xLIST_ITEM_C)
     &(lp\<rightarrow>[''xListEnd_C''])`
   equals `raw_end_item (scheduler_root_as_raw lp)`.

B1--B4 should be unconditional.  B5--B8 must not hide layout equality in an
assumption supplied by the eventual P2 relation; the bridge leaf itself must
discharge it from checked generated layout statements.

### 2.3 Raw-byte observation lens

The lens is a family of field equations over an arbitrary `h :: heap_mem`, not
a conversion between whole HOL records.  For every scheduler root `lp` and
item `p`, the minimum observation set is:

| Structure | Required corresponding observations |
|---|---|
| `xLIST_C` | `uxNumberOfItems_C`; `pxIndex_C` after applying `scheduler_item_as_raw`; embedded `xListEnd_C` prefix observations |
| `xMINI_LIST_ITEM_C` | `xItemValue_C`; `pxNext_C` and `pxPrevious_C` after applying `scheduler_item_as_raw` |
| `xLIST_ITEM_C` | `xItemValue_C`; `pxNext_C` and `pxPrevious_C` after applying `scheduler_item_as_raw`; `pvOwner_C`; `pvContainer_C` |

For example, the required shapes are:

```isabelle
List_V611_Raw_Skip_Translation.xLIST_C.uxNumberOfItems_C
  (h_val h (scheduler_root_as_raw lp))
=
Scheduler_V611_Parse.xLIST_C.uxNumberOfItems_C (h_val h lp)

List_V611_Raw_Skip_Translation.xLIST_C.pxIndex_C
  (h_val h (scheduler_root_as_raw lp))
=
scheduler_item_as_raw
  (Scheduler_V611_Parse.xLIST_C.pxIndex_C (h_val h lp))

List_V611_Raw_Skip_Translation.xLIST_ITEM_C.xItemValue_C
  (h_val h (scheduler_item_as_raw p))
=
Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C (h_val h p)

List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pxNext_C
  (h_val h (scheduler_item_as_raw p))
=
scheduler_item_as_raw
  (Scheduler_V611_Parse.xLIST_ITEM_C.pxNext_C (h_val h p))

List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvContainer_C
  (h_val h (scheduler_item_as_raw p))
=
Scheduler_V611_Parse.xLIST_ITEM_C.pvContainer_C (h_val h p)
```

The analogous previous-link, owner, mini-item value, and mini-item link
statements complete the lens.  These statements should be unconditional in
`h`; `h_val` reads bytes even when a source operation separately requires a
`c_guard`.

For a live TCB `tp`, two additional equations connect the scheduler-only TCB
layout to raw-list node identities:

```isabelle
scheduler_item_as_raw
  (PTR(Scheduler_V611_Parse.xLIST_ITEM_C)
    &(tp\<rightarrow>[''xGenericListItem_C'']))

scheduler_item_as_raw
  (PTR(Scheduler_V611_Parse.xLIST_ITEM_C)
    &(tp\<rightarrow>[''xEventListItem_C'']))
```

Each is the raw phantom pointer used by the decoder.  The owner value remains
a `unit ptr`; it is not enough to distinguish the two fields.  The exact
reverse readback cast
`PTR_COERCE(unit \<rightarrow> tskTaskControlBlock_C)` is **EXACT CONFIRMED**.
The forward TCB-to-`unit ptr` owner equation is **NEEDS TERM CHECK**.

## 3. First ABI leaf: exact statement list

This is the highest-priority next checker leaf.  It must import the existing
checker-green scheduler-root translation and raw R5 relation, but it must not
open a generated function body.  The existing session
`EAL6_FreeRTOS_V611_Scheduler_P2_Generated_Layout_First` already demonstrates
that these two universes can coexist in one theory.

### 3.1 Facts already frozen

The following exact scheduler facts and outputs may be used without guessing:

| Exact fact | Printed result |
|---|---|
| `tskTaskControlBlock_C_xGenericListItem_C_fl` | field offset 4, field type `Scheduler_V611_Parse.xLIST_ITEM_C` |
| `tskTaskControlBlock_C_xEventListItem_C_fl` | field offset 24, field type `Scheduler_V611_Parse.xLIST_ITEM_C` |
| `tskTaskControlBlock_C_uxPriority_C_fl` | field offset 44, field type `32 word` |
| `tskTaskControlBlock_C_size` | `size_of TYPE(tskTaskControlBlock_C) \<equiv> 68` |

The final PIDE also fixes the addressed-root types:

```isabelle
Scheduler_V611_Parse.pxReadyTasksLists_' ::
  (Scheduler_V611_Parse.xLIST_C[4]) ptr

array_ptr_index Scheduler_V611_Parse.pxReadyTasksLists_' False ::
  nat \<Rightarrow> Scheduler_V611_Parse.xLIST_C ptr

Scheduler_V611_Parse.xDelayedTaskList1_' ::
  Scheduler_V611_Parse.xLIST_C ptr
```

with the same last type for `xDelayedTaskList2_'`, `xPendingReadyList_'`, and
`xSuspendedTaskList_'`.

### 3.2 Generated statements that must be printed, not guessed

The leaf must capture the fully qualified generated facts for both
`Scheduler_V611_Parse` and `List_V611_Raw_Skip_Translation`.  If a name has not
first appeared in `find_theorems`, a theory/thms export, or PIDE output, do not
write a guessed `print_statement` command.

The minimum statement inventory is:

1. `size_of` for both versions of `xLIST_C`, `xLIST_ITEM_C`, and
   `xMINI_LIST_ITEM_C`;
2. `align_of` for the same six types, plus scheduler
   `tskTaskControlBlock_C`;
3. `field_lookup` statements for both versions of:
   - `xLIST_C`: `uxNumberOfItems_C`, `pxIndex_C`, `xListEnd_C`;
   - `xLIST_ITEM_C`: `xItemValue_C`, `pxNext_C`, `pxPrevious_C`,
     `pvOwner_C`, `pvContainer_C`;
   - `xMINI_LIST_ITEM_C`: `xItemValue_C`, `pxNext_C`, `pxPrevious_C`;
4. the corresponding generated `h_val` field-projection facts used to reduce
   each observation in section 2.3;
5. any generated pointer-byte or pointer-coercion statement actually needed
   to prove B1--B4 and write compatibility.  The library fact names are
   **NEEDS PRINT**; this plan does not invent them.

The raw R0/R3 theories already use exact base names such as
`xLIST_C_xListEnd_C_fl`, `xLIST_ITEM_C_xItemValue_C_fl`,
`xLIST_ITEM_C_pxNext_C_fl`, `xLIST_ITEM_C_pxPrevious_C_fl`, and the
`xLIST_C_h_val_fields`/`xLIST_ITEM_C_h_val_fields` families.  Their
fully-qualified cross-import spellings and all scheduler counterparts remain
**NEEDS PRINT** in this bridge leaf.

### 3.3 Equality gates proved by the leaf

After the statements are captured, the leaf proves these equalities.  These
are exact target statements, not claims that facts already exist.

1. Scheduler/raw `size_of` equality for `xLIST_C`.
2. Scheduler/raw `size_of` equality for `xLIST_ITEM_C`.
3. Scheduler/raw `size_of` equality for `xMINI_LIST_ITEM_C`.
4. Scheduler/raw `align_of` equality for those same three pairs.
5. Equality of the corresponding numeric field offsets listed in section
   3.2.
6. B1--B4 for root and item coercions.
7. B5--B8: guard equivalence, region equality, and sentinel commutation.
8. Field-lvalue address compatibility for every field in section 3.2.
9. The complete field-level `h_val` lens from section 2.3.
10. TCB generic/event address facts at offsets 4 and 24, containment of each
    20-byte item region in the 68-byte TCB region, and disjointness of those
    two item regions.

The numeric list/item sizes, alignments, and scheduler field offsets are not
filled in here from C intuition.  The bridge accepts them only when both
generated statements print and the equality proofs check.  In particular,
the raw theories' use of 20-byte intervals is useful prior evidence, not yet a
checked cross-translation ABI equality.

### 3.4 Minimum write-compatibility corollaries

Field reads alone do not justify an exact source heap transformer.  Once the
field-lvalue and `h_val` gates are green, derive only the write equations
needed by the two P2 list calls:

| Operation | Required scheduler/raw byte-write correspondence |
|---|---|
| remove unlink | successor `pxPrevious_C` and predecessor `pxNext_C` pointer writes |
| remove cursor repair | whole-list `pxIndex_C_update` normalised to the same bytes |
| remove detach | whole-item `pvContainer_C_update` to NULL normalised to the same bytes |
| remove count | whole-list `uxNumberOfItems_C_update (\<lambda>n. n - 1)` normalised to the same bytes |
| P2 wake key | nested scheduler TCB generic-item `xItemValue_C` write equals the raw item key-field write |
| ordered empty insert | new-item next/previous, sentinel next/previous, item container, and list count writes |

Each conclusion is equality of two `heap_mem` values.  If direct equality of
whole-structure updates is awkward, normalise both sides through
`heap_update_def` to the same primitive field-address byte write.  Do not add
a whole-record scheduler/raw conversion just to prove these equations.

The write equations must quantify over arbitrary intermediate heaps.  This is
what permits their use sequentially through the unlink, key-write, and insert
transformers.

## 4. Re-prove only scheduler source normal forms

The scheduler source constants used by the exact printed `vTaskDelay'_def`
are **EXACT CONFIRMED**:

```isabelle
Scheduler_V611_Delay_Translation.vListRemove'
Scheduler_V611_Delay_Translation.vListInsert'
```

They are not the raw-list translation's source constants.  The bounded bridge
therefore re-proves only two source-facing leaves in the scheduler universe.
The following are statement shapes, not existing theorem names.

### 4.1 Removal leaf

Given

```isabelle
raw_xlist_rel h (scheduler_root_as_raw lp) xs
```

and membership of `scheduler_item_as_raw p` in `ring xs`, executing scheduler
`vListRemove' p` must return normally and produce exactly

```isabelle
raw_remove_concrete_heap h (scheduler_item_as_raw p)
```

as its `hrs_mem`.  It should additionally state the required scheduler-global
frame: fields other than `t_hrs_'` are unchanged, and any non-memory component
of `t_hrs_'` is unchanged.

This leaf opens the scheduler-generated `vListRemove'_def` once.  Its guards
come from raw relation facts plus B5, and every typed read/write is discharged
with the ABI lens.  It does not unfold `raw_remove_effect_refines` or the pure
model.

After this source certificate, reuse the exact existing pure facts:

- `raw_remove_concrete_heap_count_effect`;
- `raw_remove_concrete_heap_index_effect`;
- `raw_remove_concrete_heap_topology_effect`;
- `raw_remove_concrete_heap_payload_effect`;
- `raw_remove_effect_refines`.

The four projection facts can be conjoined once into the existing
`raw_remove_effect` predicate before invoking `raw_remove_effect_refines`.
This conjunction is pure heap reasoning; it must not reopen either generated
C body.

### 4.2 Ordered-empty insertion leaf

Given an empty represented raw ring at `scheduler_root_as_raw lp`, a fresh
`scheduler_item_as_raw p`, and the raw sentinel-maximum condition, executing
scheduler `vListInsert' lp p` must return normally and produce exactly

```isabelle
raw_ordered_insert_empty_heap
  h (scheduler_root_as_raw lp) (scheduler_item_as_raw p)
```

as its `hrs_mem`, with the same scheduler-global frame as the removal leaf.

This leaf opens the scheduler-generated `vListInsert'_def` once.  For P2 the
item key is 7, so the nonmaximum, loop-free empty branch is enough for the
shortest proof.  The existing exact pure theorem
`raw_ordered_insert_empty_transformer_refines` then supplies the abstract
ordered insertion postrelation.  The raw source theorem
`raw_vListInsert_ordered_empty_heap_effect` is not invoked.

### 4.3 Why this split is the reuse point

The source normal forms are translation-unit-specific because their monads,
states, typed guards, selectors, and record updates are translation-unit-
specific.  The normal-form result is a common `heap_mem`.  Once that result is
equal to the already defined raw transformer, every later topology, cursor,
count, payload, and abstract projection can remain in the raw-list universe.
This keeps the ABI proof bounded and avoids duplicating the R5/R6 relation
development.

## 5. Scheduler-universe fallback for empty/singleton only

If the cross-translation `h_val` or write lens does not become checker-green
after the bounded ABI stages below, the fallback is not a second general-N raw
development.  Define only scheduler-universe shapes needed by P2:

1. an empty list: guarded list and cast mini-sentinel prefix, count 0, index at
   the sentinel, and both sentinel links self-linked;
2. a ready singleton: count 1, index at the item, both sentinel links to the
   item, both item links to the sentinel, key/container equations;
3. an ordered delayed singleton: the same topology, but index remains at the
   sentinel after `vListInsert`;
4. freshness/disjointness of the moving item against the destination list.

All fields in this fallback use `Scheduler_V611_Parse.xLIST_C` and
`Scheduler_V611_Parse.xLIST_ITEM_C` directly.  The mini-sentinel remains a
prefix observation of `xListEnd_C`; it is never promoted to a separately
allocated full item.

The fallback proves the singleton ready removal and empty delayed insertion
directly against the scheduler source bodies, then maps only the resulting
empty/singleton shapes to the polymorphic pure `xlist_abs` operations.  It
does not claim reuse of `raw_xlist_rel`, the general-N R6 projections, or the
raw source theorems.  Reports must label it
`SCHEDULER_UNIVERSE_P2_EMPTY_SINGLETON_ONLY`.

The fallback is triggered only after these materially different attempts are
recorded:

1. direct field-level `h_val` correspondence from generated layout facts;
2. byte-normalised field-write correspondence through `heap_update_def`;
3. if necessary, a canonical primitive-field byte transformer used as the
   common normal form.

## 6. Staged sessions and acceptance gates

Every name in this table is a **PLANNED session role**, not an existing
session.  The implementation should choose concrete session names in `ROOT`
only when the corresponding theory directory is created.

| Stage | Stable inputs | Deliverable | Acceptance gate |
|---|---|---|---|
| A: layout print | existing scheduler layout-first session | captured fully qualified size/alignment/field facts for both universes | no guessed fact name; PIDE contains all statements; no source body opened |
| B: pointer/region | A | B1--B8 plus TCB embedded-item containment/disjointness | unconditional address/round-trip laws; size/alignment equality; region equality; fixed pointer witness for both guards |
| C: read lens | B | all field-level `h_val` equations | arbitrary heap, no false premise, all list/item/mini observations covered |
| D: write lens | C | the P2 write table in section 3.4 | equality of complete `heap_mem` results for arbitrary intermediate heaps |
| E: scheduler list source leaves | D plus stable raw R6 heaps | exact scheduler remove and ordered-empty normal forms | each generated body opened once; `Result ()`; exact raw transformer; scheduler-global frame |
| F: P2 list relation | E plus checked relabelling | ready singleton to empty, key 5+2=7, delayed empty to ordered singleton | raw relation post obtained only from pure projection facts |
| G: P2 scheduler phases | F plus scheduler roots translation and pure P2 model | suspend, ResumeAll empty-loop paths, final yield, exact composed state | no monolithic VCG before phase leaves are green |
| H: final P2 refinement | G | concrete P2 source-to-abstract theorem | explicit concrete preimage exists; normal run exists; exact `p2_post`; forbidden scan clean |

Use a staircase of small child sessions: promote A--D only after each is green,
then put the currently changing source leaf in its own child.  The stable raw
R6 projection sessions should be registered as session dependencies rather
than copied.  Theory directories remain exclusive to one session.

All checker stages require:

- a bounded project-wrapper call with one job;
- `quick_and_dirty=false` and exit code 0;
- no `sorry`, `oops`, `admit`, axiom declaration, oracle, or skip-proof route;
- the first Isabelle failure block preserved for a red call;
- no inspection of the original formalisation.

### Non-vacuity gates

1. **ABI gate:** B1--B4 and all `h_val` equations are unconditional.  Guard
   transport additionally has a concrete aligned non-NULL pointer witness in
   both universes.
2. **Layout gate:** no root/TCB separation theorem is derived from
   `scheduler_translation_unit_global_addresses.all_distinct`; actual object
   intervals and ready-array element intervals are proved separately.
3. **Conditional relation gate:** an introduction theorem from explicit root,
   TCB, and list-shape assumptions is reported only as conditional.
4. **Concrete preimage gate:** before final P2 acceptance, construct one
   scheduler `globals`/heap state with both TCBs, all eight roots, both embedded
   items, owners, priorities, role pointers, and scalar fields, and prove the
   endpoint relation holds.
5. **Positive execution gate:** from that preimage, the generated
   `vTaskDelay' 2` has a normal `Result ()` run.  An implication from
   inconsistent guard/overlap assumptions does not pass.
6. **Post discriminator gate:** ready priority 2 is empty, delayed physical A
   is a singleton with key 7, yield count is 1, current remains RUN, and the
   top-ready cache remains 2.  These facts distinguish P2 from a vacuous or
   wrong-phase postcondition.

## 7. Shortest concrete path to P2

The shortest path does not start by defining a general scheduler-wide
representation relation.

1. Complete stages A--D for only `xLIST_C`, `xLIST_ITEM_C`,
   `xMINI_LIST_ITEM_C`, and the TCB generic/event field addresses.
2. Wrap the already checked `sched_xlist_rel` by applying
   `scheduler_root_as_raw`; keep its decoder domain as raw-list item pointers.
3. Build the P2 preimage from exactly eight physical roots and two TCBs:
   ready 0 and ready 2 are ready-singletons; the other six roots are empty.
   Do not yet generalise over arbitrary task sets or nonempty delayed lists.
4. Prove the scheduler removal source normal form at the RUN generic item in
   ready 2.  Reuse the raw removal transformer projections to obtain an empty
   ready-2 relation and a detached item.
5. Prove the scheduler nested key write sets the same raw phantom item's key
   from 0 to 7 and frames both TCB owner/priority fields and all roots.
6. Prove the scheduler ordered-empty insertion source normal form at physical
   delayed A.  Apply `raw_ordered_insert_empty_transformer_refines` to obtain
   the delayed singleton with cursor still at the sentinel.
7. Prove only the P2 branches of `xTaskResumeAll'`: pending-ready count is 0,
   missed ticks are 0, missed yield is 0, suspension returns 1 to 0, and the
   result is 0.
8. Execute the final explicit proof-port yield once.  Preserve tick 5,
   current RUN, delayed-role pointers, and top-ready cache 2.
9. Assemble the exact concrete post and use the already checked
   `task_delay_abs_2_p2` equality.  The endpoint is intentionally
   YieldPending: `core_wf p2_post` holds and `settled_wf p2_post` does not.
10. Only after this P2 theorem and its concrete preimage are green should the
    bridge be generalised to P3, arbitrary list lengths, or nonempty ordered
    insertion.

This route reuses the expensive raw work precisely where it is translation-
unit neutral: byte heap transformers, topology/count/cursor/payload
projections, the raw relation, and relabelling.  It spends new source proof
effort only on the scheduler translation's two list-call normal forms and the
P2 scheduler control phases.

## 8. Explicit no-go claims

- Do not pass a scheduler root or item directly to `raw_xlist_rel`.
- Do not use `typedef` identity in C as HOL generated-type identity.
- Do not equate whole scheduler/raw generated records.
- Do not transport a source theorem across the two `globals` types.
- Do not decode Generic versus Event from `pvOwner_C`; both embedded items
  have the same owner.
- Do not use the function-address `all_distinct` theorem as object-footprint
  evidence.
- Do not assume embedded items are disjoint from their containing TCB; prove
  containment, and prove only Generic/Event mutual disjointness.
- Do not strengthen the embedded mini-sentinel to a full allocated item.
- Do not count a conditional P2 introduction rule as a concrete preimage.
- Do not reopen a scheduler list source body in later projection or final
  refinement sessions once its exact normal-form leaf is green.

## 9. Evidence hashes and design digest

The plan was derived from these current blind artifacts:

| Artifact | SHA-256 |
|---|---|
| `theories/scheduler_p2_generated_layout_first/Scheduler_P2_Generated_Layout_First.thy` | `604A4BCCE04F39AFC499A3F58BC9DD65F7E31A57CA8AB526467DB645FFA8F843` |
| final layout-first `status.txt` | `E022F1D429064BB06F787D5278660637A1B2A9CAFDA89781F6AA8FDB70AD40E1` |
| final layout-first `PIDE/messages` | `1332C8677E07150F9FF461866AACF86FBA58C1BB63C38A175E7FD86BD662C553` |
| `List_V611_Raw_R5_Relation.thy` | `5CD5EF0B3850FEBD712664EA375ED04E3BDDD2C8B80B9AEA75EBDF006613A199` |
| `List_V611_Raw_R6_Ordered_Insert_Empty_Source.thy` | `238178DDF2C973ABF1D2B80B98EAA475D39C89B3DEED16F118480F3A82E681C9` |
| `List_V611_Raw_R6_Ordered_Insert_Empty_Refinement.thy` | `8319D39955FACD488B1409C1CFABBC021E8332A3A3F52645C4A88BDE50413806` |
| `Scheduler_V611_Delay_Translation.thy` | `D34512E4642779C49BF412E7FF05E4FB622EF47E255F152AA1CB765E7EA89A68` |
| `Scheduler_V611_Roots_Translation.thy` | `B560345AB2B38ADC871060A33E7A850E8603C8CC5DADFD6D1945A2FD2C3A3E7B` |

The digest is: **coerce only pointer phantoms; prove equality only of byte
regions, field observations, and field writes; re-prove the two scheduler
source normal forms; reuse the raw pure transformer/projection stack; fall
back only to scheduler-universe empty/singleton shapes.**

