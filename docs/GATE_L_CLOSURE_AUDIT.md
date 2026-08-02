# Gate L Formal Closure Ledger

## Verdict

**Gate L is closed.**  As of 2026-08-02, the central `theories/ROOT`
dependency graph contains both Gate-L top-level sessions and all of their
Gate-L-specific support sessions.  Both top-level sessions have been built
through that central graph with `quick_and_dirty=false`, and both builds are
checker-green.

This verdict applies the Gate-L criteria in
`docs/UNIVERSAL_SCHEDULER_ACCEPTANCE.md:224-242`: general ordered insertion,
general removal, insert-end, the legal empty-ring alias, and scheduler-family
Generic/Event and non-target-root frames are joined by checked dependency
closures.  It is not based on a finite set of priority tests or a single
concrete list instance.

Gate L closure is deliberately narrower than complete scheduler correctness.
In particular, **Gate H remains open**: this ledger does not claim the
universal heap/state `vTaskDelay` theorem, generated resume/tick-loop closure,
or full end-to-end correctness of the FreeRTOS scheduler.

## 1. Central session closure

The following Gate-L sessions are registered in the central `theories/ROOT`.
All declare `quick_and_dirty = false`.

| Central session | Parent and auxiliary sessions | Closure role |
|---|---|---|
| `EAL6_FreeRTOS_V611_Scheduler_Universal_Capacity` | parent `EAL6_FreeRTOS_V611_List_Raw_R5_Interface` | Derives count capacity from representation and freshness rather than assuming it independently. |
| `EAL6_FreeRTOS_V611_Scheduler_Universal_Geometry` | parent `EAL6_FreeRTOS_V611_Scheduler_P2_Raw_Relation` | Universal TCB, Generic/Event, and component-region geometry. |
| `EAL6_FreeRTOS_V611_Scheduler_Universal_Ordered_Insert_Composition` | parent `...Ordered_Insert_General_Refinement`; auxiliary `...Universal_Capacity` | Capacity-free ordered transformer refinement. |
| `EAL6_FreeRTOS_V611_Scheduler_Ordered_Insert_Generated_Capstone` | parent `...Ordered_Insert_General_Loop`; auxiliary `...Universal_Ordered_Insert_Composition` | Joins generated scheduler execution, ordered post-relation, and exact external frame. |
| `EAL6_FreeRTOS_V611_List_Insert_End_Generated_Capstone` | parent `...Ordered_Insert_General_Refinement`; auxiliary `...Universal_Capacity` | Joins generated raw `list.c` insert-end execution, post-relation, derived capacity, and exact seven-field frame. |
| `EAL6_FreeRTOS_V611_Scheduler_Insert_End_Translation_General` | parent `...Ordered_Insert_General_Loop`; auxiliary `...List_Insert_End_Generated_Capstone` | Opens the generated scheduler `vListInsertEnd'` body and connects it to the exact raw heap/effect. |
| `EAL6_FreeRTOS_V611_Scheduler_Remove_Translation_General` | parent `...Remove_Unlinked_Ownership`; auxiliary `...P2_Remove_Source` | Generated scheduler general-remove exact-state and unlinked-effect result. |
| `EAL6_FreeRTOS_V611_Scheduler_List_Family_Frame_Capstone` | parent `...Ordered_Insert_Generated_Capstone`; auxiliaries `...List_Insert_End_Generated_Capstone`, `...Remove_Translation_General`, and `...Universal_Geometry` | Family-wide non-target-root, sibling-owner, and priority-field frame closure for all three list primitives. |

There are two accepted top-level leaves:

1. `EAL6_FreeRTOS_V611_Scheduler_List_Family_Frame_Capstone`;
2. `EAL6_FreeRTOS_V611_Scheduler_Insert_End_Translation_General`.

The project wrapper's explicit `-CentralOnly` mode supplies `-d theories` and
does not also load the per-directory local `ROOT` files.  Thus the accepted
runs below check the central session graph itself and do not rely on a
parallel local session registration.

## 2. Central QAD-false build evidence

| Run ID | Top-level session | Exit | Timed out | Elapsed | QAD | Stdout SHA-256 | Stderr SHA-256 |
|---|---|---:|---|---:|---|---|---|
| `20260802Tgate-l-central-family-02` | `EAL6_FreeRTOS_V611_Scheduler_List_Family_Frame_Capstone` | 0 | false | 30.859 s | false | `D26B5ADF9BD68C686421A5E3A819234BAA14BFA9A46ACB6DC70B04CC09BFFCB9` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |
| `20260802Tgate-l-central-insert-end-01` | `EAL6_FreeRTOS_V611_Scheduler_Insert_End_Translation_General` | 0 | false | 31.678 s | false | `D26B5ADF9BD68C686421A5E3A819234BAA14BFA9A46ACB6DC70B04CC09BFFCB9` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

Each `status.txt` records:

- `quick_and_dirty=false`;
- `timeout_seconds=300` and `timed_out=false`;
- frozen layout ELF SHA-256
  `DC830E50513384D712E0D1C68CB198EA656365F673D021C452D7D7EBD45C045A`;
- frozen layout ledger SHA-256
  `CA288A4CD2344BE979ADFA9DBF0298C6715F196D64AE472D173304289C4F2C02`;
- generated address configuration SHA-256
  `27F74768E1DB1C3F8DBFCFC85371075192BB7D2544ED324DC81B65A9A2911712`.

The corresponding evidence directories are
`runs/20260802Tgate-l-central-family-02` and
`runs/20260802Tgate-l-central-insert-end-01`.

## 3. Core checked theorems and quantified scope

The free Isabelle variables in these statements are implicitly universally
quantified.  No theorem below fixes a particular priority, task identity,
address, ring length, cursor position, insertion position, or concrete heap.

### Generated ordered insertion

`scheduler_vListInsert_ordered_general_source_capstone` executes the generated
scheduler `vListInsert'` body.  Its only semantic premises are:

- `raw_ordered_xlist_rel` for the arbitrary source heap, list pointer, and
  abstract ring; and
- `raw_fresh_for_insert` for the arbitrary new item.

Its postcondition gives the abstract ordered-insert relation and equality at
every address outside the exact six-field write footprint.  There is no
nonempty-ring or neighbour-distinctness premise, so the empty-ring sentinel
predecessor/successor alias remains included.  The supporting theorem
`raw_ordered_insert_general_transformer_refines_unconditionally` derives the
count side condition via `raw_xlist_rel_fresh_count_can_increment`.

### Generated removal

`scheduler_vListRemove_general_exact_state` executes the generated scheduler
`vListRemove'` body for an arbitrary state, list, represented ring, cursor, and
member position.  Its explicit premises are `raw_xlist_rel` and membership of
the removed item in `set (ring xs)`.  The corollary
`scheduler_vListRemove_general_unlinked_effect` exports the corresponding
unlinked effect.  No singleton, fixed priority, P2-only address, or extra
anti-alias premise occurs in the statement.

### Raw and scheduler insert-end

`raw_vListInsertEnd_general_source_capstone` executes the generated raw
`list.c` `vListInsertEnd'` body under exactly `raw_xlist_rel` and
`raw_fresh_for_insert`.  It derives count capacity, preserves the abstract
relation, and frames every address outside the seven source fields: four link
fields, list index, new-item container, and list count.

`scheduler_vListInsertEnd_general_exact_state` separately opens the generated
scheduler `Scheduler_V611_Delay_Translation.vListInsertEnd'` body.  For every
state, list pointer, item pointer, abstract ring, cursor, key, and legal
endpoint alias satisfying `raw_xlist_rel` and `raw_fresh_for_insert`, it reaches
the exact `raw_insert_concrete_heap`.  Its corollary
`scheduler_vListInsertEnd_general_capacity_free_effect` exports the
capacity-free raw effect and exact external frame.  The empty ring is included;
it is not split out or excluded.

### Scheduler-family frames and priorities

`scheduler_family_three_list_primitives_non_target_capstone` is quantified over
the heap `h`, arbitrary finite scheduler roots `roots`, family `fam`, arbitrary
finite live-task set `live`, decoder `D`, target and other roots, three items,
and byte address `a`.  Its explicit premises are:

- `scheduler_family_pre_rel h roots fam live D`;
- target and other root membership plus `target != other`;
- target-ring membership for the removed item;
- freshness for the ordered and insert-end items;
- membership of both inserted items in `universal_managed_nodes live D`;
- absence of those inserted items from all old family rings; and
- membership of `a` in the non-target root's storage.

It proves that remove, ordered insert, and insert-end all preserve that
non-target byte.  The three
`*_family_sibling_owner_priority_byte_frame` theorems additionally preserve
the sibling embedded item's owner field and every live TCB priority field,
under their stated managed-node, nonmembership, distinctness, and live-task
premises.  Same-TCB Generic/Event separation is derived from
`universal_tcb_geometry`; it is not restricted to different tasks or to an
enumerated set of priority values.

These are conditional universal theorems: “all combinations” means all values
satisfying the representation, geometry, membership, freshness, and family
separation invariants above.  The closure does not assert correctness for
malformed heaps or premise-violating aliases.

## 4. Admission and artifact audit

After the two central builds, an exact-word scan over all `theories/**/*.thy`
files for `sorry`, `oops`, `axiomatization`, `quick_and_dirty`, `oracle`, or
`admit` returned no matches.  A separate scan of every `ROOT` below `theories`
found no `quick_and_dirty = true`.  Both accepted build commands explicitly
set `-o quick_and_dirty=false -j 1`.

The frozen layout ledger exists at
`artifacts/frozen_p2_layout/output/layout_ledger.json`; its recomputed SHA-256
is
`CA288A4CD2344BE979ADFA9DBF0298C6715F196D64AE472D173304289C4F2C02`,
which equals the value recorded by both run statuses.

## 5. Closure boundary

Gate L is formally closed for the universal list-layer obligations above.  In
particular, the result is not a proof for one fixed Priority assignment or one
concrete list: the relevant values remain universally quantified, subject to
the explicit invariants.

The following claims are outside this closure and remain open unless closed by
their own ledgers:

- Gate H's universal heap/state `vTaskDelay` theorem across all valid ticks,
  delays, priority assignments, and topologies;
- generated outer resume and missed-tick loop obligations;
- whole-scheduler API refinement and complete end-to-end FreeRTOS functional
  correctness.

Accordingly, the report-ready status is:

> **Gate L closed; Gate H and complete scheduler correctness remain open.**
> Central QAD-false dependency closures now check generated general ordered
> insertion, generated general removal, generated raw and scheduler insert-end,
> derived count capacity, exact byte footprints, legal empty-ring aliases, and
> universal scheduler-family Generic/Event, priority-field, and non-target-root
> frames under their explicit representation and separation premises.
