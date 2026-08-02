# Target decision

Status: `FINAL_GO__SEALED_BLIND_MILESTONE__EXACT_REFINEMENTS_13__DISTINCT_OPERATIONS_8__SEQUENTIAL_COMPOSITIONS_2__FROZEN_P2_PREIMAGE_GREEN__FOUR_CALL_HARD_GATE_GREEN`

## Final decision (2026-08-01)

The scoped FreeRTOS V6.1.1 target is accepted and sealed.  Both conditions
that were open at the preceding decision checkpoint are now checker-green:

1. an artifact-bound P2 preimage instantiates the artifact-specialized
   positive-delay generated-source refinement; and
2. the literal `vListInitialise' -> vListInitialiseItem' ->
   vListInsertEnd' -> vListRemove'` hard-gate chain executes and refines its
   abstract remove-after-insert result.

The portable artifact identity is frozen ELF
`DC830E50513384D712E0D1C68CB198EA656365F673D021C452D7D7EBD45C045A`,
layout ledger
`CA288A4CD2344BE979ADFA9DBF0298C6715F196D64AE472D173304289C4F2C02`,
and generated addressed-global configuration
`27F74768E1DB1C3F8DBFCFC85371075192BB7D2544ED324DC81B65A9A2911712`.
The external builder and generator extract, relink-check, and hash-lock this
ELF/ledger/configuration correspondence.  Isabelle consumes the generated
addresses as definitions; it does not prove that correspondence or a
source-to-binary relation.
Six mapped C bases derive nine static list regions; eight are P2 roots.  Fresh
logical runtime TCB addresses are guarded and separated from all nine.  This
closes logical non-vacuity without claiming that an allocator or boot path
constructs the witness.

The artifact-specialized generated `vTaskDelay' (2 :: 32 word)` exact-state/refinement path
ends at `YieldPending` and agrees with `task_delay_abs 2 p2_pre`.  The literal
four-call theorem has no assumptions and exactly three `runs_to_bind`
compositions.  It intentionally makes no `tail8` claim.

The final accounting is **13 source-to-abstract refinements, 8 distinct
operations, and 2 sequential compositions**.  The portable parser, no-go,
static geometry, dynamic geometry, P2 preimage, four-call, list-smoke, raw
skip-heap, and capstone-assumption-audit replays all exited 0 without timeout and with
`quick_and_dirty=false` (respectively 23.566, 33.162, 27.701, 27.467,
120.854, 32.338, 67.973, 22.551, and 137.387 seconds).  The last session
checks the five capstone theorem objects and finds zero premises, hypotheses,
propositional implications, sort hypotheses, or extra sort hypotheses; no
function-address or generated `G`/`S` locale premise survives.

The accepted scope excludes allocator and task-construction correctness,
boot/scheduler-start reachability, context-switch execution after the pending
yield, compiler and machine-code correctness, binary/source equivalence, and
full-scheduler functional correctness.

## Historical decision record

The remaining sections preserve the chronological decision audit.  Any
statement below that the layout/preimage or four-call chain was "open" is a
checkpoint statement and is superseded by the final decision above.

## Selected object

The provisional object is the scheduler/list slice of the official, unannotated
FreeRTOS V6.1.1 release.  The narrowed semantic roots are:

- `vTaskDelayUntil`;
- `vTaskDelay`;
- `vTaskIncrementTick`;
- `vTaskSwitchContext`; and
- `xTaskGetTickCount`.

Their source-only transitive C-call closure adds scheduler suspend/resume and
all five out-of-line `xList` bodies.  List initialisation is retained as the
state-construction boundary even though it is not called by the five roots.
Function-like macros are separate graph nodes; in particular the closure must
retain the otherwise easy-to-miss edge
`prvAddTaskToReadyQueue -> vListInsertEnd`.

This slice was chosen because it contains a genuine state machine rather than a
collection of independent functions: FIFO ready queues, ordered delayed queues,
tick wrap, wake-up, priority selection, and round-robin context selection all
meet in the same representation invariant.  Task creation/allocation is now an
explicit initial-state contract, avoiding an allocator/stack-port proof that
would push the semantic target beyond the requested size.

## Current size evidence

Under the frozen lean configuration, an exact union of upstream line intervals
is **670 physical / 587 nonblank / 458 nonblank-noncomment lines**.  It includes
the selected bodies, both scheduler helpers, every stock list body, the TCB and
used scheduler globals, active private/list macros, declarations, include
edges, and conservative fallback macro groups.  The full interval table is in
`SOURCE_SCOPE.md`.

Inactive configuration branches are not silently used to alter behaviour.  We
publish both:

1. the configuration-active semantic slice; and
2. the complete compile/translation support footprint (TCB/global/type/config/
   port declarations), even where support lines are not counted as executable
   target bodies.

The semantic source slice therefore passes the requested 500--800 physical-line
gate.  The honest whole-TU parser footprint is separately **5,603 physical /
4,660 nonblank / 2,274 nonblank-noncomment lines**; it is tooling/support, not
misreported as a 670-line program.  If “500--800” is instead defined to include
the complete unsliced translation unit, FreeRTOS is a size `NO_GO` and the
fallback must be used.  Preprocessed expansion is never used to inflate or
shrink the score.

## Alternatives considered

The strongest fallback is the fixed VST `sha.c + hmac.c + hkdf.c` stack at
commit `cbee87efb4bee2b588f8321e16b4cb7664d5cf60` (636 physical C lines,
539 nonblank C lines; 790/664 when the two public headers are included).  Its
FIPS/RFC oracle and test vectors make completion more likely, but it exercises
far less independent design of an abstract mutable state, cross-operation
representation relation, and scheduler-wide invariant.

Swap-server, CertiGC, HMAC-DRBG, FreeRTOS queue/IPC, and TweetNaCl candidates
were rejected for size/dependency risk or because search results exposed parts
of the original specification/invariants.  Those contaminated candidates are
not used as sources for this experiment.

## Hard acceptance gate

FreeRTOS becomes the frozen target only if a bounded, `quick_and_dirty=false`
run establishes all of the following without modifying upstream bodies:

1. CParser/AutoCorres2 translates the real `xList` sentinel/cast pattern;
2. an initialise -> insert-end -> remove list needle retains the intended heap
   aliasing rather than erasing it through a proof-port trick;
3. at least one selected scheduler body translates with all port effects shown
   as named contracts;
4. a provenance-preserving source slicer reproduces the 670-line interval
   union and the separate 5,603-line parser footprint;
5. a nonempty concrete-state witness satisfies the proposed representation
   relation; and
6. a mutation of a link update or tick-overflow branch makes a checker goal or
   executable oracle fail.

If the mini-list/item prefix cast requires a semantic source rewrite, if the
honest active slice exceeds 800 lines, or if external stubs can arbitrarily
repair scheduler state, the decision changes to `NO_GO` and the SHA/HMAC/HKDF
fallback is activated.

## New decisive blocker: typed sentinel root

Run `20260731Tm0-bridge-06-root-guard` is checker-green with
`quick_and_dirty=false`.  It proves two facts about the exact types and
validity predicates generated from untouched stock `list.c`:

1. a valid 20-byte `xLIST_C` root and a valid 20-byte `xLIST_ITEM_C` root at
   its cast `&xListEnd` address (offset 8) cannot coexist, because the typed
   root footprints overlap; and
2. `IS_VALID(xLIST_C) s list` implies that the generated
   `IS_VALID(xLIST_ITEM_C) s (cast &xListEnd)` guard is false.

This is stronger than a failed proof tactic and weaker than an operational
No-Go.  The next gate is an explicit theorem over `vListInsertEnd'` (and, if
needed, its pre-heap-lift correspondence level) that proves or refutes whether
the empty-list sentinel execution has any result.  Until that theorem is
checked, successful AutoCorres translation is not accepted as evidence that
the translated function has a satisfiable intended path.

That next gate is now checked.  Run
`20260731Tm0-bridge-07-operational-top` proves that whenever a valid concrete
list's `pxIndex` is the cast sentinel, the generated execution satisfies

```isabelle
run (vListInsertEnd' list item) s = ⊤
```

and consequently has no `runs_to` execution for any postcondition.  The proof
unfolds the generated function body and uses the checker-green guard-conflict
lemma before any heap update.  It is an operational emptiness result for the
exact empty-list cursor condition, not an inference from a failed tactic.

The standard heap-lifted AutoCorres route therefore fails hard gate 2.  The
next bounded audit consequently tests official non-source-rewriting routes
(`skip_heap_abs`/per-function `no_heap_abs`) and the pre-heap-lift semantics.
A route is acceptable only if it supplies a checked nonempty initialise/
insert/remove path and retains a correspondence theorem to the untouched C.
Merely translating or suppressing a diagnostic does not pass.

The first official alternative audit is now translation-green.  Run
`20260731Tlist-raw-skip-01` uses `skip_heap_abs` on the same untouched source
and proof-port hashes.  Its final definitions retain the raw C heap and use
`c_guard` on the list, new item, cursor and linked pointers; they contain no
split-heap `root_ptr_valid` predicate.  Thus the checker-green root conflict
is specific to the split-heap abstraction and does not by itself reject the
raw C semantics.

This remains a candidate route rather than a passed full gate.  The concrete-
address guard witness, empty-to-singleton insert segment, singleton-to-empty
remove segment, general-N member removal, general-N fresh insert-end, and a
general remove-then-insert-end source-to-abstract composition, plus restricted
empty-list ordered insertion, are now checked.  The sequential and restricted
ordered cases do not yet construct the full initialise -> insert-end -> remove
hard-gate path.  The local representation relation therefore targets raw heap
bytes/`h_val` rather than split typed heaps, and that extra proof cost remains
part of the Go/No-Go decision.  Per-function `no_heap_abs` remains a separate
option for determining whether the raw burden can stay local to the five list
bodies.

Runs `20260731Tlist-raw-r0-05-guards`,
`20260731Tlist-raw-r1-05-init`, and
`20260731Tlist-raw-r2-04-init-item` now discharge the first three raw rungs:
the concrete guards hold, `vListInitialise'` has the exact empty-list poststate,
and `vListInitialiseItem'` sets `pvContainer` to `NULL` while preserving its
other fields, the separate list object, and an out-of-footprint byte canary.
All three final runs are exit-zero with `quick_and_dirty=false`.  They do not
yet establish a representation relation or a source-to-abstract simulation.

R3 has now passed that concrete locality gate.  In the raw translation,
updating the cast sentinel proceeds through a full 20-byte `xLIST_ITEM_C`
read/modify/write at list-base + 8 even though the actual embedded mini-item
occupies only 12 bytes.  The checked proof derives the common-prefix fields
from the 20-byte list object without assuming a full typed sentinel object and
frames the trailing eight raw bytes at list-base + 20 through list-base + 27.

The final R3 run is `20260731Tlist-raw-r3-master-01`: exit 0 in 33.513 s,
`quick_and_dirty=false`, and no timeout.  Its theorem
`raw_vListInsertEnd_empty_master` gives a positive `Result ()` execution of
the source-derived raw `vListInsertEnd'` from the exact empty-list/fresh-item
witness.  The poststate has count 1, cursor at the item, sentinel next/previous
at the item, item next/previous at the sentinel, and the item container at the
list; it also preserves key, owner, all eight trailing bytes, the far canary,
and heap typing.  The master theorem only conjoins eight separately checked
postcondition groups with `runs_to_conj` and weakens once; it is not a second
monolithic symbolic execution.

R5 now closes the first fixed source-to-abstract simulation segment.  Run
`20260731Tlist-raw-r5-10-show-thesis` is exit-zero in 25.236 s with
`quick_and_dirty=false` and no timeout.  It checks both the positive related
prestate witness `raw_insert_end_prestate_rep_empty` and theorem
`raw_vListInsertEnd_empty_refines`: from that fixed related empty state, the
source-derived raw `vListInsertEnd'` reaches `Result ()`, and its output heap
is related by `raw_xlist_rel` to the independently defined
`list_insert_end_abs` result.  The theory SHA-256 is
`5CD5EF0B3850FEBD712664EA375ED04E3BDDD2C8B80B9AEA75EBDF006613A199`.

R4 has also closed the concrete singleton-removal path.  Its master theorem
`raw_vListRemove_singleton_master` is checker-green in run
`20260731Tlist-raw-r4-master-01`: exit 0 in 38.229 s,
`quick_and_dirty=false`, and no timeout.  Across the R4 development there were
21 checker calls, 11 green calls, and exactly 726.726 s (12.112 min) of checker
wall time.  The master theory SHA-256 is
`6F7F2107DD62B00D8541DA2E3C449452AD70A5E291DBC31D835B6819EE998E54`.
It checks the fixed singleton-to-empty result and concrete frame facts; it is
not itself a source-to-abstract refinement theorem.

The corresponding fixed remove refinement is now checker-green too.  Theorem
`raw_vListRemove_singleton_refines` maps source-derived `vListRemove'` through
`raw_xlist_rel` to the independently defined `list_remove_abs` operation for
the fixed singleton-to-empty case.  The first run, `r5r-01`, was red after
45.226 s while its prestate leaf was already green; final run
`20260731Tlist-raw-r5r-02-remove-refinement` is exit-zero in 35.741 s with
`quick_and_dirty=false`.  Total remove-refinement cost was therefore exactly
80.967 s across two calls, with one final green call.  Its prestate and
refinement theory SHA-256 values are respectively
`FE1DF5B644267CD33E6C5E6962144684BDF3EC0A3E3E62DA3701D09AEAF49AF7`
and
`4187C45D7E870E77A3EC009B0D1424597BFF9FEBB84A850D59FF4DB6C6FF653F`.

The next three green theories reduce general-N proof risk but deliberately stop
before a source VCG.  R5 cycle run
`20260731Tlist-raw-r5c-04-nth-append` checks arbitrary finite-cycle traversal,
first return, injectivity, and reachability in 24.581 s; its four attempts total
113.138 s.  R6 generic-prefix run
`20260731Tlist-raw-r6gp-01-generic-prefix` checks the address-parametric
mini-sentinel bridge in 35.260 s.  R6 dynamic-guard run
`20260731Tlist-raw-r6dg-06-imageI` checks general cycle closure and insert/remove
pointer-guard interfaces in 23.831 s; its six attempts total 151.292 s.  All
three final runs have `quick_and_dirty=false`.  Their theory SHA-256 values are
respectively
`E4C7B971C69464B29C1ED2EE4B20D0E87B1A329F80E960AAE14A779F442E4F3E`,
`281703B2FDEDEC5756C5F01127F4DFE4FB367F9E9F7C72CFD7A56FCDE6A1CD85`,
and
`82D4F9E75A801E4D433346F85B5B32FE59BDE1992F70A2BE67283CC1A68A1758`.
They open no generated C body and add no operational refinement theorem.

Subsequent R6 bricks separate source execution from postrelation assembly.
Run `20260731Tlist-raw-r6ul-13-general-remove-direct-exact` is the final green
of 13 calls (341.606 s total) and proves `raw_vListRemove_general_result` from
`raw_xlist_rel` and membership.  It opens the generated source body but its
postcondition is only `Result ()`; therefore it is not refinement.  The remove
and insert assemblers are pure relation lemmas: latest remove run
`20260731Tlist-raw-r6rr-07-count-transfer` is green after seven calls
(306.099 s total), and final insert run
`20260731Tlist-raw-r6ir-03-live-cases` is green after three calls (86.850 s
total).  Their current theory hashes are respectively
`4CE9BE41FC318FCF2919BCAC2F72B7CED73833BA3DC37980D92B827A429687CF` and
`9022271DAB3CE824CBE19C5D2DBB1EF2AC4295D6CFACD0BA6F6E6B3D061A204D`.

The alias-safe unlink projection theory also remains non-refinement.  Four
calls total 114.016 s (three green); final
`20260731Tlist-raw-r6up-04-two-write-where` checks same-node, cross-node and
sentinel frames plus the composed two-write ring-link effect.  Its current
hash is `8581095989FC3ED46DE8BA4E9A6FFEB12BE0A016E6076313E40699C8C2A62712`.
It opens no generated C body and no abstract operation.

General-N member removal is now a genuine refinement, after a deliberately
staged effect pipeline.  Metadata/effect assembly, one exact source-heap VCG,
three source-effect projections, and the final relation assembler used 44
checker calls, 14 green, and exactly 1309.315 s.  The exact source theorem
`raw_vListRemove_general_heap_effect` fixes the concrete byte-heap transformer;
index, topology, and payload theorems are projections of that one execution.
`raw_vListRemove_general_effect` conjoins the checked projections, and
`raw_remove_effect_refines` supplies the pure representation transfer.

Final run `20260731Tlist-raw-r6rgr-01-assemble` was green on its first call in
37.520 s.  Theorem `raw_vListRemove_general_refines` maps source
`vListRemove' p` through `raw_xlist_rel` to `list_remove_abs p xs` for an
arbitrary represented list and any member `p`.  This is marked
`general_operation_refinement=true`; nonmember removal is outside its premise.
The final theory hash is
`A08443F3DC4B2CB828D8089AC41BC4F59C004C38E98257A07B9B607E2F039B6A`.

General-N insert-end is now a genuine refinement too.  Supporting run
`20260731Tlist-raw-r6ise-01-first` was green on its first 27.544 s call and
checks `raw_vListInsertEnd_general_heap_effect`: one generated-body VCG fixes
normal return and the exact seven-stage `raw_insert_concrete_heap`
transformer.  It is explicitly a support layer, not an independent refinement
theorem, and has SHA-256
`38D21F5E8D283FD8938912C23F3D271A8CEFB7FA3640D4EE7CA61A806149BC0D`.

Four post-transformer calls then used exactly 151.579 s (three red, one
green).  Final run `20260731Tlist-raw-r6ipt-04-where-spacing` was green in
36.401 s with `quick_and_dirty=false`.  Theorem
`raw_vListInsertEnd_general_refines_via_transformer` maps source
`vListInsertEnd' lp p` through `raw_xlist_rel` to `list_insert_end_abs` for an
arbitrary represented list, a fresh item, and a count that can increment.
Across support and assembly this pipeline used five calls, two green, and
179.123 s.  The final theory hash is
`E83219F8F59CBF18A6BB4050A3E8F380F586BD5B237AD0EE2857D7635846959C`.

The first general sequential composition is now a genuine refinement as well.
Seven development calls used exactly 237.172 s (three red, four green), and
final run `20260731Tlist-raw-r6ris-07-bind-weaken` was green in 31.956 s with
`quick_and_dirty=false`.  Theorem
`raw_vListRemove_insert_end_general_refines` checks source
`vListRemove' p` followed by `vListInsertEnd' lp p` against
`list_insert_end_abs` after `list_remove_abs` for every represented list member.
The proof does not reopen either generated body: it composes the two checked
general refinements after proving three bridge obligations—post-remove
freshness, count headroom, and preservation of the removed item's key.  Its
theory SHA-256 is
`E12FDC4BA9A08F62C2C8F0C8493657CECE41FEE88D8B14F11360738E65B85A9D`.
Chronologically it is strict theorem #10 and has zero distinct-operation-count
delta.

Restricted empty-list ordered insertion is now a genuine fixed refinement.
Its source-effect theory used 18 calls, five green, and exactly 534.339 s;
final run `20260731Tlist-raw-r6ois-18-transformer-end-frame` was green in
39.848 s with `quick_and_dirty=false`.  The unified exact source theorem covers
both the maximum-key special branch and the nonmaximum loop-free branch of
`vListInsert'` and yields `raw_ordered_insert_empty_heap`.  This source layer
is explicitly non-refinement.  Its theory SHA-256 is
`238178DDF2C973ABF1D2B80B98EAA475D39C89B3DEED16F118480F3A82E681C9`.

The refinement layer used three calls, one green, and exactly 167.993 s; final
run `20260731Tlist-raw-r6oier-03-key-let` was green in 89.835 s with
`quick_and_dirty=false`.  Public theorem
`raw_vListInsert_ordered_empty_refines` maps source `vListInsert'` to
`list_insert_ordered_abs` under an empty-ring, fresh-item, and maximum-key-
sentinel boundary.  `raw_vListInsert_ordered_empty_refines_ordered` preserves
the strengthened ordered relation, and
`raw_vListInsert_ordered_empty_max_refines` states the maximum-item-key
special case.  This is not a general/nonempty ordered-insert theorem and is
recorded with `general_operation_refinement=false`.  Its theory SHA-256 is
`8319D39955FACD488B1409C1CFABBC021E8332A3A3F52645C4A88BDE50413806`.
The complete ordered-empty pipeline used 21 calls, six green, and 702.332 s;
it supplies strict theorem #11 and the eighth distinct refined operation.

The five scheduler roots also now have a pure checker-green endpoint model and
basic facts.  Five attempts total exactly 156.511 s; final run
`20260731Tscheduler-abs-05-let-def` is exit-zero in 45.724 s with
`quick_and_dirty=false`.  Its theory SHA-256 is
`FE22AA8F2850CDCD777D89E1D6CD3880DCD9D9524A75DCACF97B46839B98D1DE`.
The theory has no raw heap, generated C program, or representation relation, so
it is an abstract definition/invariant layer—not scheduler C refinement.

The trace-driven P2 boundary now also has a closed pure-model witness.  Six
calls used exactly 115.266 s (two green); final run
`20260731Tscheduler-p2-06-post-witness` was exit-zero in 12.597 s with
`quick_and_dirty=false`.  The checked transition is
`task_delay_abs 2 p2_pre = p2_post`; the prestate satisfies `settled_wf`, while
the poststate satisfies `core_wf` and deliberately fails `settled_wf`, with
the tick/current/ready/delayed/wake/yield observations stated explicitly.  Its
theory SHA-256 is
`FB03C1FDE6BEC66357F4E7185838423B8867D8999E2CD1422CF2064DC0C48236`.
This theory contains no raw heap, generated C, concrete preimage, or source
relation.  It therefore adds zero strict rungs and does not establish a
positive-delay `vTaskDelay'` refinement.

The scheduler composition unit and all five frozen roots now pass the raw-heap
translation gates.  Parse run `20260731Tscheduler-parse-01` is green in
50.663 s.  Tick translation first failed in the split-heap route after
56.917 s, then passed via `skip_heap_abs` in final run
`20260731Tscheduler-tick-02-raw-heap` (21.777 s; 78.694 s across both calls).
Delay/support and remaining-root runs
`20260731Tscheduler-delay-01-raw-heap` and
`20260731Tscheduler-roots-01-raw-heap` are green in 44.158 s and 45.959 s.
Their theory SHA-256 values, in parse/tick/delay/roots order, are
`353A991C993A16F33D197E51709D39958DA8F64672AC82D1E14CBDDB127BBF09`,
`7299537CA9D94A6B292F308114250F99AF435F3E891CB62407411AE67071E291`,
`D34512E4642779C49BF412E7FF05E4FB622EF47E255F152AA1CB765E7EA89A68`,
and
`B560345AB2B38ADC871060A33E7A850E8603C8CC5DADFD6D1945A2FD2C3A3E7B`.
These are translation/non-refinement gates.

Three additional checker-green support layers sharpen the path to P2 without
changing the refinement decision.  `Scheduler_Raw_List_Relabel` checked in two
calls/one green and exactly 57.276 s; final run
`20260731Tscheduler-relabel-02-intro-disambiguate` took 29.046 s, and the
current theory SHA-256 is
`3EED28E0FA3ADC44682E4ABE32569A4D2BDC1FA3392F693E7DA07578A2F129AA`.
It is a pure explicit-decoder relation layer, not source execution.

The generated-layout probe checked in four calls/one green and exactly
236.199 s; final run `20260731Tscheduler-p2-layout-first-04-green` took
58.491 s, and the theory SHA-256 is
`604A4BCCE04F39AFC499A3F58BC9DD65F7E31A57CA8AB526467DB645FFA8F843`.
The scheduler and raw-list translations share the effective
`32 word -> 8 word` heap carrier but inhabit distinct generated `xLIST_C` and
`xLIST_ITEM_C` universes.  The probe defines no relation and proves no object
footprint theorem.

The ABI plan remains static design-only material: zero checker calls, no build
claim, not fully implemented, SHA-256
`40B17DFB17C82FEE8869B45679B664CB595B98872E09FA0E8EA55AAC56231F6C`.
The separately implemented bounded ABI foundation was green on all three
calls, exactly 112.143 s; final run
`20260731Tscheduler-list-abi-03-packed-hval` took 23.281 s.  Its 36 facts check
pointer, size/alignment, guard/region, selected-address, offset, sentinel, and
packed-read compatibility across the distinct struct universes.  Its theory
SHA-256 is
`2F9CB0E2D0CE2D99E40AF25C1CDAB75DD8C7FB68018BFBA8E8CD8671427F5434`.

The Stage-D field-write bridge checked in two calls/two green and exactly
42.023 s; final run `20260731Tscheduler-list-abi-write-02-pointer-fields` took
20.882 s.  Its 13 lemmas cover key, next, previous, container, index, and count
field addresses and arbitrary-intermediate-heap writes across the two phantom
record universes.  Its theory SHA-256 is
`C972FA5B4CAFCC230056DBA267EC6581B144E93C4BDFCED7015CDB0399AED76A`.

The first layered scheduler/raw relation then checked in eight calls/four
green and exactly 251.043 s.  Final run
`20260731Tscheduler-p2-raw-rel-08-empty-extractors` took 28.897 s with exit 0 and
`quick_and_dirty=false`; theory SHA-256 is
`9A153B79D0871D4D96A5DF82299EF0D40AC8F918692FE60934A8245E048510ED`.
The relation now includes reverse-unique TCB and Generic/Event decoder laws as
well as generated roots, list, role, scalar, current, boundary, and endpoint
layers.  It also extracts P2's exact running ready-list raw ring/cursor pointer
and raw empty witnesses for delayed A and pending-ready.
Its P2 pre/post theorems are conditional introductions only: no
concrete preimage is constructed, no scheduler source body is opened, and no
`vTaskDelay' 2` run is proved.  These support records add no
source-to-abstract theorem and no distinct operation.  The positive-delay
source theorem and concrete P2 preimage remain open.

The first genuine scheduler refinement is also checker-green.  Relation
`scheduler_tick_boundary_rel` requires quiescent critical depth 0 and
interrupts-disabled flag 0 and equates committed `xTickCount` with abstract
`sa_tick`.  Theorem `xTaskGetTickCount_refines` maps source
`xTaskGetTickCount'` to `task_get_tick_abs`, returns that committed tick, and
preserves the relation; it does not return missed-tick debt.  Three calls cost
exactly 72.610 s (one red, two green); final run
`20260731Tscheduler-tick-refine-03-explicit-model-op` took 24.323 s with
`quick_and_dirty=false`.  Its theory SHA-256 is
`99D46C2193DD213CF6D4645D48A4F93F18B50CA8887BA1ABC74255BF77094BCA`.

Three more scheduler roots now have restricted checker-green refinements.
`vTaskSwitchContext_suspended_refines`, run
`20260731Tscheduler-switch-suspended-01` (36.548 s), maps the nonzero-suspension
branch's `xMissedYield := 1` update to `sa_missed_yield := True` without ready-
list access or proof-port yield.  Its hash is
`E6907500EEE776183F11178EEDDC095E6DE92E14CB7C23A8F382C2B16C685D4A`.
`vTaskIncrementTick_suspended_refines`, run
`20260731Tscheduler-increment-tick-suspended-01` (36.297 s), maps the suspended
branch's missed-tick word increment to the abstract natural-number debt.  Its
nonzero-suspension and explicit no-wrap premises are part of the theorem; the
committed tick remains fixed and no delayed list is inspected.  Its hash is
`06077C3FCD1F17C07694437957C7D4AA5CB94D68C056B3BC80B9E3B73F60F098`.

`vTaskDelay_zero_refines`, final run
`20260731Tscheduler-delay-zero-02-vcg-solved` (20.619 s; 53.837 s across two
calls), covers argument exactly 0 under an explicit no-wrap premise for the
proof-port yield counter.  It maps one source yield-count increment to
`sa_yield_count := Suc sa_yield_count` and does not access the suspend
protocol, current TCB, or any list.  Positive-delay source refinement remains
unproved; P2 is pure-model evidence only.  Its hash is
`A77DE8F4215AF1EE592858B9232FD8F3EF068D5A2C12C4912C99028FE525D9E4`.

`vTaskDelayUntil_suspended_no_delay_refines` now closes a stated restricted
branch of the fifth root.  Eight calls used exactly 267.381 s (two green): run
`20260731Tscheduler-delay-until-nodelay-05-all-method` first checked the exact
source state in 33.522 s, and final run
`20260731Tscheduler-delay-until-nodelay-08-readback` checked the refinement in
34.100 s.  The boundary fixes source suspension depth 1, a guarded previous
wake pointer, critical/interrupt flags 0, the no-delay arithmetic branch, and
a non-wrapping yield count.  Internal depth is 1 -> 2 -> 1; the source commits
the nominal wake and increments the proof-port yield count once, without
blocking the current task or migrating a list node.  Its hash is
`44C6CF2B014D9BB9D2F47D4770246457DD0EFCB3850FB2D52B6301FAF19A51EB`.

This raises the checked source-to-abstract theorem count to exactly eleven:
three fixed list simulations (empty insert-end, singleton removal, and empty
ordered insertion), general-N member removal, general-N fresh insert-end,
their general remove-then-insert-end composition, and one restricted theorem
for each of the five scheduler roots.  The eleven theorems cover eight distinct
operations because ordered insert adds one operation, while the sequential
theorem adds no operation and insert-end/remove retain fixed and general cases.
All five scheduler roots are now refinement-green at their stated narrow
boundaries.  Positive-delay source refinement, the concrete P2 preimage, the
blocking/list-migration delay-until branch, unlocked switch/increment,
general/nonempty ordered insertion, and the full initialise -> initialise-item
-> insert-end -> remove construction path remain open.  The target decision
therefore stays conditional.

The raw operational insert/remove paths, general insert/remove, their checked
remove-then-insert composition, and the three fixed correspondence cases are no
longer in doubt, but they and the five narrow scheduler boundaries do not pass
the full acceptance gate.  If the remaining initialisation-chain construction
cannot be checked against untouched C without changing source behaviour or
weakening C validity, the target switches.  Merely using
`skip_heap_abs`,
`no_heap_abs`, or an ignored addressability error is not accepted without the
full nonempty needle and broader correspondence evidence.

## Historical P2 positive-delay decision update (superseded)

The conditional positive-delay acceptance needle is now checker-green.  The
artifact-specialized generated `vTaskDelay' 2` body executes through exact suspend, remove,
wake-key write, delayed-A insertion, quiet resume, and yield states.  The pure
postrelation checks all eight list roots plus decoder, role, scalar, current,
and boundary components, and the final corollary relates the source result to
`task_delay_abs 2 p2_pre`.

The three final runs, all with `quick_and_dirty=false`, are:

- `20260801Tscheduler-p2-delay-source-09-canonical-states`, exit 0,
  35.056 s;
- `20260801Tscheduler-p2-post-relation-09-nat-index`, exit 0, 38.618 s;
- `20260801Tscheduler-p2-delay-refinement-04-final-heap`, exit 0,
  39.603 s.

The decision label is therefore:

> Conditional generated-source refinement theorem: green; concrete
> frozen-build-layout P2 non-vacuity witness: open.

The remaining non-vacuity gap is not an SMT or symbolic-execution obligation.
The CParser theory leaves addressed data-global locations unconstrained, while
the available `all_distinct` locale covers function addresses only.  A legal
HOL interpretation may therefore make the list roots null or overlapping.
Closing the deployment-instance claim requires an artifact-bound data-layout
certificate for one exact source/configuration/toolchain/linker-script/ELF
tuple.  A synthetic address witness would show logical satisfiability but not
that the frozen ELF has that layout.
