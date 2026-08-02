# Blind reconstruction: FreeRTOS V6.1.1 scheduler

Status: `SEALED_BLIND_MILESTONE__EXACT_REFINEMENTS_13__DISTINCT_OPERATIONS_8__SEQUENTIAL_COMPOSITIONS_2__FROZEN_P2_PREIMAGE_GREEN__FOUR_CALL_HARD_GATE_GREEN`

This experiment independently reconstructs an artifact-specialized
CParser/AutoCorres2 generated-source refinement of a scheduler-related slice of
FreeRTOS V6.1.1.  The original VCC annotations,
Z models, abstraction relations, invariants, and proof scripts remain sealed
until a checker-green blind result has been committed and hashed.

## Sealed blind milestone (2026-08-01)

The formerly open frozen-layout/non-vacuity gate is now closed for one exact
artifact-bound P2 witness.  The portable identity is:

| Evidence object | SHA-256 |
|---|---|
| frozen ELF32/i386 artifact | `DC830E50513384D712E0D1C68CB198EA656365F673D021C452D7D7EBD45C045A` |
| extracted layout ledger | `CA288A4CD2344BE979ADFA9DBF0298C6715F196D64AE472D173304289C4F2C02` |
| generated addressed-global configuration | `27F74768E1DB1C3F8DBFCFC85371075192BB7D2544ED324DC81B65A9A2911712` |

The artifact builder extracts and independently relink-checks the ledger, and
the generator validates the configuration against that ledger.  Isabelle then
consumes the six addresses as CParser definitions.  This ELF-to-ledger-to-
configuration correspondence is a hash-locked external evidence check, not an
Isabelle theorem or a source-to-binary proof.

Exactly six addressed-data bases derive nine pairwise separate static
`xLIST` regions: four ready-array elements and five standalone lists.  The P2
relation uses eight roots; the ninth termination-wait region remains in the
exact CParser address map and separation proof.  The P2_IDLE and P2_RUN TCBs
are fresh logical runtime heap objects, separated from all nine static
regions.  They are not fixed-address ELF symbols and make no allocator or boot
reachability claim.

`frozen_p2_artifact_bound_seal` constructs a concrete logical preimage at
`StableRunning` and composes it with the artifact-specialized generated
`vTaskDelay' (2 :: 32 word)` result.  The checked endpoint is
`YieldPending`, related to `task_delay_abs 2 p2_pre`; the exact-state path is
suspend, ready-list removal, wake-key write to 7, delayed-list insertion,
quiet resume, and one proof-port yield request.

The literal hard-gate chain is also closed.  Theorem
`raw_vListInitialise_insert_end_remove_refines` executes
`vListInitialise' -> vListInitialiseItem' -> vListInsertEnd' ->
vListRemove'` with no theorem assumptions and exactly three
`runs_to_bind` compositions.  Its final state refines remove-after-insert from
an initial empty abstract list; the clean corollary returns to an empty
relation.  This theorem deliberately makes no eight-byte trailing-frame
(`tail8`) claim.

The sealed count is **13 source-to-abstract refinement theorems, 8 distinct
source operations, and 2 sequential compositions**.  The final portable
replays all used `quick_and_dirty=false`, exited 0, and did not time out:

| Gate | Run | Seconds |
|---|---|---:|
| artifact-specialized scheduler parse | `20260801Tseal-scheduler-parse-01-portable` | 23.566 |
| ordinary split-heap no-go | `20260801Tseal-p2-layout-no-go-01-portable` | 33.162 |
| nine-region static geometry | `20260801Tseal-p2-static-nine-01-portable` | 27.701 |
| runtime-TCB dynamic geometry | `20260801Tseal-p2-dynamic-all-nine-01-portable` | 27.467 |
| concrete P2 preimage and seal | `20260801Tseal-p2-preimage-06-parenthesised-seal` | 120.854 |
| literal four-call list chain | `20260801Tseal-list-four-call-01-portable` | 32.338 |
| stock list translation smoke | `20260801Tseal-list-smoke-01-portable` | 67.973 |
| raw `skip_heap_abs` list translation | `20260801Tseal-list-raw-skip-01-portable` | 22.551 |
| capstone theorem-object assumption audit | `20260801Tseal-assumption-audit-01-portable` | 137.387 |

A dedicated leaf session audits the five capstone theorem objects.  Each has
empty `Thm.prems_of` and `Thm.hyps_of`, no `Pure.imp` or `HOL.implies` anywhere
in its proposition, and zero sort hypotheses.  Thus the sealed capstones retain
no function-address, addressed-data-global, or generated `G`/`S` locale
premises.  The fail-closed method and exact hashes are in
[`ASSUMPTION_AUDIT.md`](ASSUMPTION_AUDIT.md).

The milestone does not establish allocator correctness, boot or
scheduler-start reachability, context-switch execution after the pending yield,
compiler correctness, machine-code correctness, binary/source equivalence,
or full-scheduler functional correctness.

## Historical progress record

The chronology below is retained as an audit trail.  Statements that a frozen
layout, concrete P2 preimage, or four-call construction was "open" describe
their checkpoint at that time; the sealed evidence above supersedes them.

### Former conditional P2 positive-delay checkpoint (superseded)

The artifact-specialized generated `vTaskDelay' (2 :: 32 word)` body now has a checker-green
exact-state theorem.  It composes exact suspend, singleton ready-list removal,
the generated wake-key write to 7, delayed-A ordered insertion, quiet resume
returning 0, and the proof-port yield.  Run
`20260801Tscheduler-p2-delay-source-09-canonical-states` was exit-zero in
35.056 s with `quick_and_dirty=false`.

The pure postrelation layer separately checks all eight physical list roots:
ready0 preserves the P2_IDLE singleton and its whole item, ready2 becomes
empty, delayed-A becomes the P2_RUN wake-7 singleton, and ready1/3,
delayed-B, pending, and suspended remain empty.  Run
`20260801Tscheduler-p2-post-relation-09-nat-index` was exit-zero in 38.618 s.
The final assembly also proves decoder, roles, scalars, current task, and
boundary facts, then connects the source execution to
`task_delay_abs 2 p2_pre = p2_post`.  Run
`20260801Tscheduler-p2-delay-refinement-04-final-heap` was exit-zero in
39.603 s.  The principal theorems are
`scheduler_vTaskDelay_2_p2_exact_state`,
`p2_remove_wake_insert_lists_rel`, and
`scheduler_vTaskDelay_2_p2_refines_task_delay_abs`.
The corresponding theory SHA-256 values are
`7BFB623FE099104EA4276D0119CCD6C7B23A0F94ABF04B87FAAFAF3AEB1DD6C0`,
`CF5CCB728150BC4B185CEAE448E9E2FAB0C9C88E1CCBCDA1F79E2A67AD7375B8`,
and `43BC41254C609DF8302F38113F662912E2FD99C72D0A612E5A72925E5AA1C9E7`.

Before the first repository publication, the four CParser root theories were
made clone-location independent by resolving `scripts/cpp-wsl.sh` from each
theory's master directory.  The current scheduler parse theory is green in
run `20260801Tpublish-portable-scheduler-parse-01` (82.094 s; SHA-256
`BA286C0091DF4BEE9D4DCB8013A5E3903DEE054357E6012968C459D1ED51BA68`).
Run `20260801Tpublish-portable-refinement-02` then replayed the current
dependency closure through
`EAL6_FreeRTOS_V611_Scheduler_P2_Delay_Refinement` in 385.146 s with exit 0,
no timeout, and `quick_and_dirty=false`.  Its status and stdout SHA-256 values
are `6D45F563CB84212812C59F5A723DD17177E03FF36328D6FFAF96AAA3FAB78B5E`
and `594A6C89502091A013CB9A6D71EDC6DB1AB76A5C174D869F15DB2687F4B95C89`.

This is a conditional generated-source refinement theorem.  Its
`scheduler_endpoint_rel + p2_source_footprint` precondition is not yet tied to
one frozen linked FreeRTOS build.  The addressed data-global constants remain
unconstrained by the current translation's function-address locale, so a
frozen-build data-layout certificate and concrete P2 non-vacuity witness are
still open.  A generic SMT backend or a second symbolic executor would not
close that missing layout fact.

The target becomes final only if the frozen physical C dependency slice is
between 500 and 800 lines and an unmodified-source CParser/AutoCorres2 smoke
test succeeds using only configuration headers and audited external contracts.
Otherwise the experiment records a `TARGET_GATE_FAIL` and changes target
before any original proof artifact is opened.

Current evidence clears the size gate and the hardest list-front-end risk:
the manifest independently reproduces **670 physical / 587 nonblank / 458
nonblank-noncomment** upstream lines, and the unmodified stock `list.c` is
checker-green through CParser/AutoCorres2 with `quick_and_dirty=false`.  The
embedded mini-sentinel prefix alias is retained with the formal
`addressable_fields = xLIST.xListEnd` mechanism.  A nine-state executable
trace supplies five invariant-killing witnesses, and a one-link removal mutant
is killed by the unchanged shape oracle.  The translation gate has now exposed
a stricter non-vacuity blocker: checker-green theorems show both that an
`xLIST_C` root and the cast `xLIST_ITEM_C` root at its embedded sentinel cannot
satisfy the split-heap validity guards together, and that the corresponding
heap-lifted `vListInsertEnd'` has no run.  The candidate therefore fails its
split-heap M0 gate.  An isolated official `skip_heap_abs` translation is
nevertheless green and retains raw `c_guard`/heap semantics without changing
upstream source; it has no `root_ptr_valid` conflict.

The independently rerun scheduler source trace
`20260731Tscheduler-trace-02-independent` is the final reproducibility
evidence for executable invariant discovery.  In 5.621 s it passed bounded
compile, trace, and analysis gates (`0/0/0`) over four scenarios, producing 39
records, 13 full snapshots, 25 successful checks, and no fatal record.  Its
harness, runner, proof-port, upstream-source, binary, trace, and analysis
hashes are identical to the initial run.  The trace observes that tick wakeup
and context selection are separate transitions, that wrap swaps delayed-list
roles without moving their nodes, and that same-priority choice is relative
to the list cursor.  Run `20260731Tscheduler-trace-01` alone additionally had
a separate manual ASan/UBSan compile-and-run check; that sanitizer result is
not attributed to the independent rerun.  These are source-execution
witnesses and invariant killers, not a machine-checked scheduler refinement.

A focused tooling run now exercises both positive-delay arithmetic branches
without promoting executable evidence to refinement.  Run
`20260731Tscheduler-trace-03-delay-phases` completed compile/trace/analysis
with exits `0/0/0` in 6.097 s and produced 57 records, 17 snapshots, 39
successful checks, six scenarios, and no fatal record.  It observes the
stable-running versus yield-pending phase boundary, non-wrapping insertion
into the current delayed list, wrapping insertion into the overflow delayed
list without prematurely swapping list roles, preserved tick/current-task
identity until the port switch, and exactly one yield request.  The harness
and runner SHA-256 values are
`9B9BD5D73AFBBCB7715016A8A1A1D9A2FF8A14471FBBE31CF2EA70205D5123A7`
and
`1D855DF45BBBB009725AED8C203D8FE529D6EEF8EEA5D88F10FF492121C0DD84`.
This is executable invariant-discovery evidence, not an Isabelle theorem.

The raw route has now passed R0--R4 for exact empty and singleton witnesses.
After the guard and initialisation rungs, run
`20260731Tlist-raw-r3-master-01` checks
`raw_vListInsertEnd_empty_master` with `quick_and_dirty=false`: the source-
derived raw `vListInsertEnd'` reaches `Result ()` from the recorded empty-list
and fresh-item prestate, produces count 1 and cursor-at-item, establishes the
two sentinel links, two item links, and container pointer, preserves the key
and owner, preserves every byte in the eight-byte over-read tail and the far
canary, and leaves heap typing unchanged.  The master is a mechanical
conjunction of separately checked postcondition groups; it does not rerun a
monolithic VCG.

Run `20260731Tlist-raw-r4-master-01` then checks
`raw_vListRemove_singleton_master` in 38.229 s with exit 0,
`quick_and_dirty=false`, and no timeout.  From a separately encoded singleton
prestate, the source-derived raw `vListRemove'` reaches `Result ()`, changes
count from 1 to 0, repairs `pxIndex` to the sentinel, makes both sentinel links
self-links, and clears the item's container.  Faithfully to the source, the
detached item's next/previous links remain pointed at the sentinel; its key and
owner, the eight-byte tail, the far canary, and heap typing are preserved.  The
master mechanically conjoins five previously checked groups and does not reopen
the generated C body.  Its theory SHA-256 is
`6F7F2107DD62B00D8541DA2E3C449452AD70A5E291DBC31D835B6819EE998E54`.

R0--R4 remain concrete raw operational evidence rather than refinement.  R5
now adds the first genuine, deliberately narrow source-to-abstract theorem.
Run `20260731Tlist-raw-r5-10-show-thesis` checks
`raw_vListInsertEnd_empty_refines` in 25.236 s with exit 0,
`quick_and_dirty=false`, and no timeout.  The separately checked
`raw_insert_end_prestate_rep_empty` relates the fixed concrete empty witness to
`raw_empty_abs`; the source-derived raw `vListInsertEnd'` then reaches
`Result ()` and a heap related by `raw_xlist_rel` to
`list_insert_end_abs raw_item_ptr k (raw_empty_abs keys)`.  The checked theory
SHA-256 is
`5CD5EF0B3850FEBD712664EA375ED04E3BDDD2C8B80B9AEA75EBDF006613A199`.

The second genuine source-to-abstract theorem is the fixed
singleton-to-empty removal.  `raw_singleton_prestate_rep` gives the concrete
singleton a non-vacuous `raw_xlist_rel` preimage, and
`raw_vListRemove_singleton_refines` relates the source-derived removal result
to `list_remove_abs`.  Run `20260731Tlist-raw-r5r-02-remove-refinement` is
exit-zero in 35.741 s with `quick_and_dirty=false` and no timeout.  The two
remove-refinement calls total 80.967 s: the first 45.226 s call was red only in
the final refinement proof while its prestate leaf was green; the second is the
final green call.  The prestate and refinement theory SHA-256 values are,
respectively,
`FE1DF5B644267CD33E6C5E6962144684BDF3EC0A3E3E62DA3701D09AEAF49AF7`
and
`4187C45D7E870E77A3EC009B0D1424597BFF9FEBB84A850D59FF4DB6C6FF653F`.

Later checker-green layers prepare the general-N list proof without being
counted as source-to-abstract refinement.  First, the R5 cycle theory derives finite-cycle
indexing, first return, no early return, injectivity, and exact reachability
from `raw_ring_links`/`raw_xlist_rel`.  Its four calls cost exactly 113.138 s
(three red, one green); final run
`20260731Tlist-raw-r5c-04-nth-append` took 24.581 s with
`quick_and_dirty=false`.  Its theory SHA-256 is
`E4C7B971C69464B29C1ED2EE4B20D0E87B1A329F80E960AAE14A779F442E4F3E`.

R6 then removes the fixed-address guard scaffolding.  Run
`20260731Tlist-raw-r6gp-01-generic-prefix` checks the address-parametric
mini-sentinel/full-item prefix bridge in 35.260 s; its theory SHA-256 is
`281703B2FDEDEC5756C5F01127F4DFE4FB367F9E9F7C72CFD7A56FCDE6A1CD85`.
The dynamic-guard layer derives cycle closure and all pointer guards needed at
the entrances to future general-N insert/remove VCGs.  Its six calls cost
exactly 151.292 s (five red, one green); final run
`20260731Tlist-raw-r6dg-06-imageI` took 23.831 s with
`quick_and_dirty=false`.  Its theory SHA-256 is
`82D4F9E75A801E4D433346F85B5B32FE59BDE1992F70A2BE67283CC1A68A1758`.
These are representation, reachability, layout, and guard lemmas—not an
execution of a source-derived operation and not source-to-abstract operational
refinement.

R6 now has a positive general-remove execution brick as well.  Across 13
calls, `List_V611_Raw_R6_Unlink_Locality` cost exactly 341.606 s (four green);
final run `20260731Tlist-raw-r6ul-13-general-remove-direct-exact` took
26.303 s.  Its theorem `raw_vListRemove_general_result` opens the generated
`vListRemove'` body and proves normal `Result ()` execution under
`raw_xlist_rel`/membership assumptions.  It does not state an abstract
poststate, so it is positive execution rather than refinement.  The theory
SHA-256 is
`7EA7C1094272F35FF5D80A58D89D588F180617BF3ED679371CBCEE887A2D3BBF`.

The insert and remove postrelation assemblers remain pure Isabelle relation
lemmas.  Remove took seven calls and exactly 306.099 s (two green); final run
`20260731Tlist-raw-r6rr-07-count-transfer` took 26.641 s and added the explicit
word-count transfer used by `raw_xlist_rel_removeI`.  Its current theory hash
is `4CE9BE41FC318FCF2919BCAC2F72B7CED73833BA3DC37980D92B827A429687CF`.
Insert took three calls and exactly 86.850 s (one green); final run
`20260731Tlist-raw-r6ir-03-live-cases` took 25.600 s and its theory hash is
`9022271DAB3CE824CBE19C5D2DBB1EF2AC4295D6CFACD0BA6F6E6B3D061A204D`.
Neither theory opens generated C.

The alias-safe unlink projection layer was developed in four calls totalling
114.016 s (three green).  The first two green runs established same-node and
cross-node/sentinel field frames; after one red strengthening attempt, final
run `20260731Tlist-raw-r6up-04-two-write-where` took 27.420 s and also checked
the combined two-write effect and ring-link deletion.  Its current theory hash
is `8581095989FC3ED46DE8BA4E9A6FFEB12BE0A016E6076313E40699C8C2A62712`.
This is pure alias/projection reasoning: it opens neither a generated C body
nor an abstract operation and contributes zero refinement theorems.

The general-N removal pipeline is now closed.  Its six stages used 44 checker
calls, 14 green, and exactly 1309.315 s: metadata/effect assembly used 18 calls
and 490.788 s; the single exact source-heap-effect stage used nine calls and
324.541 s; index, payload, and topology projections used respectively
6/187.597 s, 4/109.881 s, and 6/158.988 s; the final assembler was green on
its first 37.520 s call.  The key source certificate
`raw_vListRemove_general_heap_effect` symbolically executes the generated C
body once and gives the exact concrete byte-heap transformer.  The later
index/topology/payload stages project that certificate without reopening the
source VCG.  The pure theorem `raw_remove_effect_refines` then turns the
assembled effect into the final representation relation.

Run `20260731Tlist-raw-r6rgr-01-assemble` checks
`raw_vListRemove_general_refines`: for any concrete heap related by
`raw_xlist_rel` and any `p` in `set (ring xs)`, source-derived
`vListRemove' p` reaches `Result ()` and a heap related to
`list_remove_abs p xs`.  This is genuine general-N member-removal refinement,
not a fixed witness; its theory SHA-256 is
`A08443F3DC4B2CB828D8089AC41BC4F59C004C38E98257A07B9B607E2F039B6A`.
The nonmember case is outside the theorem's API precondition.

General-N insert-end is now closed as a second general list refinement.  The
supporting source-effect run `20260731Tlist-raw-r6ise-01-first` was green on
its first call in 27.544 s.  It checks
`raw_vListInsertEnd_general_heap_effect`, which opens the generated source body
once and fixes the normal result plus the exact seven-stage
`raw_insert_concrete_heap` transformer.  This certificate is registered as a
supporting non-refinement layer with zero theorem-count delta; its theory
SHA-256 is
`38D21F5E8D283FD8938912C23F3D271A8CEFB7FA3640D4EE7CA61A806149BC0D`.

The pure post-transformer development then used four calls and exactly
151.579 s (three red, one green).  Final run
`20260731Tlist-raw-r6ipt-04-where-spacing` took 36.401 s with
`quick_and_dirty=false`.  Theorem
`raw_vListInsertEnd_general_refines_via_transformer` maps source-derived
`vListInsertEnd' lp p` through `raw_xlist_rel` to
`list_insert_end_abs p (raw_key_at h p) xs` for any represented list, a fresh
item, and `raw_count_can_increment xs`.  Across source-effect support and
post-transformer assembly the insert pipeline used five calls, two green, and
179.123 s.  The final theory SHA-256 is
`E83219F8F59CBF18A6BB4050A3E8F380F586BD5B237AD0EE2857D7635846959C`.

The general remove-then-insert-end sequential needle is now checker-green too.
Its seven-call development used exactly 237.172 s (three red, four green);
final run `20260731Tlist-raw-r6ris-07-bind-weaken` took 31.956 s with
`quick_and_dirty=false`.  Theorem
`raw_vListRemove_insert_end_general_refines` maps
`bind (vListRemove' p) (\<lambda>_. vListInsertEnd' lp p)` from any
`raw_xlist_rel` state and member `p` to `list_insert_end_abs` applied after
`list_remove_abs`, using the item's original concrete key.  The composition
reuses the two checked general refinements without reopening either generated
C body.  Its three explicit bridges establish that removal makes `p` fresh,
that the shortened ring has count headroom, and that removal preserves `p`'s
key.  The final theory SHA-256 is
`E12FDC4BA9A08F62C2C8F0C8493657CECE41FEE88D8B14F11360738E65B85A9D`.
Chronologically this is strict source-to-abstract theorem #10, with a zero
distinct-operation-count delta.

The two earlier list theorems remain deliberately fixed: empty-to-singleton
insert and singleton-to-empty remove both have
`general_operation_refinement=false`; they remain separately counted even
though the general theorems now cover their operations.  The checked sequence
is specifically general member removal followed by insert-end of the same
item; it does not yet supply the longer concrete initialisation-chain witness
in the hard acceptance gate.

Restricted empty-list ordered insertion is now checker-green as a third fixed
list case.  The source-effect development used 18 calls, five green, and
exactly 534.339 s.  Final run
`20260731Tlist-raw-r6ois-18-transformer-end-frame` took 39.848 s with exit 0
and `quick_and_dirty=false`.  Its unified theorem
`raw_vListInsert_ordered_empty_heap_effect` covers both the maximum-key special
branch and the nonmaximum loop-free branch of source-derived `vListInsert'`,
yielding the exact `raw_ordered_insert_empty_heap` transformer.  This source
layer is not refinement and has zero theorem-count delta.  Its theory, status,
and stdout SHA-256 values are respectively
`238178DDF2C973ABF1D2B80B98EAA475D39C89B3DEED16F118480F3A82E681C9`,
`ADE3AAC35F3DCD7FBEE30E12B64AE67009E9E0F7F307FE97AD7D3C708C4AD7FB`,
and `823A32FA6F3CC9A1A39B33724AD5AB77D0001A2B65EF1405453995B901480435`.

The three-call postrelation assembly then used exactly 167.993 s (one green).
Final run `20260731Tlist-raw-r6oier-03-key-let` took 89.835 s with exit 0 and
`quick_and_dirty=false`.  Public theorem
`raw_vListInsert_ordered_empty_refines` maps `vListInsert'` to
`list_insert_ordered_abs` from an empty represented ring, a fresh item, and a
maximum-key sentinel.  Corollary
`raw_vListInsert_ordered_empty_refines_ordered` preserves the strengthened
ordered relation, while `raw_vListInsert_ordered_empty_max_refines` isolates
the maximum-item-key special branch.  This is an empty-to-singleton branch,
not general/nonempty ordered insertion; it is recorded with
`general_operation_refinement=false`.  The theory, status, and stdout hashes
are respectively
`8319D39955FACD488B1409C1CFABBC021E8332A3A3F52645C4A88BDE50413806`,
`69B11F9B55CF4518EC6B570D5F085C81AC7629E0CABB6118E935A9B3EBCBC265`,
and `91801D97F2C08C506E3BC75753C3AADE4846B5902DEB05D2DD77BCC497F8F0CB`.
Across source effect and refinement the ordered-empty pipeline used 21 calls,
six green, and 702.332 s.  It contributes strict theorem #11 and makes
`vListInsert` the eighth distinct refined source operation.

The independently reconstructed pure `xList` model is checker-green as a
separate M0 result.  Its canonical theory graph is
Definitions -> Sequence Lemmas -> Predecessor/Removal Lemmas -> Operation
Invariants -> executable witnesses.  Run `20260731Tmodel-13-sequential`
finished with exit code 0 in 13.058 s under `quick_and_dirty=false` and
`parallel_proofs=0`; the session database records no errors.  This establishes
the internal abstract-model preservation lemmas.  R5 now connects its empty/
singleton fragment to the fixed insert and remove source transitions; R6 now
additionally connects arbitrary represented member removal and fresh
insert-end, plus the restricted empty ordered-insert branch.

The five scheduler roots now also have a checker-green pure endpoint model:
`task_delay_until_abs`, `task_delay_abs`, `task_increment_tick_abs`,
`task_switch_context_abs`, and `task_get_tick_abs`, together with `core_wf`,
`settled_wf`, and basic endpoint facts.  Across five calls, four red and one
green, the session cost exactly 156.511 s; final run
`20260731Tscheduler-abs-05-let-def` took 45.724 s with
`quick_and_dirty=false`.  The theory SHA-256 is
`FE22AA8F2850CDCD777D89E1D6CD3880DCD9D9524A75DCACF97B46839B98D1DE`.
This pure theory contains no raw heap, TCB pointer, generated C program, or
representation relation.  It therefore adds zero source-to-abstract
refinement theorems.

A separate pure P2 witness now checks the positive-delay phase boundary of the
abstract model.  Across six calls it used exactly 115.266 s (two green); final
run `20260731Tscheduler-p2-06-post-witness` took 12.597 s with exit 0 and
`quick_and_dirty=false`.  Theorem `task_delay_abs_2_p2` establishes the stated
two-tick transition from `p2_pre` to `p2_post`; `p2_pre_settled` establishes a
settled prestate, while `p2_post_core` and `p2_post_not_settled` establish that
the poststate retains `core_wf` but is intentionally not yet settled.
`p2_post_phase_observations` records the tick, current task, emptied ready
queue, delayed membership/wake key, and pending yield.  This theory has no raw
heap, generated C state, concrete preimage, or source relation, so it adds zero
strict rungs and zero distinct refined operations.  Its theory, status, and
stdout hashes are respectively
`FB03C1FDE6BEC66357F4E7185838423B8867D8999E2CD1422CF2064DC0C48236`,
`4C0F092CD72DD4C984F8520740D6C0BC71B389244A18104760485E391229F050`,
and `8CBE80095AD95274AA84A6D0469ABC52F0930A991771C8FA0D623D3878480B76`.

The scheduler C front end is now checker-green through the raw-heap route.
The historical parse run `20260731Tscheduler-parse-01` took 50.663 s; the
pre-portability theory SHA-256 recorded by that run is
`353A991C993A16F33D197E51709D39958DA8F64672AC82D1E14CBDDB127BBF09`.
The first tick attempt exposed the split-heap route in a 56.917 s red run;
final `skip_heap_abs` run `20260731Tscheduler-tick-02-raw-heap` took 21.777 s,
for 78.694 s across two calls, and its theory SHA-256 is
`7299537CA9D94A6B292F308114250F99AF435F3E891CB62407411AE67071E291`.
Delay/support run `20260731Tscheduler-delay-01-raw-heap` took 44.158 s with
theory SHA-256
`D34512E4642779C49BF412E7FF05E4FB622EF47E255F152AA1CB765E7EA89A68`;
remaining-roots run `20260731Tscheduler-roots-01-raw-heap` took 45.959 s with
theory SHA-256
`B560345AB2B38ADC871060A33E7A850E8603C8CC5DADFD6D1945A2FD2C3A3E7B`.
All four final gates have `quick_and_dirty=false`.  They establish raw-heap
CParser/AutoCorres translation only and contribute no refinement theorem.

The scheduler/raw-list reuse support is now separately checker-green without
being promoted to source refinement.  `Scheduler_Raw_List_Relabel` supplies an
explicit decoder from raw pointer node identities to scheduler Generic/Event
identities, plus empty, ready-singleton, and ordered-singleton facts.  Its two
calls used exactly 57.276 s (one green); final run
`20260731Tscheduler-relabel-02-intro-disambiguate` took 29.046 s.  The current
theory SHA-256, verified after the run, is
`3EED28E0FA3ADC44682E4ABE32569A4D2BDC1FA3392F693E7DA07578A2F129AA`.

The generated-layout diagnostic used four calls, one green, and exactly
236.199 s; final run `20260731Tscheduler-p2-layout-first-04-green` took
58.491 s.  It confirms a common byte-heap carrier of effective type
`32 word -> 8 word`, but distinct scheduler and raw-list generated `xLIST_C`
and `xLIST_ITEM_C` universes.  Direct scheduler-pointer reuse is therefore
ill-typed.  The diagnostic defines no relation and proves no footprint
theorem.  Its final theory SHA-256 is
`604A4BCCE04F39AFC499A3F58BC9DD65F7E31A57CA8AB526467DB645FFA8F843`.

The translation-unit ABI bridge plan remains a static design artifact with
zero checker calls; it is not retroactive build evidence and is not fully
implemented.  Its SHA-256 is
`40B17DFB17C82FEE8869B45679B664CB595B98872E09FA0E8EA55AAC56231F6C`.
The subsequent bounded ABI foundation is separately checker-green: all three
calls were green and cost exactly 112.143 s, with final run
`20260731Tscheduler-list-abi-03-packed-hval` taking 23.281 s.  Its 36 named
facts cover pointer-address/equality/NULL laws, generated size and alignment,
guards and regions, selected root and embedded-item addresses, field offsets,
the sentinel address, and packed `h_val` reads across the two struct
universes.  The theory SHA-256 is
`2F9CB0E2D0CE2D99E40AF25C1CDAB75DD8C7FB68018BFBA8E8CD8671427F5434`.

The separately checked Stage-D field-write bridge used two calls, both green,
and exactly 42.023 s.  Final run
`20260731Tscheduler-list-abi-write-02-pointer-fields` took 20.882 s with
`quick_and_dirty=false`.  Its 13 lemmas cover the nested Generic-item wake-key
field plus next, previous, container, index, and count addresses and
arbitrary-intermediate-heap writes; pointer-valued writes use an explicit
phantom-type coercion theorem.  The theory SHA-256 is
`C972FA5B4CAFCC230056DBA267EC6581B144E93C4BDFCED7015CDB0399AED76A`.

The first layered scheduler/raw representation relation is also separately
checker-green.  Eight calls used exactly 251.043 s (four green); final run
`20260731Tscheduler-p2-raw-rel-08-empty-extractors` took 28.897 s with exit 0 and
`quick_and_dirty=false`.  `Scheduler_P2_Raw_Relation` defines generated roots,
exact forward/reverse TCB and Generic/Event decoder laws, the eight list views,
role/scalar/current/boundary layers, `raw_scheduler_rel`, and the
StableRunning/YieldPending endpoint split.  Lemma
`p2_pre_ready2_raw_singletonE` extracts the exact raw ring and cursor pointer
for P2's running ready-list item; `sched_xlist_rel_emptyE` and the delayed-A
and pending corollaries extract the required empty raw witnesses.  Theorems
`p2_pre_conditional_endpointI` and `p2_post_conditional_endpointI` remain
conditional introductions: they do not construct a concrete heap preimage or
execute `vTaskDelay'`.  The theory, status, and stdout hashes are respectively
`9A153B79D0871D4D96A5DF82299EF0D40AC8F918692FE60934A8245E048510ED`,
`7A83BA7B439CB940D177F6EADF50AC020CA4DF997B7B95B77A0E6F8373DAE039`,
and `EF920019DA793E1CB1F04430A1CAF807C8EF025BFA3172546A42133914AA4276`.

Neither relabelling, the layout diagnostic, the static plan, the ABI
foundation/write brick, nor this conditional relation layer opens a scheduler
source body or establishes a source-to-abstract operation.  Together they add
zero strict rungs and zero distinct refined operations.  A positive-delay
`vTaskDelay'` source theorem and a concrete P2 preimage both remain open.

The first genuine scheduler source-to-abstract theorem is now green.
`scheduler_tick_boundary_rel` fixes the quiescent API boundary to critical
depth 0 and interrupts-disabled flag 0, and equates committed source
`xTickCount` with abstract `sa_tick`.  Theorem `xTaskGetTickCount_refines`
relates source `xTaskGetTickCount'` to `task_get_tick_abs`: it returns the
committed tick and preserves the boundary relation.  It deliberately does not
return `sa_missed_ticks`, because the source API reads `xTickCount` rather than
the deferred-tick debt.  The three refinement calls cost exactly 72.610 s
(23.799 s red, then 24.488 s and 24.323 s green); final run
`20260731Tscheduler-tick-refine-03-explicit-model-op` has
`quick_and_dirty=false`.  The theory SHA-256 is
`99D46C2193DD213CF6D4645D48A4F93F18B50CA8887BA1ABC74255BF77094BCA`.

Two further scheduler roots now have deliberately restricted refinement
theorems.  Run `20260731Tscheduler-switch-suspended-01` checked
`vTaskSwitchContext_suspended_refines` on its first call in 36.548 s.  Under
nonzero suspension depth, `scheduler_control_rel` maps the source update
`xMissedYield := 1` to abstract `sa_missed_yield := True`; the branch neither
reads a ready list nor invokes the proof-port yield.  The theory SHA-256 is
`E6907500EEE776183F11178EEDDC095E6DE92E14CB7C23A8F382C2B16C685D4A`.

Run `20260731Tscheduler-increment-tick-suspended-01` checked
`vTaskIncrementTick_suspended_refines` on its first call in 36.297 s.  Its
boundary requires nonzero suspension depth and explicitly assumes that the
concrete 32-bit missed-tick counter does not wrap.  The source increments only
`uxMissedTicks`; the abstract operation increments `sa_missed_ticks`, while
the committed tick stays fixed and delayed lists are not inspected.  The
no-wrap premise is necessary because the concrete counter is a word whereas
the abstract debt is a natural number.  The theory SHA-256 is
`06077C3FCD1F17C07694437957C7D4AA5CB94D68C056B3BC80B9E3B73F60F098`.

The zero-delay branch of a fourth scheduler root is now checker-green.  The
first call was red after 33.218 s because of a redundant proof tactic; final
run `20260731Tscheduler-delay-zero-02-vcg-solved` took 20.619 s, for exactly
53.837 s across two calls.  Theorem `vTaskDelay_zero_refines` is explicitly
restricted to argument 0 and a non-wrapping proof-port yield counter.  Source
`vTaskDelay' 0` performs one proof-port yield-count increment, which
`scheduler_control_rel` maps to `sa_yield_count := Suc sa_yield_count` in
`task_delay_abs 0`; the branch does not suspend the scheduler, access the
current TCB, or touch a list.  It proves no positive-delay source refinement;
the checker-green P2 result above is a pure-model witness only.  The theory
SHA-256 is
`A77DE8F4215AF1EE592858B9232FD8F3EF068D5A2C12C4912C99028FE525D9E4`.

The suspended no-delay branch of the fifth scheduler root is also
checker-green.  Its eight-call development used exactly 267.381 s (two green).
Run `20260731Tscheduler-delay-until-nodelay-05-all-method` first checked the
exact source result in 33.522 s; final run
`20260731Tscheduler-delay-until-nodelay-08-readback` checked
`vTaskDelayUntil_suspended_no_delay_refines` in 34.100 s, both with
`quick_and_dirty=false`.  The theorem starts with source suspension depth
exactly 1, a guarded previous-wake pointer, proof-port critical and interrupt
flags both 0, the arithmetic no-delay branch, and a non-wrapping yield count.
The source's internal suspend/resume depth is 1 -> 2 -> 1; it commits
`*previous_ptr := previous + increment` and performs one proof-port yield,
which `scheduler_control_rel` maps to `task_delay_until_abs`.  This branch does
not block the current task or migrate any list node.  The theory SHA-256 is
`44C6CF2B014D9BB9D2F47D4770246457DD0EFCB3850FB2D52B6301FAF19A51EB`.

The exact source-to-abstract refinement theorem count is now twelve:
three fixed list cases (insert-end empty-to-singleton, singleton removal, and
ordered-insert empty-to-singleton), general-N member removal, general-N fresh
insert-end, their general remove-then-insert-end sequential composition, and
one stated restricted refinement for each of the five scheduler roots, plus
the conditional positive-delay P2 source-to-abstract theorem.  These cover
the same eight distinct operations because P2 strengthens the already-counted
`vTaskDelay` operation.  The blocking/list-migration branch of delay-until,
unlocked switch/increment branches, general/nonempty ordered insertion, the
frozen-build P2 preimage/layout certificate, and the full initialisation-chain
witness remain open.  If the full acceptance needle fails, the target switches
to the frozen fallback before any original artifact is opened.

A post-build scan of all project theory/proof-port/build-script sources found no
`sorry`, `oops`, `admit`, axiom declaration, skip-proof, oracle/cheat, or
`quick_and_dirty=true` pattern.

The work is staged around an end-to-end needle rather than a monolithic proof:

1. freeze source, public requirements, paper allowlist, and hashes;
2. execute concrete scheduler/list traces and extract state deltas;
3. translate the real C and record generated signatures;
4. build an executable abstract state machine;
5. derive the representation relation and invariants from traces and source;
6. prove one non-trivial success path and one unchanged/error path;
7. grow a checked lemma graph to all in-scope operations;
8. seal the blind result, then open the original artifact for comparison.

No scheduler-wide or deployment-instance refinement claim is accepted without
`quick_and_dirty=false`, an exit-zero Isabelle build, a non-vacuity witness,
and a forbidden-pattern scan.  The P2 positive-delay theorem is explicitly
labelled conditional until its addressed-data layout assumptions are
instantiated by a certificate for one frozen linked build.
