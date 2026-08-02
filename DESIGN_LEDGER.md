# Blind design ledger

This ledger separates three kinds of knowledge so that a later comparison does
not mistake paper-derived hints for independent discoveries.

- `SRC`: directly observed in the unannotated V6.1.1 source/comments.
- `REQ`: public FreeRTOS behaviour or a concrete executable example.
- `PAPER`: explicitly stated in the allowed ICFEM 2015 paper.
- `DESIGN`: our proposed Isabelle object, relation, or proof decomposition.

No item below comes from the supplementary proof artifact.

## Final sealed design instance (2026-08-01)

The blind design is instantiated for the frozen ELF/layout/configuration
identity
`DC830E50513384D712E0D1C68CB198EA656365F673D021C452D7D7EBD45C045A` /
`CA288A4CD2344BE979ADFA9DBF0298C6715F196D64AE472D173304289C4F2C02` /
`27F74768E1DB1C3F8DBFCFC85371075192BB7D2544ED324DC81B65A9A2911712`.
The resulting geometry is exact: six addressed C bases, nine static list
regions, and eight P2 relation roots.  The two TCBs are fresh logical runtime
heap objects, not ELF symbols, and their Generic/Event item regions are
separate from every one of the nine static list regions.

The final scheduler witness connects `StableRunning` to the artifact-specialized generated
`vTaskDelay' (2 :: 32 word)` exact source state and ends at `YieldPending`,
matching `task_delay_abs 2 p2_pre`.  This phase boundary preserves the design
choice learned from the executable trace: requesting a yield is not itself a
context switch.

The hard construction design is a literal source-monad chain:

```text
vListInitialise' -> vListInitialiseItem' ->
vListInsertEnd'  -> vListRemove'
```

Its theorem has no assumptions and exactly three `runs_to_bind` composition
steps.  It uses checked list relations rather than adding an unnecessary
`tail8` postcondition; no trailing-eight-byte frame is claimed by this final
chain.

The final accounting is 13 source-to-abstract refinement theorems, 8 distinct
operations, and 2 sequential compositions.  This closes the prior
layout/preimage and construction gates only at the stated source/HOL boundary.
It does not cover allocator or boot reachability, execution of the pending
context switch, compiler or machine-code correctness, binary/source
equivalence, or full-scheduler correctness.

The rest of this ledger is retained chronologically.  Occurrences of
"provisional", "pending", or "open" below record the state when that design
entry was written; the final instance above states which of those gates are
now closed.

## Concrete observations

| ID | Class | Observation | Consequence |
|---|---|---|---|
| C-01 | SRC | `xListEnd` is an embedded `xMiniListItem` cast to `xListItem *`; its prefix fields are used as the ring sentinel. | The C proof must justify prefix aliasing and may not replace the sentinel by a separately allocated full item. |
| C-02 | SRC | `vListInitialise` makes sentinel next/previous self-links, sets the cursor to the sentinel, and sets the real-item count to zero. | Empty is a concrete cyclic heap, not `NULL`. |
| C-03 | SRC | `vListInsertEnd` inserts immediately after `pxIndex` and then moves `pxIndex` to the inserted item. | In the FIFO iteration view, the new element is appended even though its raw ring position depends on the cursor. |
| C-04 | SRC | `vListInsert` walks from the sentinel while the next key is `<=` the new key; `portMAX_DELAY` has a special terminating branch. | Ordered insertion is nondecreasing and stable after equal keys; the maximum-key branch is proof-relevant. |
| C-05 | SRC | `vListRemove` changes the cursor to the removed node's predecessor only when the cursor equals the removed node. | A relation that forgets the cursor cannot prove future round-robin behaviour. |
| C-06 | SRC | A TCB has both a generic list item and an event list item; both may simultaneously have containers. | “Each task belongs to exactly one list” is false. Partition invariants must be stated per list-item role. |
| C-07 | SRC | Delay uses unsigned tick addition and chooses the overflow list exactly when the wake tick is less than the current tick. | The abstraction needs an epoch/overflow interpretation; raw word order is not global time order. |
| C-08 | SRC | Tick wrap swaps the two delayed-list pointers before waking due tasks. | “Current delayed list” is a role carried by a pointer, not a fixed concrete object name. |
| C-09 | SRC | `vTaskSwitchContext` decreases `uxTopReadyPriority` until a nonempty ready list, then advances that list's cursor. | Termination needs a nonempty lower-priority witness (normally idle) and a bound on the priority index. |
| C-10 | PAPER | API calls are treated as atomic boundaries in the allowed case-study model. | Interrupt interleavings inside an API are outside the first theorem and must remain an explicit assumption. |
| C-11 | REQ | In the executable `9 -> 10` wake example, `vTaskIncrementTick` moves the high-priority task from delayed to `ready[3]` and raises `uxTopReadyPriority`, but leaves the low-priority task current; only the following `vTaskSwitchContext` selects the high task. | Tick readiness and context selection need separate abstract transitions and separate simulation lemmas. |
| C-12 | REQ | After same-priority tasks `A,B,C` are inserted, the physical ring is `A,B,C`, the cursor is `C`, and four switches select `A,B,C,A`. | FIFO selection must be defined relative to `pxIndex`, not as unconditional selection of the physical ring head. |
| C-13 | REQ | In the executable `UINT32_MAX -> 0 -> 1` example, the task with key `1` remains in the same physical delayed-list object across wrap; the role pointers swap and the task wakes only at tick `1`. | The representation relation should change role interpretation at wrap rather than postulate node migration. |

## Competing representation relations

### R0: sequence only — rejected

Map every concrete list to one mathematical sequence and forget `pxIndex`.
This can express ordered delayed queues but cannot predict
`listGET_OWNER_OF_NEXT_ENTRY` after insert/remove.  C-03 and C-05 are immediate
counterexamples.

### R1: raw ring plus cursor — retained as the concrete-independent list layer

The `XList_Model_Definitions.xlist_abs` layer records:

- real-node identifiers in sentinel-next ring order;
- a cursor of `None` (the sentinel) or `Some node`; and
- the item key map.

The relation from the AutoCorres heap must additionally state node ownership,
container membership, next/previous mutuality, sentinel prefix validity, count,
and separation from unrelated nodes.

### R2: typed views over R1 — retained as the scheduler-facing layer

- FIFO view: iterate strictly after the cursor, skip the sentinel, wrap, and
  finish at the cursor.  `vListInsertEnd` appends and context switch rotates.
- Ordered view: read from sentinel-next to sentinel-previous.  `vListInsert`
  performs stable nondecreasing insertion.
- Generic membership view: use only the node set and container relation.

The view is selected by a scheduler role (ready/delayed/pending), not by a
ghost type stored in upstream C.

### R3: scheduler relation — historically provisional, now instantiated for P2

The abstract state will contain task IDs, priority, ready FIFOs by priority,
the running task, logical tick/epoch, current and overflow delayed ordered
queues, pending-ready tasks, scheduler-suspension depth, missed ticks, and a
missed-yield flag.  A partial injection maps live TCB pointers to task IDs.

R3 is intentionally split into:

1. `heap_shape`: memory safety, sentinel/ring/link/container/count facts;
2. `list_views`: each concrete role agrees with its R2 abstract view;
3. `task_ledger`: TCB fields agree with task priority and two item roles;
4. `scheduler_roles`: delayed-list pointer roles, ready-array bounds, and top
   ready priority;
5. `observables`: current task, tick, return value, and declared port events.

This factorisation lets symbolic execution report the exact failed layer.

## Raw operational proof staircase

The names `Raw-R0` through `Raw-R3-master` below denote checker rungs over the
raw C heap produced by `skip_heap_abs`.  They are deliberately prefixed with
`Raw-`: they are not the competing representation relations R0/R1/R2 or the
provisional scheduler relation R3 above, and a green raw rung does not advance
those abstraction relations or the source-to-model simulation.

| Rung | Checker evidence | Established fact | Explicit non-claim |
|---|---|---|---|
| `Raw-R0` | `20260731Tlist-raw-r0-05-guards`, exit 0 in 21.774 s, `quick_and_dirty=false` | At the fixed witnesses 0x1000 (list), 0x2000 (detached item), and 0x1008 (cast sentinel), the exact `c_guard` and sentinel-offset facts hold. | No allocated heap, list shape, operation execution, or correspondence relation. |
| `Raw-R1` | `20260731Tlist-raw-r1-05-init`, exit 0 in 23.832 s, `quick_and_dirty=false` | `raw_vListInitialise_exact_post` gives a positive raw `vListInitialise'` result with count zero, index/sentinel fields exact; `raw_vListInitialise_canary_frame` preserves the byte at 0x3000. | This is one concrete construction witness, not a general heap invariant or an abstraction relation. |
| `Raw-R2` | `20260731Tlist-raw-r2-04-init-item`, exit 0 in 22.001 s, `quick_and_dirty=false` | `raw_vListInitialiseItem_exact_post_and_frames` gives a positive item initialisation, `pvContainer = NULL`, frames the other item fields and complete list value, and preserves the 0x3000 canary byte. | It contains no `vListInsertEnd` or `vListRemove` execution and no source-to-`xlist_abs` refinement. |
| `Raw-R3a` | `20260731Tlist-raw-r3a-01-prefix`, exit 0 in 29.643 s, `quick_and_dirty=false` | The cast full-item view and embedded mini-sentinel agree on key/next/previous for arbitrary raw heaps, without a typed-root premise. | Common-prefix read facts only; no operation execution. |
| `Raw-R3b` | `20260731Tlist-raw-r3b-19-selector-frames`, exit 0 in 22.432 s, `quick_and_dirty=false` | Whole-sentinel next/previous updates normalize to the embedded list fields, preserve the other selector, and preserve all eight bytes beyond the real 20-byte list object. | Local heap-update algebra only; no `vListInsertEnd'` result or abstract relation. |
| `Raw-R3c` | `20260731Tlist-raw-r3c-06-prestate`, exit 0 in 22.666 s, `quick_and_dirty=false` | One exact empty-list/fresh-item raw prestate has the ten required field projections and unchanged heap typing. | A concrete witness, not a general representation invariant. |
| `Raw-R3d` | `20260731Tlist-raw-r3d-05-result`, exit 0 in 24.132 s, `quick_and_dirty=false` | `raw_vListInsertEnd_empty_result` proves the source-derived raw function has a positive `Result ()` run at that witness. | Positive reachability only; it does not state the full poststate. |
| `Raw-R3e` | `20260731Tlist-raw-r3e-04-count-index-post`, exit 0 in 75.863 s, `quick_and_dirty=false` | The insert result has item count 1 and `pxIndex` equal to the inserted item. | Count/cursor postcondition only. |
| `Raw-R3f` | `20260731Tlist-raw-r3f-09-container`, exit 0 in 25.860 s, `quick_and_dirty=false` | Separate checked postconditions establish both sentinel links, both item links, and the item-to-list container pointer. | Concrete singleton topology only; no abstraction simulation. |
| `Raw-R3g` | `20260731Tlist-raw-r3g-10-canary-htd`, exit 0 in 24.313 s, `quick_and_dirty=false` | The operation frames item key/owner, every trailing byte in the eight-byte sentinel over-read region, the 0x3000 canary, and heap typing. | Frame groups only; the final conjunction is the master rung. |
| `Raw-R3-master` | `20260731Tlist-raw-r3-master-01`, exit 0 in 33.513 s, `quick_and_dirty=false` | `raw_vListInsertEnd_empty_master` mechanically conjoins the eight checked groups into the exact empty-to-singleton raw poststate. | No `vListRemove'`, sequential full needle, raw-to-`xlist_abs` relation, or source-to-abstract theorem. |

Thus the split-heap route is blocked at the intended empty-sentinel insert,
whereas the raw route has a checker-green concrete empty-to-singleton
`vListInsertEnd'` result with exact locality and topology.  Every rung in this
operational table remains explicitly marked non-refinement in the mapping.

## First fixed source-to-abstract refinement rung

`Raw-R5` is recorded in the separate
`source_to_abstract_refinement_rungs` mapping section, not retroactively added
to the raw operational table.

| Rung | Checker evidence | Established fact | Explicit non-claim |
|---|---|---|---|
| `Raw-R5` | `20260731Tlist-raw-r5-10-show-thesis`, exit 0 in 25.236 s, `quick_and_dirty=false`; theory SHA-256 `5CD5EF0B3850FEBD712664EA375ED04E3BDDD2C8B80B9AEA75EBDF006613A199` | `raw_insert_end_prestate_rep_empty` relates the fixed concrete empty witness to `raw_empty_abs`; `raw_vListInsertEnd_empty_refines` gives a positive `Result ()` source execution whose output heap satisfies `raw_xlist_rel` for `list_insert_end_abs raw_item_ptr k (raw_empty_abs keys)`. | This is an empty-to-singleton simulation at the fixed layout, not a general-N ring relation, complete R5 bridge, removal theorem, or scheduler refinement. |

The source-to-abstract refinement count is therefore exactly one.  R4
removal, general-N representation/simulation lemmas, the sequential initialise
-> initialise-item -> insert-end -> remove needle, and scheduler refinement
remain pending.

## Invariant candidate ledger

| Candidate | Status | Killing witness or justification |
|---|---|---|
| Cursor is always the sentinel. | `KILLED` | One `vListInsertEnd` moves it to the new item. |
| Cursor is always the ring tail. | `KILLED` | One owner-of-next rotation can leave it at any real node. |
| Every xList is key-sorted. | `KILLED` | FIFO/generic roles use insert-end and need no global key ordering. |
| Every task is in exactly one concrete list. | `KILLED` | A blocked task can have generic and event list items in two lists. |
| Every delayed key is greater than the current tick. | `KILLED` | An overflow-delayed key is numerically below the pre-wrap tick. |
| The named object `xDelayedTaskList1` is always the current list. | `KILLED` | Tick wrap swaps role pointers. |
| A tick that readies a higher-priority task also changes `pxCurrentTCB`. | `KILLED` | In `tick_wakes_delayed`, the tick moves `HIGH` into `ready[3]` and raises the top priority while `LOW` remains current; a separate switch changes current. |
| Tick wrap moves delayed nodes between the two physical list objects. | `KILLED` | In `tick_wrap_swaps_delay_roles`, `WRAP` remains physically in delayed-list object 2 while only the current/overflow role pointers exchange. |
| Same-priority switching always selects the physical sentinel-next item, regardless of `pxIndex`. | `KILLED` | The preserved ring is `A,B,C`, the pre-switch cursor is `C`, and cursor-relative switches select `A,B,C,A`. |
| Cursor is sentinel or a counted real member. | `ACTIVE` | Established by init/insert/remove source updates; pure preservation lemmas are staged from `XList_Model_Sequence_Lemmas.thy` through `XList_Model_Invariants.thy`. |
| Real ring IDs are distinct and next/previous are mutual. | `ACTIVE` | Required for bounded traversal, removal, count, and a functional abstraction. |
| Ready-list FIFO view contains exactly ready tasks of its array priority. | `ACTIVE` | Needed for context selection and delay removal; requires a TCB-pointer injection. |
| At least one ready list at or below `uxTopReadyPriority` is nonempty. | `ACTIVE` | Makes the context-switch search terminating; the idle-task assumption must be explicit. |
| Current/overflow delayed roles are disjoint and swap only at word wrap. | `ACTIVE` | Needed to interpret modular ticks as one logical time line. |
| An unsuspended `vTaskIncrementTick` increments the tick modulo `2^32`; exactly when the new tick is zero it swaps the delayed roles and increments the overflow counter. | `ACTIVE` | Source control flow and the no-wake/wrap traces support the decomposition; universal preservation is an L8 obligation. |
| The tick wake scan removes the due prefix of the current delayed ordered view and stops at the first future key. | `ACTIVE` | The singleton no-wake and wake traces exercise both sides of the boundary; the general-prefix statement remains to be proved. |
| `vTaskIncrementTick` frames `pxCurrentTCB`; scheduling choice is delegated to `vTaskSwitchContext`. | `ACTIVE` | The wake trace distinguishes readiness from selection; a source theorem is still required. |
| `vTaskSwitchContext` preserves ready-ring topology and membership, advances only the selected ready-list cursor, and makes that cursor's owner current. | `ACTIVE` | The `A,B,C,A` execution is a four-step witness; the general theorem is an L9 obligation. |

Here `ACTIVE` means a candidate selected for the representation relation or
lemma graph.  Trace coverage does not universally establish any active row.

## First lemma graph

```text
L0 lexical/macro closure + proof-port ledger
  -> L1 sentinel-prefix and allocated-region facts
  -> L2 ring shape / distinctness / count
  -> L3 init, insert-end, ordered-insert, remove preserve L2
  -> L4 FIFO and ordered view equations
  -> L5 TCB pointer injection and per-item-role membership
  -> L6 ready-array / delayed-role scheduler invariant
  -> L7 delay success and delay-until wrap branches
  -> L8 tick no-wrap, tick-wrap/swap, wake-prefix
  -> L9 context-switch search termination and FIFO rotation
  -> L10 per-operation forward simulation
  -> L11 trace refinement for the frozen API alphabet
```

The graph is revised only after a checked goal or executable counterexample;
generated verification conditions are evidence about dependencies, not proofs.

The pure R1/L2--L3 model is deliberately checker-runged rather than monolithic:

1. `XList_Model_Definitions.thy` fixes the state, operations, and candidate
   invariant without proof search;
2. `XList_Model_Sequence_Lemmas.thy` proves set, distinctness, and sortedness
   facts for the two insertion traversals;
3. `XList_Model_Predecessor_Lemmas.thy` isolates cursor-predecessor and removal
   obligations;
4. `XList_Model_Invariants.thy` composes those facts into operation-level
   preservation theorems; and
5. `XList_Model.thy` contains only executable, non-vacuous witnesses.

This dependency chain is also a diagnostic tool: the first red theory names
the abstraction layer that needs repair, while later layers are not searched
until their prerequisites are checker-green.  The model session sets
`parallel_proofs=0` so a later proof future cannot hide the earliest red brick;
this is a reproducibility/tooling choice, not a logical assumption.

### Pure-model checker evidence

Run `20260731Tmodel-13-sequential` built all five theories with Isabelle2025-2,
`quick_and_dirty=false`, `parallel_proofs=0`, and the session's 60 s hard
bound.  It finished with exit code 0 in 13.058 s (2 s reported session time,
9 s total Isabelle time).  The session database records `return_code=0` and a
null error blob.  The durable stdout SHA-256 is
`76987C104EEBE29C4DAE6CEC61C65906DAECE37A97B9AFAADEF7953397E033AB`;
stderr is the empty-log hash
`7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6`.
The post-build forbidden-pattern scan across `theories/`, `proof_port/`, and
`scripts/` returned zero matches for unfinished/admitted proofs, added axioms,
skip-proof/oracle/cheat mechanisms, and `quick_and_dirty=true`.

The checked theorem chain covers set and distinctness preservation for
insert-after, set/distinctness/sortedness preservation for stable ordered
insertion, predecessor membership through removal, and `xlist_wf`
preservation for insert-end, ordered insert, and remove.  The final theory's
FIFO and equal-key examples also evaluate and prove their concrete expected
states.  This is a checker-green pure abstraction layer; it is not yet a
source-to-model refinement theorem, a heap-shape proof, or a concurrency
claim.

## Executable invariant-discovery evidence

Run `20260731Tlist-trace-04-analysed` compiles the unmodified upstream
`list.c`, executes nine named states, and then runs
`tools/analyse_list_trace.py --require-core-witnesses`.  Its
`analysis.json` classifies itself as `EXECUTABLE_OBSERVATION_NOT_PROOF` and
records first witnesses for five false candidates:

- insert-end makes the cursor a real item, killing “cursor is always END”;
- one FIFO rotation leaves the cursor away from the raw ring tail;
- descending FIFO keys kill the claim that every xList role is sorted;
- equal-key ordered insertion leaves the old item before the new one;
- removing the cursor moves it to the predecessor.

The same run checks count/ring-length agreement, cursor membership, and
ordered-role monotonicity in every recorded applicable state.  These are
candidate generators only; the universal preservation claims remain L2/L3
Isabelle obligations.

Run `20260731Tlist-mutation-01-reverse-link` creates a provenance-recorded
temporary mutant that omits the first reverse-link update in `vListRemove`.
The mutant compiles, but the unchanged shape oracle aborts (exit 6).  No
upstream file is edited.  This is the first non-vacuity mutation required by
the target gate; a later Isabelle mutation must additionally kill a proof
goal rather than only the executable oracle.

### Scheduler source trace

Run `20260731Tscheduler-trace-03-delay-phases` extends the independently
reproducible four-scenario trace with two positive-delay executions and an
explicit phase-indexed invariant gate.  It completed in 6.097 s with
compile/trace/analysis exit codes `0/0/0`, 57 JSONL records, 17 snapshots, 39
successful checks, all six required scenarios, and zero fatal records:

| Scenario | Observed source-state delta | Design effect |
|---|---|---|
| `tick_no_wake` | Tick `5 -> 6`; key `7` remains delayed and current is unchanged. | Supplies the future-key stop witness for L8. |
| `tick_wakes_delayed` | Tick `9 -> 10` moves `HIGH` delayed -> `ready[3]` and raises top priority without changing current; a later switch selects `HIGH`. | Kills fused tick/switch semantics and splits L8 from L9. |
| `tick_wrap_swaps_delay_roles` | Real `UINT32_MAX -> 0`; role pointers swap, the key-`1` node stays in physical object 2, and `0 -> 1` wakes it. | Kills physical-node migration and supports an epoch/role relation. |
| `same_priority_switch_fifo` | Ring `A,B,C` and its links remain fixed while the cursor drives selections `A,B,C,A`. | Kills head-only selection and exposes the cursor-relative FIFO view. |
| `delay_positive_no_wrap` | At tick 5, source `vTaskDelay(2)` moves current `RUN` from `ready[2]` to current-delayed at key 7, leaves `IDLE` ready, keeps current identity until port service, and records one yield. | Instantiates P2 and kills globally asserting either current-ready or exact top-cache at the yield-pending boundary. |
| `delay_positive_wrap` | At tick `UINT32_MAX-1`, source `vTaskDelay(3)` inserts current `RUN` at key 1 into the overflow-delayed physical list without swapping roles and records one yield. | Instantiates P3 and separates delay-time arithmetic wrap from tick-time role swap. |

The run includes the unchanged proof-port contract body followed directly by
untouched `tasks.c` and `list.c`.  Every one of seven out-of-scope link-closure
stubs records `stub_reached` and terminates rather than fabricating state; none
was reached.  The extended harness/runner/binary/trace/analysis hashes are
respectively
`9B9BD5D73AFBBCB7715016A8A1A1D9A2FF8A14471FBBE31CF2EA70205D5123A7`,
`1D855DF45BBBB009725AED8C203D8FE529D6EEF8EEA5D88F10FF492121C0DD84`,
`D6C9B6480C38165B33D2D57846D9A007E1E0FB0AD53EAF1D2D79A82CE16737FF`,
`125A7B9F605DC41C894EEB39D4AED3A128963FF05A6C1758E7A5CEF45EC099A8`,
and `2E2821F00974776D29BA53A3772F8C975261E78F82FF16A46EB986D3AF2C08BD`.

The phase gate checks exact top-ready/current-ready only at `StableRunning`.
At `YieldPending` it checks the cache as an upper bound, current membership in
a delayed role, and a positive proof-port yield ledger.  This is evidence for
the phase-indexed invariant architecture rather than a relaxation made solely
to pass the trace.

Run `20260731Tscheduler-trace-01` alone additionally received a separate
manual `-fsanitize=address,undefined` compile-and-run check with exit codes
`0/0` and no reported sanitizer error.  The independent run does not claim a
sanitizer gate.  Both runs are classified
`EXECUTABLE_OBSERVATION_NOT_PROOF`: these runs revise L7/L8/L9 candidates but do not
increase the source-to-abstract refinement theorem count.
