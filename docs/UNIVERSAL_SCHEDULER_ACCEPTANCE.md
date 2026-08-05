# Universal Scheduler Refinement Acceptance Criteria

**Correction date:** 2 August 2026
**Frozen build:** FreeRTOS V6.1.1 proof configuration with `configMAX_PRIORITIES = 4`

## 1. Purpose and immediate correction

The sealed P2 theorem is a useful non-vacuous generated-source execution
witness, but it is not a universal correctness theorem for `vTaskDelay`, the
five scheduler roots, or the FreeRTOS scheduler.  It fixes two tasks with
priorities 0 and 2, tick 5, delay 2, wake 7, singleton ready lists at priorities
0 and 2, and empty remaining scheduler lists.  It proves exactly that path.

For the frozen four-priority build, "all priority combinations" must not mean a
small test matrix.  It means universal quantification over an arbitrary finite
set of live tasks and an arbitrary priority function satisfying

$$
\forall t\in\mathit{live}.\;\mathit{priority}(t)<4.
$$

For $n$ live tasks this subsumes all $4^n$ priority assignments, as well as all
well-formed task distributions among the four ready queues.  The task count is
not fixed, so the state space is not a finite list of P2-like cases.  This
criterion is universal for the frozen value `configMAX_PRIORITIES = 4`; it does
not claim correctness for every possible compile-time value of that macro.
Such a claim would require a separately justified configuration-parametric
translation or separately checked builds.

## 2. Required state relation and quantifiers

A qualifying theorem must use one generic concrete-to-abstract scheduler
relation, not a relation whose premises already select the desired branch or
poststate.  Schematically, the minimum Level A theorem is:

```isabelle
theorem vTaskDelay_refines_all:
  fixes D R c a ticks
  assumes "scheduler_endpoint_rel StableRunning D R c a"
      and "settled_inv a"
      and "representation_side_conditions D R c a"
  shows
    "vTaskDelay' ticks \<bullet> c
     \<lbrace>\<lambda>r c'.
        r = Result () \<and>
        scheduler_endpoint_rel YieldPending D R c'
          (task_delay_abs ticks a) \<and>
        core_inv (task_delay_abs ticks a)
      \<rbrace>"
```

The actual statement may factor the abstract resume/yield transition
differently, but it must quantify over at least:

- every finite live-task set;
- every task-to-TCB decoding that is injective on live tasks;
- every priority assignment in the range 0 through 3;
- every well-formed content, ordering, and cursor position of `ready[0..3]`;
- either delayed-list physical role assignment;
- arbitrary well-formed current and overflow delayed lists;
- arbitrary current task admitted by the stable-state invariant;
- every 32-bit tick and every 32-bit delay argument;
- all heap addresses satisfying the generic separation and alias conditions;
- all source scalars and proof-port fields permitted by the declared API
  boundary.

The relation must cover all four ready lists, both delayed lists, the pending
and suspended lists, the generic and event list items embedded in every live
TCB, current-task and top-priority caches, delayed-list roles, list cursors,
tick and overflow counters, suspend depth, missed ticks, missed yield, and the
declared proof-port observations.

If the theorem assumes a settled, sequential API-call boundary -- for example,
empty pending-ready list, zero missed ticks, suspension depth zero, and no
interrupt interleaving during the call -- that is a legitimate but mandatory
scope restriction.  It must be present in the theorem and in every report.  It
must not be described as concurrent-kernel correctness.

## 3. Coverage dimensions for universal `vTaskDelay`

The universal theorem must cover these cases through its quantified statement,
not merely through separate concrete witnesses:

| Dimension | Required cases |
|---|---|
| Delay argument | zero and every positive 32-bit value |
| Wake arithmetic | non-wrapping and wrapping addition |
| Current priority | 0, 1, 2, and 3 |
| Other tasks | none beyond the mandatory runnable task, one, or arbitrarily many |
| Ready topology | arbitrary valid population at every priority |
| Same-priority scheduling | arbitrary list order and cursor, including two or more peers |
| Delayed destination | current delayed list and overflow delayed list |
| Delayed topology | empty and arbitrary non-empty ordered rings; insertion at head, middle, and tail |
| Resume result | every outcome reachable under the declared sequential or concurrent call model |
| Endpoint | explicit phase relation, including the period before a port context switch |
| Frames | every unmodified root, TCB field, list item, and unrelated heap region |

At the frozen sequential settled boundary, branches that require an intervening
interrupt may be excluded only by a proved reachability argument.  If interrupt
interleaving is admitted, the pending-ready and missed-tick processing inside
`xTaskResumeAll` must instead be included in the abstract transition and proof.

## 4. Three distinct acceptance levels

### Level A -- one API, universally quantified

Level A is a full generated-source refinement theorem for one API, initially
`vTaskDelay`, over every state and argument satisfying the generic invariant
and the explicitly declared call boundary.  It must include all priority
assignments and all source branches reachable at that boundary.  A finite
collection of fixed witnesses does not satisfy Level A.

### Level B -- five scheduler roots, all branches

Level B requires universal refinements for the five frozen roots:

1. `vTaskDelayUntil`;
2. `vTaskDelay`;
3. `vTaskIncrementTick`;
4. `vTaskSwitchContext`;
5. `xTaskGetTickCount`.

The branch ledger must include:

- `vTaskDelayUntil`: delay and no-delay outcomes; all relations among current
  tick, previous wake, and modular next wake; current versus overflow delayed
  destination;
- `vTaskDelay`: zero and positive delays, modular wrap and non-wrap, and both
  delayed destinations;
- `vTaskIncrementTick`: suspended and unlocked execution, tick wrap and
  delayed-role swap, due prefixes of length zero, one, and arbitrary $N$,
  event-item absent or present, and every priority of every awakened task;
- `vTaskSwitchContext`: suspended and unlocked execution, downward search from
  each possible cached top priority, empty queues passed during the search, and
  every valid same-priority cursor/list ordering;
- `xTaskGetTickCount`: return-value correctness and a complete frame theorem.

All source-reachable uses of `vTaskSuspendAll`, `xTaskResumeAll`,
`prvCheckDelayedTasks`, and `prvAddTaskToReadyQueue` belong to the closure.  A
claim of closure-wide branch coverage therefore also requires pending-ready
prefixes of length zero, one, and arbitrary $N$, missed-tick debt zero and
arbitrary $N$, priority comparisons that do and do not request a yield, and
the relevant word-wrap side conditions.

Level B ends with invariant preservation and a forward-simulation theorem for
every finite sequence of the five root calls whose successive API
preconditions hold.  Five unrelated leaf lemmas are not sufficient.

### Level C -- whole scheduler functional correctness

Level C is substantially stronger than Level B.  It additionally includes all
in-scope task lifecycle and scheduling operations, including task creation and
deletion, suspend and resume, priority change, event/queue/ISR interaction,
scheduler initialisation and start, idle cleanup, and every API enabled by the
frozen configuration.  It also needs an explicit concurrency model or
rely/guarantee discipline for interrupts and the port, plus the connection
between a yield request and the real context-switch implementation.

Allocator correctness, stack construction, compiler correctness, and
machine-code refinement remain further independent layers unless explicitly
included.  Even a completed Level B must not be labelled Level C.

## 5. Current hard score

The score is deliberately binary at the acceptance boundary; partial lemmas
remain useful engineering progress but do not round up.

| Acceptance item | Current score | Reason |
|---|---:|---|
| Translation of the five roots | **5/5** | All five generated definitions have checker-green translation evidence. |
| Generic, whole-operation refinement of the five roots | **0/5** | Every current root refinement is a restricted branch or weak projection. |
| Universal all-priority scheduler theorem | **0/1** | The positive-delay capstone is one fixed two-task priority assignment. |

More specifically:

- `xTaskGetTickCount` has a near-universal scalar projection, but not a theorem
  over the full unified scheduler representation;
- `vTaskDelay` has a universal zero-delay scalar fragment and the fixed
  positive-delay P2 witness, but no universal positive-delay theorem;
- `vTaskDelayUntil` covers only a pre-suspended no-delay branch;
- `vTaskIncrementTick` covers only the scheduler-suspended branch;
- `vTaskSwitchContext` covers only the scheduler-suspended branch.

At the reusable list layer, Gate L is now closed.  Generated general ordered
insertion and general removal are checker-green for arbitrary legal
represented rings; generated raw and scheduler insert-end are checker-green;
and the accepted family capstone supplies non-target-root, sibling-owner, and
priority-field frames under its explicit representation and separation
premises.  The central QAD-false closure runs are
`20260802Tgate-l-central-family-02` and
`20260802Tgate-l-central-insert-end-01`.  These list-layer results remove the
former non-empty ordered-insert blocker, but they do not change the **0/5**
whole-operation score above: no list primitive or abstract composition is by
itself a universal generated-source refinement of a scheduler root.

## 6. Anti-cheat acceptance rules

A result is rejected from the universal inventory if any of the following is
true:

1. The precondition fixes `p2_pre`, two tasks, priorities 0 and 2, tick 5,
   delay 2, wake 7, or an otherwise predetermined branch.
2. A case split produces finitely many example heaps instead of one theorem
   quantified over an arbitrary finite task set and arbitrary valid rings.
3. The relation omits a source-observable list, cursor, TCB item, scalar, or
   heap region modified or inspected by the operation.
4. The expected concrete poststate, branch result, or destination list is
   assumed rather than derived from the generated source semantics.
5. A pure abstract lemma, translation smoke test, executable harness, symbolic
   trace, or SMT model is counted as source-to-abstract refinement.
6. A conditional source theorem is counted without proving its representation
   precondition is inhabited over the claimed generic state class.
7. Arithmetic silently replaces 32-bit modular words by naturals or omits the
   necessary non-wrap premise.
8. A successful-call theorem omits normal termination or permits a vacuous
   postcondition.
9. Invariant preservation, alias/frame conditions, or sequential composition
   is inferred from tests rather than checked in Isabelle.
10. The accepted dependency closure contains `sorry`, `oops`, admitted desired
    facts, oracle shortcuts, or `quick_and_dirty=true`, or retains undisclosed
    locale/axiomatic assumptions.

Regression witnesses should include priorities 0 through 3, at least two
same-priority tasks, every downward top-priority scan distance, non-empty
delayed insertion at head/middle/tail, tick wrap, zero/one/$N$ due tasks, and
zero/one/$N$ pending-ready tasks.  Such witnesses are valuable branch and
mutation tests, but never substitutes for the universal theorem.

## 7. Staged gates

### Gate L -- universal list layer

Close the general-$N$ ordered-insertion refinement for arbitrary well-formed
rings, including the legal empty-ring sentinel alias, together with general
remove and insert-end theorems.  The gate also requires generic-item/event-item
alias and frame
lemmas strong enough to use these operations at arbitrary scheduler-owned
roots.  Gate L is closed only by source-derived, checker-green theorems.

**Current status: Gate L is closed.**  Generated general ordered insertion,
generated general removal, generated raw and scheduler insert-end, derived
count capacity, exact write footprints, the legal empty-ring alias, same-TCB
Generic/Event separation, and arbitrary non-target scheduler-root frames are
present in the accepted central dependency closure.  The two top-level
QAD-false runs are `20260802Tgate-l-central-family-02` for
`EAL6_FreeRTOS_V611_Scheduler_List_Family_Frame_Capstone` and
`20260802Tgate-l-central-insert-end-01` for
`EAL6_FreeRTOS_V611_Scheduler_Insert_End_Translation_General`; both have
`exit_code=0`.  The exact quantified scope, explicit premises, hashes, and
session ledger are recorded in `GATE_L_CLOSURE_AUDIT.md`.

The trace-led invariant design and its empty-ring/alias falsification tests are
recorded in `UNIVERSAL_ORDERED_INSERT_INVARIANT_AUDIT.md`.  Those traces guide
the invariant but are not evidence for closing this gate.

### Gate H -- universal heap/state `vTaskDelay` hard gate

Establish the generic representation relation over arbitrary finite live
tasks, all four ready queues, both delayed lists, pending and suspended lists,
and all required TCB fields.  Then prove the Level A `vTaskDelay` theorem for
every tick, delay, priority assignment, and valid topology at the declared API
boundary.  Add generic preimage/inhabitation evidence and audit the exported
theorem object's assumptions.  The existing P2 theorem is a regression witness
for Gate H, not its completion.

The positive-delay composition must expose a remove-to-insert intermediate
state in which the current generic item is globally unlinked (normally witnessed
by a null container under the faithful-membership invariant).  Spatial
freshness relative to the target delayed list alone is not enough to frame all
other scheduler-owned roots.

Delay-phase endpoints must identify their physical root.  A single anonymous
sentinel value cannot represent two distinct empty scheduler lists, especially
across tick-wrap role exchange.  The root-tagged abstract endpoint model, its
raw removal/ordered-scan bridge, and a general abstract `ResumeRel` are now
checker-green.  The abstract captured-source-key result is also checker-green:
`core_wf_resume_one_pending_abs_preserves_physical_source_key` preserves the
key selected from physical delayed A, delayed B, or suspended storage, with
central QAD-false evidence in `20260802Tresume-general-relation-central-01`.
This is an abstract relation lemma, not a generated-source theorem.  The
resume outer scaffold likewise supplies proof architecture only.  Composition
with the generated outer `xTaskResumeAll'` pending-ready and missed-tick loops
remains an open source-level Gate-H obligation; therefore Gate H remains open.

The following additional Gate-H bricks are now checker-green.  Their stated
boundaries are part of the result; none is counted as the missing full
`vTaskDelay` source theorem.

| Result and evidence | Exact checked scope | Boundary that remains |
|---|---|---|
| `EAL6_FreeRTOS_V611_Scheduler_Task_Observation_Rel`; central run `20260802Ttask-observation-central-01` | For an arbitrary finite live-task set, records each live TCB's guarded Generic/Event item pointers, owner payloads, and concrete/abstract priority equality with the frozen bound `< 4`; derives represented list-head owner/priority observations and exact observation frames. | This is a representation and frame layer, not execution of a scheduler root. |
| `EAL6_FreeRTOS_V611_Scheduler_Event_Root_Family_Rel`; central run `20260802Tevent-root-family-central-01` | Represents an arbitrary finite Event-root family with a distinguished pending root, arbitrary finite live set, every root ring/count/cursor/key, total Event-key map `K_E`, unique membership, exact container/null fidelity, and non-target/removal payload frames. | These are relation and raw-transformer facts; they do not execute the generated pending-ready loop or close `xTaskResumeAll'`. |
| `EAL6_FreeRTOS_V611_Scheduler_Delay_Suspended_Core`; central run `20260802Tdelay-suspended-core-central-01` | Checks the arbitrary remove--32-bit-wake-key-write--ordered-insert core under explicit family ownership, geometry, ordered-target, current/overflow-root, and owner/target-distinct premises; modular wake comparison derives the selected delayed root, and the composed helper reaches the exact heap. | The checked helper composes generated list leaves with an explicit proof-level key-write step; it is not execution of the complete generated `vTaskDelay'` body and contains no suspend/resume/final-yield composition. |
| `EAL6_FreeRTOS_V611_Scheduler_Resume_Inner_Source`; central run `20260802Tresume-inner-central-01` | Executes generated `xTaskResumeAll'` when the positive suspension word remains nonzero after decrement.  Under the declared proof-port boundary it returns integer `0`, changes only the suspension word, and refines the inner `ResumeRel` constructor through `scheduler_control_mod_rel`; tasks, priorities, heap, and list populations remain arbitrary. | This is only the nested/inner resume branch; it excludes the outermost pending, missed-tick, and yield paths. |
| `scheduler_xTaskResumeAll_outer_quiet_general_exact`; QAD-false run `20260802Tresume-outer-quiet-general-02` | Executes generated outermost `xTaskResumeAll'` for suspension word `1`, nonzero task count, an empty guarded pending list, zero missed ticks, zero missed yield, and the declared proof-port boundary.  It returns integer `0` and changes only the suspension word from `1` to `0`; no task identity, priority, tick, heap, or other list population is fixed. | This is the quiet branch only and has no representation-preservation or `ResumeRel` postcondition.  Its recorded command used the then-local outer-scaffold session root, so it is checker-green evidence but not a `-CentralOnly` closure run. |

All five runs have `exit_code=0`, `quick_and_dirty=false`, empty stderr, and
`timed_out=false`.  Local recomputation matches every recorded stdout/stderr
SHA-256.  They also share the frozen evidence hashes:

- ELF: `DC830E50513384D712E0D1C68CB198EA656365F673D021C452D7D7EBD45C045A`;
- layout ledger: `CA288A4CD2344BE979ADFA9DBF0298C6715F196D64AE472D173304289C4F2C02`;
- generated address configuration:
  `27F74768E1DB1C3F8DBFCFC85371075192BB7D2544ED324DC81B65A9A2911712`.

#### Pending-ready drain body: generated fragment progress (3 August 2026)

The generated pending-loop body `resume_pending_generated_body` is now
checker-green along a longer prefix.  Beyond the previously recorded
event/generic unlink and top-raise cutpoints, the steps below are executed
from the cutpoint state for an arbitrary head task at an arbitrary in-range
priority.  No task, priority, live set, heap, address or list population is
fixed.

| Result and evidence | Exact checked scope | Boundary that remains |
|---|---|---|
| `generated_ready_destination_from_priority_word` and `generated_ready_destination_distinct_from_other_roots`; QAD-false run `20260803Tresume-ready-destination-02` | For every 32-bit priority word `w < 4`, the source expression `array_ptr_index pxReadyTasksLists_' False (unat w)` is the indexed root `sr_ready generated_scheduler_roots (unat w)`; that root belongs to the eight physical scheduler roots, is `c_guard`ed, is distinct from delayed A, delayed B, pending and suspended, and its 20-byte region is disjoint from every other physical root.  The bound is the source's own guard, not an added restriction. | Static layout, guard and separation only; no source statement is executed here. |
| `resume_pending_generated_ready_select_exact`; QAD-false run `20260803Tresume-ready-select-01` | Executes the generated in-range priority guard, the ready-array guard, and the destination read from `resume_pending_top_raised_state`.  Returns exactly `sr_ready generated_scheduler_roots (rpc_priority C t)`, leaves the state unchanged, and supplies the destination guard and its separation corollaries. | Three source steps of one loop body; no insertion, yield join, or loop closure. |
| `resume_pending_generated_ready_insert_exact`; QAD-false run `20260803Tresume-ready-insert-03` | Executes generated `vListInsertEnd'` on the selected ready queue with the awakened task's Generic item, reaching the exact post heap `raw_insert_concrete_heap` over the represented target ring.  Both premises of the general generated insert-end theorem are discharged rather than assumed: the target ring relation comes from the post-removal family relation, and freshness is transported from entry freshness, which survives the removal because the removal rewrites only the owner root and that owner root is proved distinct from the destination queue. | No `pxCurrentTCB` guard, yield-required join, next-head read, or loop closure; the body is not composed end to end. |

All three runs have `exit_code=0`, `quick_and_dirty=false`, `timed_out=false`
and empty stderr, and share the frozen evidence hashes recorded above.  These
are generated-source execution steps for a fragment of one loop body.  They
add zero refinement rungs and do not change the **0/5** whole-operation score.

The drain body's remaining statements are now also checker-green, from the
same arbitrary gate entry state:

| Result and evidence | Exact checked scope | Boundary that remains |
|---|---|---|
| `resume_pending_generated_yield_join_exact`; QAD-false run `20260803Tresume-yield-join-01` | Executes the generated `pxCurrentTCB` guard and the yield comparison from the ready-inserted cutpoint state.  The current task is whatever the entry relation's current clause designates; the comparison result is the exact conditional word for both outcomes.  A sibling-free insert-end priority byte frame transports both priority observations across the insertion, and `resume_pending_yield_join_word_encoding` ties the returned word to the abstract local-yield flag. | Two source statements of the body; no next-head read and no loop composition. |
| `raw_remove_member_owner_byte_frame`, insert-side Event storage/item frames, and `resume_pending_generated_head_read_drained_empty` / `_nonempty`; QAD-false run `20260803Tresume-next-head-03` | The exact removal footprint is proved to miss every ring member's owner field (including the removed node and the unlinked head's neighbours), the Event-root family relation is transported across the generated insertion, and the generated head re-read is executed at the drained state: it returns the next pending task's TCB pointer, or NULL when the drained task was the last.  The next task is whatever the arbitrary pending context lists second. | A read-only re-read; no loop closure and no re-established gate entry relation for the drained context. |
| `resume_pending_generated_body_exact`; QAD-false run `20260803Tresume-body-02` | Executes the complete generated loop body `resume_pending_generated_body` end to end from the gate entry state, in source order: head guard, generated Event and Generic removals, top-priority conditional, in-range and array guards, destination read, generated ready insert-end, current-task guard, yield comparison, and the generated next-head re-read.  Returns the exact loop-carried pair -- the next pending TCB pointer or NULL, and the conditional yield word -- and carries the transported Event family relation, the current-task pointer frame, the exact top-priority word, and the `RP_YieldChecked` phase invariant to the drained state.  Head task, priorities, current task, live set, ring populations and heap remain arbitrary. | One arbitrary iteration of the loop body.  It does not re-establish the gate entry relation for the drained context, does not close the while loop over arbitrary prefixes, and does not execute the generated outer `xTaskResumeAll'` wrapper (suspension word, missed-tick loop, yield flag clear). |

The three continuation runs (`20260803Tresume-yield-join-01`,
`20260803Tresume-next-head-03`, `20260803Tresume-body-02`) have
`exit_code=0`, `quick_and_dirty=false`, `timed_out=false`, the standard
empty stderr, and the same frozen evidence hashes.  With them the generated
pending-loop body is executed end to end for one arbitrary iteration.  This
is still zero refinement rungs: no scheduler root's whole-operation theorem
changes, and the **0/5** score above stands.

#### Loop-closure preparation: relation transport to the drained state

Closing the drain loop requires re-establishing the gate relation at the
state the body theorem produces.  The following transport bricks are now
checker-green; each holds for an arbitrary head task, arbitrary live set and
arbitrary topology, and none of them executes any further source statement.

| Result and evidence | Exact checked scope | Boundary that remains |
|---|---|---|
| `raw_insert_end_family_owner_byte_frame`, per-write owner projections, and `resume_pending_drained_task_observation`; QAD-false run `20260803Tresume-drained-observation-01` | The exact insert-end footprint misses every managed node's owner field (members of the rewritten ready ring, the inserted item, and unrelated live items alike); combined with the removal-side member and sibling frames, the owner projections of both embedded items of every live task survive all three drain writes, and the full `TaskObservationRel` is re-established at the drained heap against the unchanged abstract state. | Observation layer only; no list representation, scalar, or current-task clause of the gate relation is re-established here. |
| `resume_pending_generic_unlinked_after_removal` and `resume_pending_drained_generic_family`; QAD-false run `20260803Tresume-drained-family-01` | The awakened task's Generic item is proved globally unlinked at the remove-to-insert intermediate state -- the exact null-container membership condition this document requires -- and the accepted insert-end preservation theorem then yields the whole drained Generic family: family relation at the drained heap, membership exactly the selected ready queue, wake key unchanged, container now that queue. | Raw family layer only; no decoder or abstract link. |
| `resume_pending_drained_generic_relabel`; QAD-false run `20260803Tresume-drained-relabel-01` | At every scheduler-owned Generic root, the drained raw family relabels to the abstract ready-inserted snapshot family: the ready queue gains `Generic t` with the context key exactly where the raw ring gains the task's item, and every other root keeps the removal relabel. | Per-root decoder link only; the assembled gate relation for the drained context, the loop induction, and the outer wrapper remain open. |

| `raw_insert_end_family_key_byte_frame` and `resume_pending_drained_keys`; QAD-false run `20260803Tresume-insert-key-frame-02` | The exact insert-end footprint misses every managed node's item-value field, so every live task's wake key survives the drain body's final write; combined with the removal preservation, the gate's key clause is re-established at the drained heap for all live tasks. | Byte layer only. |
| `core_wf_resume_one_pending_abs` (with the tail-cursor/predecessor kit `Scheduler_Resume_Abs_Kit`); QAD-false runs `20260803Tresume-abs-kit-01`, `20260803Tresume-abs-preservation-10` | The abstract one-task resume preserves the full core well-formedness invariant -- ring shapes, role payloads and tail cursors, the twelve membership clauses, delayed ordering and wake agreement, the ready cache, and the current task -- assuming only a well-formed state and a pending task; liveness, blocked placement, and ready absence are derived from membership well-formedness.  The abstract update aligns field by field with the checked concrete drain (including `sa_top_ready := max`). | A pure abstract theorem; it executes no source statement and is not itself a refinement. |

These bricks re-establish the observation, family, decoder, and key layers
of the gate relation at the drained state, and supply the abstract-side
invariant preservation the re-entry theorem needs.  They add zero
refinement rungs and leave the **0/5** score unchanged.

#### Loop re-entry: the drained state satisfies the gate again

| Result and evidence | Exact checked scope | Boundary that remains |
|---|---|---|
| `resume_pending_gate_reentry` with its supporting chain (`resume_pending_drained_entry_rel`, tail container observations, the abstract bridge with `pending_generic_key_abs t a = rpc_K_G C t`, the five snapshot-to-abstract family matches, `resume_pending_drained_lists_rel` and the scalar/role/current clauses, and the tail ownership/geometry/subset/cross clauses); QAD-false runs `20260803Treentry-pure-06`, `20260803Treentry-container-01`, `20260803Treentry-abs-bridge-04`, `20260803Treentry-lists-01`, `20260803Treentry-rep-04`, `20260803Treentry-fam-03`, `20260803Treentry-gate-01` | The state produced by one checked drain iteration satisfies the **full** gate entry relation again, with explicit witnesses: the tail context (remaining tasks, entry top raised to the awakened priority), the four-phase snapshot, the drained raw families, and the abstract one-task resume `resume_one_pending_abs t a`.  All thirty-three gate clauses are re-derived; the abstractly captured wake key is proved equal to the context key; nothing about the head task, the tail, priorities, rings or the heap is fixed.  Together with `resume_pending_generated_body_exact` the pending-ready loop is a relation-preserving gate-to-gate step, one task per iteration. | One step only: the while-loop induction over an arbitrary pending prefix, the loop-exit case, the missed-tick loop, and the outer `xTaskResumeAll'` wrapper are not yet composed.  Still zero refinement rungs; the **0/5** score stands. |

#### Loop closure: the generated while loop drains any pending list

| Result and evidence | Exact checked scope | Boundary that remains |
|---|---|---|
| `resume_pending_generated_loop_drains`; QAD-false run `20260803Treentry-induction-09` | The generated pending-ready while loop, started at the head pointer for an **arbitrary** pending task list and an arbitrary entry yield word, runs to completion by plain list induction over the gate-to-gate step (`resume_pending_generated_body_exact` + `resume_pending_gate_reentry`).  It returns exactly `(NULL, yw)` and exits in a gate state for the empty pending list whose abstract side is `foldl resume_one_pending_abs` over the drained tasks; the exit yield word is proved equivalent to "entry word set, or some drained task's priority reaches the current priority".  Live set, priorities and the priority function are carried unchanged across the whole loop.  No pending length, task identity, priority, ring topology or heap layout is fixed. | The loop theorem alone: its entry pair comes from the initial head read (proved separately in both empty and nonempty forms), and the outer `xTaskResumeAll'` wrapper -- critical section, suspension decrement, missed-tick replay loop, missed-yield branch and final yield -- is not yet composed. |
| `resume_pending_generated_loop_drain_pending_abs` with `resume_pending_gate_drain_pending_absD` / `resume_pending_gate_requires_yieldD`; QAD-false run `20260803Tdrain-abs-fold-03` | Under the gate the abstract pending ring is exactly `map Event (rpc_tasks C)`, so the loop's fold coincides with the outer scaffold's `drain_pending_abs`, and the exit yield word is exactly `resume_pending_requires_yield` -- the first disjunct of `resume_yield_required` inside `ResumeOuterDecomp`.  The loop summary is restated in that outer vocabulary with no change of witnesses. | A vocabulary bridge; it adds no new source execution. |
| `resume_missed_generated_loop_replays` and `resume_missed_generated_loop_inv_exit`; QAD-false run `20260804Tmissed-loop-05` | Any relation that (i) exposes `uxMissedTicks` as `sa_missed_ticks` (the gate does, through `scheduler_scalar_rel`) and (ii) is preserved by one generated missed-tick body execution mapping the abstract state through `resume_missed_source_step_abs` is carried through the complete generated missed-tick while loop by induction on the abstract debt: the loop performs exactly `resume_missed_source_steps_abs (sa_missed_ticks a)`, exits with a zero counter, and lands in the outer scaffold's `resume_missed_loop_inv` at full debt.  No debt bound, task population or heap layout is fixed. | The per-iteration premise is honest and open: the unlocked `vTaskIncrementTick'` source summary (delayed-wake processing at suspension depth zero) is not yet proved, so this composes the loop but not its body. |
| `xTaskResumeAll_program_eq` and `xTaskResumeAll_drain_composed`; QAD-false run `20260804Touter-compose-23` | The **real generated wrapper** `xTaskResumeAll'` is proved equal to a named-factor program, and the composition theorem executes it from a gate premise at the decremented state through: critical-section entry, the suspension decrement, both population branches (the underpopulated and still-suspended branches are refuted from the gate), the initial pending head read for an arbitrary task list, and the complete drain loop -- handing an arbitrary continuation triple the drained gate state (`drain_pending_abs`), the preserved live/priority context, and a yield word equal to `resume_pending_requires_yield`.  During this composition the loop-carried yield word was found to be C `long` (`int` after translation) while the named factors had been authored at `32 signed word` -- print-identical, type-different, silently blocking every unification against the real wrapper; the whole stack is retyped `int` and every session re-elaborates green. | The continuation premise (missed-tick replay segment, final yield branch, critical exit) is honest and open pending the unlocked `vTaskIncrementTick'` source summary; with `resume_missed_generated_loop_replays` its loop layer is already closed, so the open core is exactly the tick body.  Still zero refinement rungs; the **0/5** score stands. |

#### Tick body: the post-Event preservation contract and the tail insertion

| Result and evidence | Exact checked scope | Boundary that remains |
|---|---|---|
| `one_due_gateH_after_event_obligations`; QAD-false run `20260804Tone-due-after-event-02` | After the tick body's Generic removal and the branch's Event removal (or NULL skip), the shrunk delayed source, the untouched ready target and every other Generic ring survive by exact-footprint framing against the gate's storage separation (the shrunk source through storage monotonicity); the linked owner ring loses exactly the due task's Event item; insert freshness is carried verbatim. | Family layer only. |
| `one_due_gateH_priority_after_eventD`; QAD-false run `20260804Tone-due-priority-frame-02` | Every live task's four-byte priority field survives both removals: the Generic footprint stays in the source storage, the Event footprint in the owner storage, both separated from every priority field by the capstone geometry; the structure projection transports by field-pointer congruence. | One observation field; owner and key observations through the second removal are not yet packaged. |
| `one_due_tail_source_split` and `one_due_tick_tail_insert_composed`; QAD-false runs `20260804Tone-due-tail-insert-01`, `20260804Tone-due-tail-insert-11` | The generated top/ready tail is exactly the top-raise conditional, the in-range and array guards, the ready selection and the generated insert followed by a named delayed-head remainder; and from the state after both removals that tail executes through `vListInsertEnd'`: both top-raise outcomes read the preserved priority, the guards discharge from the observation bound and the frozen base address, the selection returns the gate's target root, and the insert produces the exact insert heap over the after-event target ring.  The remainder is received by a continuation pinned only to that exact heap and the untouched delayed-root pointer. | The delayed-head read at the post-insert heap, the gateH re-entry for the next due task, and the complete `vTaskIncrementTick'` while body remain open. |
| `one_due_insert_family_pre_rel`, `one_due_source_rel_at_insert`, the storage-separation pack `scheduler_family_pre_rel_storage_disjoint`, and `one_due_tick_delayed_remainder_exact`; QAD-false runs `20260804Tone-due-delayed-head-04` through `-13` | The due task's Generic item is globally unlinked after its removal, so the accepted insert-end preservation theorem carries the **whole packaged Generic family** to the exact insert heap, in particular the shrunk delayed ring; every remaining delayed member's owner field survives all three writes by exact-footprint framing; and the generated delayed-head re-read -- root guard, count test, sentinel guards, owner read -- executes at that heap leaving the state unchanged and returns exactly the next due candidate: NULL for an empty ring, otherwise the preserved owner of the head node.  Together with the tail-insert composition the generated tick-body tail is closed end to end from the gate state. | The returned owner is not yet decoded to a task identity (relabel/decoder step), the gateH re-entry for the next due task and the complete `vTaskIncrementTick'` while body with its loop condition remain open, as does the wrapper.  Still zero refinement rungs; the **0/5** score stands. |
| `one_due_source_member_decode` / `one_due_next_head_owner_decode` and `one_due_reentry_entry_rel` with the component pack (`one_due_reentry_context/snapshot`, register/top/payload/family equations, `one_due_reentry_family_shape`); QAD-false runs `20260804Tone-due-delayed-head-15`, `20260804Tone-due-reentry-pure-19` | The preserved head owner decodes through the gate's relabel and decoder laws to a **live task identity** -- the next due candidate is a task, not a pointer.  At the pure phase level the re-entry witnesses (context advanced to that task with the entry top raised to `max`, snapshot equal to the completed five-phase state with capture/check registers cleared) satisfy the full `one_due_entry_rel` again: `family_shape'` is re-derived clause by clause through the model-level remove/insert-end lemmas (well-formedness, ring sets, pairwise disjointness by a membership characterization of the moved node, key/payload preservation), and head/membership/key/dueness/top transport by the component equations.  Root membership of the new ready target, the next head's dueness and the branch' witness stay explicit premises for the gate layer. | Pure layer only: the gate-level (post-insert heap) clauses -- raw families, relabel at the insert heap, key/observation/event transports, the concrete globals (raised `uxTopReadyPriority`, unchanged `xTickCount`) -- are not yet re-established, and the while-loop induction and wrapper remain open.  Still zero refinement rungs; the **0/5** score stands. |
| `one_due_reentry_generic_pre_rel` / `one_due_reentry_generic_ring_subset`, the strengthened `one_due_tick_tail_insert_composed` continuation, `one_due_reentry_relabel_closed` with the key chain (`one_due_reentry_key_he`, `raw_remove_concrete_heap_key_at_removed`, `one_due_event_remove_source_item_bytes_frame`) and the model transports (`xlist_relabel_remove` / `xlist_relabel_insert_end`); QAD-false runs `20260804Tone-due-reentry-gateH-06/-07/-08` | Three gate clauses re-established at the re-entry family and insert heap with **no key premise left**: the packaged Generic `scheduler_family_pre_rel`, the managed-set ring subset, and the per-root relabel to the re-entry snapshot -- source through the decode-aligned remove transport, target through the insert-end transport (freshness from the after-event obligations, ring injectivity from the decoder laws), the moved node's key carried from the entry heap through its own removal (neighbour-field/list-header/container-only writes) and the Event removal (whole-item outside the exact footprint by storage separation).  The tail-insert continuation now also pins the concrete globals the gate re-entry needs: `uxTopReadyPriority` as the exact raised-or-kept conditional and `xTickCount` untouched. | Remaining gate clauses at the insert heap: TaskObservation, the Event family relation, delay-owner/insert-geometry, scalar/root equations, and the storage-disjointness pack at the new families; then the full gate re-entry assembly, the while-loop induction and the wrapper.  Still zero refinement rungs; the **0/5** score stands. |
| `one_due_reentry_task_observation` with the nine step frames (`one_due_{generic_remove,event_remove,ready_insert}_{generic,event}_owner_live`, `one_due_ready_insert_priority_live`), the rebuilt event pre-relation `one_due_gateH_event_pre_after_genericD` and the ring exclusion `one_due_gateH_generic_notin_event_ringD`; QAD-false run `20260804Tone-due-reentry-gateH-12` | The **full task observation relation holds at the insert heap** against the unchanged abstract state: for every live task the priority word, the Generic-item owner and the Event-item owner survive the Generic removal (member frame at the moved node itself or sibling item frame), the branch-cased Event removal (the event family's packaged pre-relation rebuilt at the after-generic heap from the per-root transports; Generic-vs-Event ring exclusions from the decoder laws), and the ready insertion (the membership-free owner byte frame; the capstone sibling frame for the priority word with the due task's Event item as witness).  Guards and abstract priorities are heap-independent. | Event family relation, delay-owner/geometry, scalar/root equations and storage disjointness at the new families are still open at the insert heap, then the gate re-entry assembly, the while-loop induction and the wrapper.  Still zero refinement rungs; the **0/5** score stands. |
| `one_due_reentry_event_family_rel` with `one_due_reentry_event_{root_raw_rel,root_rep,key_rep,pre_rel}` and the event-side decoder kit; QAD-false runs `20260804Tone-due-reentry-gateH-13` through `-16` | The **packaged event-root family relation holds at the insert heap** for the after-removal raw family and the re-entry snapshot families: every event ring's raw relation is carried through both removals (the linked owner at its removed shape from the after-event obligations, other roots by family storage separation and exact footprints) and the insertion (framed off the whole event side against both the ready target and the delayed source); per root the ring subset, the relabel through the remove transport at the due task's decoded Event identity, and the abstract shape clauses from the pure re-entry family shape; every live task's Event key survives all three writes and the abstract keys transport through the snapshot equations; the pre-relation's heap-free clauses inherit through the removal subsets. | The container representation at the insert heap is the one explicit premise of the assembly (its per-item transport is the next rung); then the delay-owner/geometry/scalar/root equations, storage disjointness at the new families, the gate re-entry assembly, the while-loop induction and the wrapper.  Still zero refinement rungs; the **0/5** score stands. |

Gate H therefore remains open.  In particular, no accepted generated-source
theorem yet covers arbitrary
missed-tick debt at source level (the unlocked `vTaskIncrementTick'` summary
is still an explicit premise wherever it appears), the complete zero/one/$N$
due prefix (including equal-key tasks and the exact first-not-due stop),
tick-wrap role exchange with its reachable
old-current-empty invariant, both internal and caller yield results, or the
complete positive-delay `vTaskDelay'` composition.  The outer
`xTaskResumeAll'` wrapper is composed through the drain loop with the
missed-tick segment as its one open premise (see the wrapper row above).  Concurrent interrupt correctness additionally
requires the separately declared interference or rely/guarantee model; it is
not implied by these sequential source theorems.

### Gate D -- five-root dispatcher and trace gate

Prove Level B for the other four roots, the required helper closure, the formal
branch-completeness ledger, and preservation of the common invariant.  Finish
with a single dispatcher refinement and its arbitrary finite-call trace
corollary.  Gate D does not include the additional obligations of Level C.

No report may use "universal scheduler correctness" unless Gates L, H, and D
are all checker-green under the same frozen source, configuration, relation,
and invariant ledger.
