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

### Gate D -- five-root dispatcher and trace gate

Prove Level B for the other four roots, the required helper closure, the formal
branch-completeness ledger, and preservation of the common invariant.  Finish
with a single dispatcher refinement and its arbitrary finite-call trace
corollary.  Gate D does not include the additional obligations of Level C.

No report may use "universal scheduler correctness" unless Gates L, H, and D
are all checker-green under the same frozen source, configuration, relation,
and invariant ledger.
