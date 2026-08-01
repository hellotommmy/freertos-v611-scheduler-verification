# Scheduler abstract-model and representation design

Status: `DESIGN_ONLY__SOURCE_TRACE_DERIVED__NO_ISABELLE_RUN`

This document proposes the next blind-reconstruction layer above the
checker-green pure `xlist_abs` model.  It was derived only from the five frozen
FreeRTOS V6.1.1 roots, their source-only closure, the independent scheduler
trace, the named proof-port contract, and the local raw-list design.  The
sealed original formalisation was not inspected.  No Isabelle command was run
and no existing theory was changed while producing this design.

The five roots are:

- `xTaskGetTickCount`;
- `vTaskDelay`;
- `vTaskDelayUntil`;
- `vTaskIncrementTick`; and
- `vTaskSwitchContext`.

Their closure adds `vTaskSuspendAll`, `xTaskResumeAll`, and the five stock
list bodies.  The configuration fixes four priorities, 32-bit ticks, and
preemption enabled, with tick hooks, runtime statistics, trace code, and
stack-overflow hooks inactive.

Two evidence boundaries must remain visible:

1. `XList_Model` is checker-green as a pure, allocation-free list model.
   The arbitrary-ring raw-heap representation and simulations are still proof
   obligations; the current raw source-to-abstract theorem is only the fixed
   empty-to-singleton insert case.
2. `20260731Tscheduler-trace-02-independent` is reproducible source execution
   evidence: four scenarios, 39 records, 13 snapshots, 25 checks, and no fatal
   record.  It discovers state deltas and kills invariants; it is not a
   scheduler refinement proof.  Its scenarios cover unsuspended tick and
   switch behavior only; delay, suspend/resume, pending-ready, missed-tick,
   and tick-read semantics below are source-derived and not trace-tested.

The load-bearing source anchors are `tasks.c:604-674` (delay-until),
`681-735` (delay), `1098-1175` (suspend/resume), `1188-1200` (tick read),
`1397-1424` (active tick branches), and `1593-1640` (context switch), plus
`list.h:187-198` and `217` for cursor-relative and sentinel-head owner access.
The active macro choices come from `proof_port/scheduler/FreeRTOSConfig.h`,
not from assumptions inferred from a trace.

## 1. Design decisions forced by the source

The model must preserve the following source distinctions.

### 1.1 List item identity is not task ownership

Every TCB contains two distinct nodes:

```text
Generic t = address of t.xGenericListItem
Event t   = address of t.xEventListItem
```

Both have the same `pvOwner`, namely the TCB pointer.  They may be in two
lists simultaneously: a blocked task's generic item can be in a delayed list
while its event item is in an event-wait list.  Therefore neither the owner
pointer nor the abstract task ID may be used as the list-node ID.

Use an explicit sum type at the scheduler layer:

```text
datatype 'tid sched_item = Generic 'tid | Event 'tid

item_owner (Generic t) = t
item_owner (Event t)   = t
```

`item_owner` is deliberately not injective.  Node-level distinctness is
proved before applying `item_owner`; task-level distinctness after projection
uses a role-homogeneity invariant for the particular list.

### 1.2 Current means the source selection pointer

`pxCurrentTCB` is changed by `vTaskSwitchContext`, not by
`vTaskIncrementTick` and not by the sequential proof-port `yield` body.
Consequently a positive `vTaskDelay` removes the current task's generic item
from ready state, places it in a delayed list, requests a yield, and returns
while `pxCurrentTCB` still points to that blocked task.

The abstract field named `current` therefore denotes the TCB selected by the
source variable.  Core well-formedness requires it to name a live task, but
does not require it to be ready.  A stronger `dispatch_settled` predicate says
that it is ready; this predicate is restored by a successful context switch
and is a normal external precondition, but it is not a global invariant of
every source API endpoint.

### 1.3 Top-ready priority is a cache, not always an exact maximum

Adding a ready task raises `uxTopReadyPriority`, but removing the last task at
the top priority does not lower it.  `vTaskSwitchContext` performs the downward
search and repairs it.  The core invariant is therefore:

```text
top_ready < 4
every nonempty ready priority is <= top_ready
some ready priority at or below top_ready is nonempty
```

Equality with the maximum nonempty priority belongs to `dispatch_settled`,
not to core well-formedness.  The scheduler trace happened to snapshot only
states where the cache was exact; that trace gate must not be generalised to
all source endpoints.

### 1.4 Delayed roles are semantic pointers, not object names

The two physical roots `xDelayedTaskList1` and `xDelayedTaskList2` never move.
The pointers `pxDelayedTaskList` and `pxOverflowDelayedTaskList` assign them
the semantic roles `CurrentDelay` and `OverflowDelay`.  At tick wrap the
pointers swap; nodes stay in their physical rings.

The scheduler model stores semantic current/overflow queues.  The raw relation
separately records which physical list currently implements each role.

### 1.5 Ready order is cursor-relative

The concrete ring and the scheduler FIFO are different observations of the
same `xList`.  If `ring = A,B,C` and `cursor = C`, the next selections are
`A,B,C,A`.  A context switch changes the cursor and current task but preserves
the physical ring.  A model that selects the sentinel-next node unconditionally
is false.

## 2. Isabelle-shaped abstract vocabulary

The declarations below are design notation, not checked Isabelle syntax.

```text
type_synonym priority = nat              -- constrained to {0,1,2,3}
type_synonym tick32 = 32 word

datatype delay_role = CurrentDelay | OverflowDelay
datatype 'tid sched_item = Generic 'tid | Event 'tid

datatype 'event event_place =
    EventDetached
  | EventWaiting 'event
  | EventPending

record task_abs =
  priority   :: priority
  wake       :: tick32 option

record port_abs =
  critical_depth     :: 32 word
  interrupts_disabled :: bool
  yield_count         :: 32 word

record ('tid, 'event) scheduler_abs =
  tick              :: tick32
  wraps             :: nat
  current           :: 'tid option
  ready             :: priority => 'tid list
  delayed_current   :: 'tid list
  delayed_overflow  :: 'tid list
  pending_ready     :: 'tid list
  suspended         :: 'tid set
  event_waiters     :: 'event => 'tid list
  tasks             :: 'tid => task_abs option
  top_ready         :: priority
  scheduler_suspended :: nat
  missed_ticks      :: nat
  missed_yield      :: bool
  port              :: port_abs
```

`wraps` is a logical epoch count related to `xNumOfOverflows`.  A source
simulation of a wrap needs a bound preventing signed overflow of that concrete
counter.  The logical time used in specifications may be written

```text
logical_now s = 2^32 * wraps s + unat (tick s).
```

This does not claim an unbounded concrete counter: the relation and each wrap
theorem carry the concrete range premise.

The top-level collections are authoritative.  A derived `generic_place s t`
reports membership in exactly one ready, delayed, or suspended collection; a
derived `event_place_of s t` returns the `event_place` value determined by
`pending_ready`, one external event queue, or detachment.  Keeping placement
derived avoids duplicated mutable fields while still making the two item roles
explicit.

`event_waiters` is an open-world auxiliary resource.  Event lists are not
global roots in the five-root slice, but `vTaskIncrementTick` can follow a
non-null event-item container and remove that node.  Omitting all event-list
state would make that source write impossible to simulate or frame.

## 3. Reusing `xlist_abs`

### 3.1 Cursor-relative and ordered views

For a well-formed `xlist_abs`, define:

```text
fifo_view xs =
  case cursor xs of
    None   => ring xs
  | Some c =>
      if ring xs = before @ [c] @ after
      then after @ before @ [c]

ordered_view xs = ring xs
```

The decomposition around `c` is unique because `ring` is distinct and the
cursor is a member.  The required list-view lemmas are:

```text
fifo_view (list_insert_end_abs x k xs) = fifo_view xs @ [x]

fifo_view (list_remove_abs x xs) = remove1 x (fifo_view xs)
  when x is a member

if fifo_view xs = x # rest, then advancing the concrete cursor once gives
  fifo_view xs' = rest @ [x]
  ring xs' = ring xs

ordered_view (list_insert_ordered_abs x k xs)
  = stable insertion of x by k into ordered_view xs
```

The first equation is valid even when `cursor = None` and `ring` is nonempty:
ordered insertion can leave a nonempty list with a sentinel cursor, and
insert-end then puts the new node at the raw head but at the FIFO tail.

Ready queues use `fifo_view`.  Current and overflow delayed queues use
`ordered_view`.  Pending-ready uses sentinel-head ring order because
`xTaskResumeAll` repeatedly calls `listGET_OWNER_OF_HEAD_ENTRY`; it does not
select relative to the cursor.  Suspended scheduling semantics needs only the
member set, although the raw relation continues to preserve its full ring and
cursor.

The raw scheduler relation also needs role-specific cursor discipline inherited
from initialisation and the reachable operations:

- both delayed-list cursors remain at the sentinel, because ordered insert and
  remove never advance them in this closure;
- pending-ready and suspended cursors are sentinel when empty and the raw ring
  tail when nonempty, preserved by insert-end and removals; and
- ready cursors are unrestricted counted members/sentinel and are interpreted
  only through `fifo_view`.

Without the pending tail property, a later insert-end could splice into the
middle of the raw ring and sentinel-head order would not be an abstract queue
append.

### 3.2 Relabelling the pointer-based raw relation

The raw-list design intentionally uses an `xLIST_ITEM_C ptr` as the node ID.
Do not replace that relation with an owner-based relation.  Reuse it through a
separate bijection over the live node universe:

```text
node_ptr  :: 'tid sched_item => xLIST_ITEM_C ptr
decode    :: xLIST_ITEM_C ptr => 'tid sched_item option

node_ptr (Generic t) = address of tcb_ptr(t).xGenericListItem
node_ptr (Event t)   = address of tcb_ptr(t).xEventListItem

decode (node_ptr i) = Some i
node_ptr is injective on live scheduler items
```

Given a pointer-identified list `pxs` whose ring and cursor are in the live
node universe, define `relabel decode pxs` by:

```text
ring      = map (the o decode) (ring pxs)
cursor    = map_option (the o decode) (cursor pxs)
item_key i = item_key pxs (node_ptr i)
```

Prove relabelling commutes with the three pure list operations:

```text
relabel (list_insert_end_abs (node_ptr i) k pxs)
  = list_insert_end_abs i k (relabel pxs)

relabel (list_insert_ordered_abs (node_ptr i) k pxs)
  = list_insert_ordered_abs i k (relabel pxs)

relabel (list_remove_abs (node_ptr i) pxs)
  = list_remove_abs i (relabel pxs)
```

These equations let the general raw list simulations remain pointer-based and
let scheduler proofs use `Generic t` and `Event t`.  Owner agreement is an
additional predicate:

```text
pvOwner (node_ptr i) = tcb_ptr (item_owner i).
```

It validates projection from a selected list item to a task.  It is never used
to identify the list item itself.

## 4. Layered well-formedness

Define `scheduler_wf` as named layers rather than one unfolded conjunction.

### WF-0: finite live task universe and scalar bounds

- `live s = {t. tasks s t != None}` is finite;
- every live task has priority below 4;
- every task mentioned by any collection is live;
- `top_ready < 4`;
- suspension, missed-tick, list-count, port, and wrap counters are within the
  bounds needed by the next source operation.

The counter bounds are operation preconditions where possible.  They should
not be hidden behind mathematical naturals while the source uses finite C
integers.

### WF-1: generic-item partition

Each live task's `Generic t` occurs in exactly one of:

```text
one ready[p]
delayed_current
delayed_overflow
suspended
```

All these collections are duplicate-free and pairwise disjoint by task ID.
This is a partition of the generic item role, not a claim that a task occurs
in only one concrete list overall.

### WF-2: event-item partition

Each `Event t` occurs in at most one of:

```text
pending_ready
one event_waiters[e]
```

or is detached.  Pending entries are distinct.  If `t` is pending, its generic
item is still in a delayed or suspended collection, because
`xTaskResumeAll` unconditionally removes that generic item before making the
task ready.  A task may simultaneously be in a delayed collection through
`Generic t` and an event queue through `Event t`.  Conversely, a task in a
ready queue has a detached event item at a stable root boundary.

### WF-3: ready queues and top cache

- every `t` in `ready[p]` has `priority t = p`;
- each ready sequence is the owner projection of a homogeneous generic-item
  `fifo_view`;
- at least one ready queue is nonempty (normally supplied by the idle task);
- every nonempty ready priority is at most `top_ready`.

The stronger predicate

```text
top_exact s = top_ready s = Max {p. ready s p != []}
```

is kept separate.

### WF-4: delayed queues and modular time

- both delayed sequences contain only generic items and are disjoint;
- each is nondecreasing by the task's semantic wake key;
- `t` is in either delayed sequence iff `wake t = Some k` for its key `k`;
- every current-delay key satisfies `tick < k` in unsigned word order;
- every overflow-delay key satisfies `k < tick`.

The strict inequalities describe stable transition boundaries after due tasks
have been removed.  At `tick = UINT32_MAX`, the current delayed queue is empty
as a consequence.  At wrap, the roles swap first and the due prefix at key
zero is then removed, restoring the stable inequalities.

No ordering constraint is placed on stale generic-item keys for ready or
suspended tasks.  The source does not reset an item's key when inserting it
into a ready list.

### WF-5: current and settled dispatch

Core WF requires only:

```text
current = None or current names a live task.
```

For normal root entry and after a successful context switch, use:

```text
current_ready s =
  current s = Some t and t occurs in ready s (priority t)

dispatch_settled s = current_ready s and top_exact s.
```

A positive delay preserves core WF but may falsify both conjuncts of
`dispatch_settled` until the environment services the yield request.

### WF-6: suspension and deferred work

- if `scheduler_suspended = 0`, then `pending_ready = []` and
  `missed_ticks = 0` at a quiescent API boundary;
- if pending is nonempty, suspension is positive;
- `missed_yield` records a switch request attempted while suspended;
- replay of missed ticks has the current source tick fixed until final resume;
- final resume drains pending tasks before replaying missed ticks, matching
  source order.

### WF-7: proof-port boundary

At a quiescent public boundary:

```text
critical_depth = 0
interrupts_disabled = False.
```

For nested internal states, positive critical depth implies interrupts are
disabled.  `yield_count` is a modular observable counter, not a current-task
update and not proof of a hardware context switch.

## 5. Pure transition vocabulary

The root semantics should be assembled from small executable helpers.

### 5.1 Ready append

`ready_append t` appends `t` to the cursor-relative FIFO at its task priority,
sets `wake t := None`, and raises `top_ready` only when the new priority is
greater than the old cache.  It does not change `current`.

### 5.2 Block current

For a positive delay, `block_current k`:

1. requires `current = Some t` and `t` in its priority's ready FIFO;
2. removes `t` from that FIFO without lowering `top_ready`;
3. sets `wake t := Some k`;
4. stably inserts `t` into overflow delayed if `k < tick`, otherwise into
   current delayed; and
5. leaves `current = Some t`.

For a source-admissible positive delay the current-role case has `tick < k`.

### 5.3 Wake due prefix

`wake_due now` splits `delayed_current` into the longest prefix whose wake key
is `<= now` and the first future-key suffix.  In prefix order, for each task it:

- removes `Event t` from its external event queue when attached;
- detaches the event role;
- clears the semantic wake;
- appends `t` to its priority ready FIFO; and
- leaves `current` unchanged.

Sortedness justifies stopping at the first future key.  Equal-key wakeups keep
their stable delayed order and are appended to the corresponding ready FIFO in
that order.

### 5.4 One unsuspended tick

`tick_unlocked` performs:

```text
new_tick = tick + 1 modulo 2^32
if new_tick = 0:
  swap(delayed_current, delayed_overflow)
  wraps := wraps + 1
tick := new_tick
wake_due new_tick
```

The physical-list swap is not part of this pure state update; it is discharged
by the raw delayed-role relation.

### 5.5 Context selection

`switch_unlocked` searches downward from the cached `top_ready` to the first
nonempty ready FIFO.  If that FIFO is `t # rest`, it sets:

```text
top_ready := selected priority
current := Some t
ready[selected] := rest @ [t]
```

The rotation is an observation of a cursor advance.  At the underlying list
layer the ring, links, count, keys, containers, and owners are framed.

## 6. Five root semantics

### 6.1 `xTaskGetTickCount`

Abstract signature:

```text
get_tick_abs s = (tick s, s with the proof-port enter/exit pair)
```

At a quiescent port boundary the entire abstract state is unchanged and the
return value is the old tick.  For a nested critical prestate, model the named
port bodies exactly: enter increments depth and disables interrupts; exit
decrements depth and enables interrupts only when depth becomes zero.

No list, current, scheduler-control, or yield field changes.

### 6.2 `vTaskDelay`

For a quiescent, dispatch-settled prestate with no deferred work:

```text
delay_abs 0 s = request_yield s

delay_abs n s, n > 0:
  k = tick s + n modulo 2^32
  s1 = block_current k s
  result = request_yield s1
```

Thus zero delay changes no scheduler collection and requests one yield.  A
positive delay moves only the current task's generic item, leaves its event
item detached, leaves `current` unchanged, does not lower `top_ready`, and
requests exactly one yield through the proof-port counter.

The exact general semantics is the source composition:

```text
if n > 0:
  suspend_one;
  block_current;
  (already_yielded, s') = resume_all_abs;
else:
  already_yielded = False;
if not already_yielded then request_yield.
```

The first refinement rung should use the quiescent simplification.  General
nested suspension and deferred-work composition should be proved only after
`resume_all_abs` is independently green.  Without the sequential atomicity
rely, an ISR can add missed ticks between suspend and resume and replay can
wake the just-delayed task before return; therefore “positive delay implies
delayed membership in every poststate” is not a source theorem without that
rely or an explicit no-replay premise.

### 6.3 `vTaskDelayUntil`

Treat the caller's `*pxPreviousWakeTime` as an explicit input/output cell, not
as a hidden scheduler field:

```text
k = previous + increment modulo 2^32

should_delay(now, previous, k) =
  if now < previous
  then k < previous and now < k
  else k < previous or now < k
```

The output cell is unconditionally updated to `k`.  If `should_delay` is true,
apply `block_current k`; otherwise leave all scheduler collections unchanged.
As in `vTaskDelay`, the suspend/resume composition ends with exactly one proof-
port yield request at a quiescent boundary.  The operation does not directly
select another current task.

The proof must retain all four modular comparison branches.  Replacing them
with the ordinary-integer claim `now < previous + increment` loses the
source's wrap logic.

### 6.4 `vTaskIncrementTick`

```text
if scheduler_suspended > 0:
  missed_ticks := missed_ticks + 1
else:
  tick_unlocked
```

The suspended branch changes no tick, queue, current, top-ready, delayed role,
or port field.  The unlocked branch increments the tick, optionally swaps
delayed roles and increments `wraps`, wakes the due prefix, and appends each
woken task to ready state.  It never changes `current` and issues no proof-port
yield request in the frozen configuration.

The trace provides three concrete witnesses: future key remains blocked,
equal key wakes without switching current, and real `UINT32_MAX -> 0` swaps
roles while leaving a key-1 node in its physical list until tick 1.

### 6.5 `vTaskSwitchContext`

```text
if scheduler_suspended > 0:
  missed_yield := True
  all other fields unchanged
else:
  switch_unlocked
```

The unlocked branch requires the cached priority bound and a nonempty ready
witness at or below it.  It restores `top_exact` and `current_ready`, advances
only the selected list cursor, and frames all list rings.  It does not clear a
pre-existing `missed_yield`; final resume is the source location that clears
that flag after requesting a yield.

## 7. Load-bearing closure semantics

Although not roots, suspend and resume must have explicit abstract contracts.

`vTaskSuspendAll` increments `scheduler_suspended` and changes nothing else.
The theorem requires that the finite concrete counter does not wrap.

Scheduler suspension is not interrupt exclusion.  The sequential root model
uses the allowed atomic API-boundary rely: no unmodelled ISR step is interleaved
inside the source call.  A later concurrent environment model must permit ISR
steps to add pending-ready items or missed ticks while the nesting counter is
positive and must prove that those are the only shared-state effects.  This
rely is distinct from the proof-port critical-depth contract.

`xTaskResumeAll` requires positive suspension depth and models the named
critical enter/exit bodies.  After decrement:

- if depth remains positive, it returns false and performs no deferred work;
- if depth reaches zero and live tasks exist, it drains `pending_ready` in
  sentinel-head order.  For each task it removes the event item from pending,
  removes the generic item from its delayed or suspended location, and appends
  the generic item to its ready FIFO;
- it then runs `tick_unlocked` exactly `missed_ticks` times, decrementing the
  missed counter after each source call;
- with preemption enabled, any replayed tick requires a yield; a pending task
  with priority at least the source-current task also requires a yield;
- if that condition or `missed_yield` holds, it clears `missed_yield`, requests
  one proof-port yield, and returns true; otherwise it returns false.

The drain-before-replay order is proof-relevant.  A monolithic recursive proof
should be avoided: prove one pending-head step, list-length induction for the
drain, one unlocked tick, and natural-number induction for replay, then compose
the return/yield cases.

## 8. Raw scheduler representation relation

Define `raw_scheduler_rel c s` as independently named layers.

### RR-0: concrete layout and allocation

- the four ready roots, two physical delayed roots, pending root, and suspended
  root are distinct valid list objects;
- live TCB roots are distinct and disjoint from all list roots;
- each TCB's generic and event item subobjects have the generated offsets and
  do not alias one another;
- real item roots and embedded list sentinels obey the prefix-safe raw-list
  allocation discipline; no full `xLIST_ITEM_C` is allocated over a mini
  sentinel;
- caller-owned `pxPreviousWakeTime` for delay-until is valid and separated from
  the scheduler footprint required by the operation.

### RR-1: TCB and item injections

Use an injective partial map `tcb_ptr :: tid => tskTCB ptr` over live tasks and
derive `node_ptr` from field addresses.  Require:

```text
decode(node_ptr(Generic t)) = Some(Generic t)
decode(node_ptr(Event t))   = Some(Event t)
pvOwner(node_ptr(Generic t)) = coerce(tcb_ptr t)
pvOwner(node_ptr(Event t))   = coerce(tcb_ptr t)
```

The first two equations establish node identity.  The last two establish
owner agreement.  They are not interchangeable.

### RR-2: one raw `xlist_abs` relation per concrete list

Relate each physical list to a pointer-identified `xlist_abs` using the general
raw list relation, then relabel it to scheduler items:

- ready list `p`: only `Generic t` with priority `p`;
- physical delayed lists 1 and 2: only `Generic t` with semantic wake keys;
- pending-ready list: only `Event t`;
- suspended list: only `Generic t`;
- each represented external event list: only `Event t`.

This layer owns ring shape, cursor, count, links, keys, and containers.  The
scheduler relation must not duplicate those byte-level predicates.

### RR-3: scheduler views

- `ready p = map item_owner (fifo_view ready_xlist[p])`;
- the semantic delayed sequences are owner projections of ordered ring views;
- `pending_ready` is the owner projection of the pending ring, not its
  cursor-relative FIFO view;
- `suspended` is the owner projection of the suspended member set;
- event waiter sequences are owner projections of event-item rings.

Role homogeneity is used before projecting with non-injective `item_owner`.

### RR-4: delayed physical-role permutation

Exactly one of two cases holds:

```text
pxDelayedTaskList         = &xDelayedTaskList1
pxOverflowDelayedTaskList = &xDelayedTaskList2

or

pxDelayedTaskList         = &xDelayedTaskList2
pxOverflowDelayedTaskList = &xDelayedTaskList1.
```

`delayed_current` and `delayed_overflow` select the corresponding physical
`xlist_abs` views.  A wrap proof changes this two-case selector and source
pointers; it does not prove or require any node-copying theorem.

### RR-5: task fields and membership closure

- concrete `uxPriority` equals abstract priority;
- when a task is delayed, its generic item key equals the semantic wake;
- no key agreement is required for a generic item outside delayed roles;
- concrete container pointers agree exactly with the derived generic/event
  placement;
- every represented container member has the corresponding container pointer,
  and every non-null represented item container identifies its unique list;
- ready tasks have detached event items; pending and event-wait placements
  agree with the event item container.

### RR-6: scheduler scalar globals

Relate `xTickCount`, `pxCurrentTCB`, `uxTopReadyPriority`, suspension depth,
missed ticks, missed yield, and overflow count to their abstract fields.
Relate `uxCurrentNumberOfTasks` to `card (live s)` under the finite-live and
machine-word bound; the source uses its zero/nonzero test in final resume.
`pxCurrentTCB = NULL` corresponds to `current = None`; otherwise it must equal
`tcb_ptr t` for the abstract current task.

### RR-7: proof-port and frame

Relate the three named proof-port globals exactly.  Keep an explicit external
heap frame for stacks, task names, inactive TCB fields, unrelated event lists,
and caller memory.  A per-root write-set lemma should show which part of this
frame is preserved.

## 9. Concrete preimage and counterexample scenarios

Each abstract constructor and major branch needs a concrete preimage before a
general refinement theorem is attempted.

| ID | Preimage | Expected source/abstract delta |
|---|---|---|
| P0 | One idle/runner generic item in `ready[0]`, tick 5, quiescent port. | `xTaskGetTickCount` returns 5 and frames all scheduler state. |
| P1 | Current `A` ready at priority 2, delay 0. | No list change; current remains `A`; yield count increments once. |
| P2 | Current `A` ready at priority 2 plus an idle lower-priority witness, tick 5, delay 2. | `A` moves to current delayed at key 7; current still `A`; top cache may remain 2 although priority 2 became empty; one yield request. |
| P3 | Same shape at tick `UINT32_MAX-1`, delay 3. | Wake key 1 is inserted into overflow delayed; physical delayed roles do not swap yet. |
| P4 | Delay-until with now 12, previous 10, increment 1. | Previous becomes 11, no blocking occurs, and one yield is requested. |
| P5 | Delay-until with now `UINT32_MAX-2`, previous `UINT32_MAX-3`, increment 5. | Wake 1 satisfies the source no-prior-wrap branch (`wake < previous`) and current is placed in overflow delayed. |
| P6 | Trace `tick_no_wake`: tick 5, key 7 current-delayed. | Tick becomes 6; queues/current unchanged. |
| P7 | Trace `tick_wakes_delayed`: tick 9, high task key 10, low current. | High moves to `ready[3]`, top rises to 3, current remains low. |
| P8 | Trace wrap: tick max, old current delay empty, key 1 in old overflow. | Tick 0, physical role pointers swap, node stays in physical list, wraps increments; tick 1 wakes it. |
| P9 | Trace FIFO: ring `A,B,C`, cursor `C`, all priority 2. | Four switches select `A,B,C,A`; ring and links are framed. |
| P10 | Positive suspension depth with current `A`. | Switch changes only `missed_yield` to true. |
| P11 | Final resume with pending high event item, its generic item delayed, and missed ticks. | Pending drains before replay; generic becomes ready, event becomes detached, missed ticks reach zero, and one yield is requested. |

P2 and P3 are now executable untouched-source witnesses in run
`20260731Tscheduler-trace-03-delay-phases`.  P2 concretely kills both “current
is always ready” and “top-ready is always exact” at the explicit
`YieldPending` boundary; P3 distinguishes arithmetic wake-time wrap from the
later tick-time physical-role swap.  They remain execution evidence, not
source-to-abstract theorems.

## 10. False invariants that must remain dead

| False claim | Source or trace killer |
|---|---|
| Owner/TCB pointer uniquely identifies a list node. | Generic and event items of one TCB have the same owner and distinct containers. |
| A task belongs to exactly one concrete list. | Its generic delayed item and event-wait item can be linked simultaneously. |
| Pending-ready stores the generic item. | The source inserts/removes `xEventListItem`; the generic item remains blocked until resume. |
| Current is always a member of a ready queue. | Positive delay blocks the selected task before the proof-port yield is serviced. |
| Current is always the highest-priority ready task. | Tick can ready a higher task while leaving current unchanged; positive delay can leave current blocked. |
| Current always equals the owner at its ready-list cursor. | The trace prestate has current `A` while insertion has left the same-priority cursor at `C`. |
| `uxTopReadyPriority` is always the exact maximum nonempty priority. | Removing the sole top-priority current task does not lower the cache. |
| Tick wakeup immediately changes current to a newly readied higher task. | P7: only a later switch changes current. |
| Yield-counter increment is a context switch. | The named port body increments only `eal6_port_yield_count`. |
| The named object `xDelayedTaskList1` is always current delayed. | P8 swaps semantic role pointers. |
| Wrap moves nodes between physical delayed objects. | P8 keeps the key-1 node in physical list 2 while its role changes. |
| Every delayed key is numerically greater than the current tick. | Overflow-delay keys are below the pre-wrap tick. |
| Every `xList` is sorted. | Ready and generic lists use insert-end; only ordered roles need key monotonicity. |
| Cursor is always sentinel or raw ring tail. | Insert-end and owner-of-next traces place it at other real nodes. |
| Same-priority selection always chooses sentinel-next. | Selection is after the current cursor; P9 exposes the difference. |
| Delay-until always blocks for positive increment. | P4 updates the previous wake cell but does not block. |
| Positive `vTaskDelay` always returns with the task delayed. | Under an interleaving environment, missed ticks accumulated during suspension can be replayed before return and wake it. |
| `xTaskResumeAll` merely decrements suspension. | Final resume drains pending tasks and replays missed ticks. |
| Scheduler suspension is Boolean or disables interrupts. | It is a nesting counter; ISR work is deferred through pending-ready and missed-tick state. |
| Missed ticks can be replaced by one batched tick addition and wake scan. | Source replays one modular tick at a time, including wrap-role swap and each intermediate due prefix. |
| A ready insertion resets the generic item key. | `vListInsertEnd` does not write the key; ready keys may be stale. |

## 11. Dependency-ordered lemma graph

The graph is intentionally split so symbolic execution is the last step in a
branch, not the first monolithic task.

```text
M0  sched_item constructors, item_owner, live-task vocabulary
  -> M1 node_ptr/decode injection; Generic/Event field-address disjointness

V0  fifo_view definition and unique cursor split
  -> V1 insert-end becomes FIFO append
  -> V2 cursor advance becomes FIFO rotation and frames ring
  -> V3 ordered view/stable insertion and due-prefix facts
  -> V4 pointer-xlist relabelling commutes with insert/remove

W0  finite live universe and priority bounds
  -> W1 generic/event role partitions
  -> W2 ready-cache upper bound and nonempty search witness
  -> W3 delayed sortedness, current/overflow key inequalities
  -> W4 core scheduler_wf
  -> W5 dispatch_settled and quiescent-boundary strengthenings

A0  modular addition and wake-role classification
  -> A1 exact should_delay four-branch equations
  -> A2 block_current preserves core WF
  -> A3 delay/delay-until quiescent pure transitions preserve core WF

T0  sorted split into due prefix and future suffix
  -> T1 one wake step preserves item partitions and ready invariants
  -> T2 wake-prefix induction
  -> T3 non-wrap tick preservation
  -> T4 wrap swap, old-current-empty, key-zero wake, epoch increment
  -> T5 suspended tick/missed-counter branch

C0  downward priority search terminates from W2
  -> C1 selected priority is highest nonempty
  -> C2 one cursor step equals FIFO rotation
  -> C3 switch preserves core WF and establishes dispatch_settled
  -> C4 suspended switch sets only missed_yield

U0  one pending-head drain
  -> U1 pending-list induction
  -> U2 one missed-tick replay
  -> U3 missed-tick induction
  -> U4 final-resume return/yield cases and WF preservation
  -> U5 general delay roots by composition

R0  raw TCB/list layout and scheduler globals
  -> R1 one general pointer-based raw_xlist relation per list
  -> R2 relabel and owner-agreement transfer
  -> R3 container/membership closure across both item roles
  -> R4 delayed physical-role permutation
  -> R5 raw_scheduler_rel and concrete preimages

S0  generated xTaskGetTickCount normal form
  -> S1 get-tick simulation
S2  generated vTaskSwitchContext branch normal forms
  -> S3 switch simulation
S4  generated vTaskIncrementTick no-wake/wake/wrap normal forms
  -> S5 tick simulations
S6  generated suspend/resume normal forms
  -> S7 resume simulation
S8  generated vTaskDelay zero/nonzero normal forms
  -> S9 delay simulation
S10 generated vTaskDelayUntil comparison-branch normal forms
  -> S11 delay-until simulation

S1 + S3 + S5 + S7 + S9 + S11
  -> F0 five-root forward simulation for the frozen API alphabet
  -> F1 trace refinement after a separate environment/port theorem
```

The raw list relation and operation simulations at R1 are genuine blockers.
The fixed empty-to-singleton Raw-R5 theorem cannot be substituted for the
general ready/delayed/pending rings needed by scheduler roots.

## 12. Suggested theory and session split

No file below should be created until its immediate predecessor has a small,
checked statement list.  Proposed theory responsibilities are:

| Theory | Contents |
|---|---|
| `Scheduler_Model_Types.thy` | Item roles, state records, live tasks, scalar helpers. |
| `Scheduler_List_Views.thy` | `fifo_view`, cursor rotation, ordered view, relabelling. |
| `Scheduler_Model_WF.thy` | WF-0 through WF-7 and implication lemmas only. |
| `Scheduler_Model_Tick.thy` | Due-prefix, unlocked/suspended tick, wrap. |
| `Scheduler_Model_Switch.thy` | Priority search and FIFO rotation. |
| `Scheduler_Model_Resume.thy` | Pending drain and missed-tick replay. |
| `Scheduler_Model_Delay.thy` | Delay and exact delay-until predicate/composition. |
| `Scheduler_Model_Witnesses.thy` | P0-P11 executable pure witnesses and false-claim counterexamples. |
| `Scheduler_Raw_Layout.thy` | TCB/item field addresses, injections, owner agreement. |
| `Scheduler_Raw_Lists.thy` | General raw-list relations, role homogeneity, relabel transfer. |
| `Scheduler_Raw_State_Rel.thy` | RR-0 through RR-7 and concrete preimages. |
| one `Scheduler_Raw_<Root>.thy` per root | Source normal form and one root simulation. |
| `Scheduler_Refinement.thy` | Thin composition of already checked root theorems. |

Recommended session staircase:

1. a stable HOL parent for Types + List Views + WF;
2. separate small pure child sessions for Tick, Switch, Resume, and Delay;
3. a witness child that imports all green pure transitions;
4. the existing scheduler translation staircase as a stable AutoCorres parent;
5. a raw-layout/raw-list-relation child;
6. one exclusive child session per root, promoting each green root to the next
   parent heap rather than replaying a monolith; and
7. a thin final descendant importing all five simulations.

Each session-owned theory directory must be exclusive to that session; child
theories should use session-qualified imports from promoted parent heaps rather
than pointing two sessions at the same directory.

Pure sessions should retain `quick_and_dirty=false`, `parallel_proofs=0`, and a
short bounded timeout.  Generated-program leaves need their own bounded 300 s
budget.  A slow or red root must be split at its first branch normal form; it
must not trigger a broad proof search over all roots.

## 13. Symbolic-execution and acceptance workflow

For each root, first write an independently defined pure normal form and its
frame.  Symbolically execute the generated source only far enough to show that
normal form.  Recover the public simulation by combining:

```text
source normal form
+ raw list operation simulations
+ raw_scheduler_rel view-transfer lemmas
+ the corresponding pure transition equation.
```

The first implementation order should be:

1. `xTaskGetTickCount`, to validate scalar and proof-port framing;
2. unsuspended and suspended `vTaskSwitchContext`, to validate ready FIFO,
   current, and top-cache modelling;
3. `vTaskIncrementTick` no-wake, singleton-wake, and wrap witnesses before the
   general due-prefix induction;
4. `vTaskDelay 0`, then positive no-wrap and wrap cases;
5. delay-until no-delay, ordinary delay, and both wrap-comparison branches;
6. pending drain and missed-tick replay; and only then
7. the general nested-suspension versions of the delay roots.

Acceptance for a scheduler theorem requires all of the following, none of
which this design document supplies:

- a positive generated source run from a represented concrete preimage;
- a poststate satisfying `raw_scheduler_rel` for the independently defined
  abstract transition;
- explicit preservation of the external frame and proof-port boundary;
- `quick_and_dirty=false`, an exit-zero bounded Isabelle build, and an empty
  forbidden-pattern scan; and
- a statement that distinguishes source-level yield request from eventual
  hardware context switching.

Until those gates are met, this file is an invariant and lemma-graph proposal,
not an additional refinement result.
