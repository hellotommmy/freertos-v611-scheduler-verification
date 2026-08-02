# Delay/Resume Invariant Refinement Audit

## 1. Purpose and claim boundary

This note records the mathematical specification needed to refine the
positive-delay path of `vTaskDelay` through `xTaskResumeAll` and the conditional
outer yield.  It is an audit of theorem shape and invariant strength.  It does
not claim that the generated outer-resume source composition or the final
whole-scheduler theorem has already been discharged.  The abstract general
resume relation itself is checker-green.

The strengthened Event-root, Event-key, due-task phase, and wrap-epoch clauses
introduced below are **invariant design obligations** obtained by manual
source-order analysis.  They are not being reported here as checker-green
lemmas, generated-source refinements, or completed Gate-H results.

Concrete values below are **discovery probes only**.  They expose false
invariants with a small state.  Every acceptance theorem must quantify over an
arbitrary legal state, an arbitrary finite live-task set, every priority
assignment in the frozen source range `0..3`, arbitrary legal list populations
and cursors, arbitrary 32-bit ticks and delays, and every source branch admitted
by its API boundary.  The abstract schema below uses a symbolic positive level
count $L$; instantiating the frozen C build fixes $L=4$.  A theorem for every
compile-time `configMAX_PRIORITIES` would be a separate configuration-family
result.

## 2. State and phase vocabulary

Let a scheduler observation be

\[
  \sigma=(R,D_c,D_o,\mathcal E,q_E,M,C,N,P,K_E,x,\tau,h,s,Q,m,y,Y).
\]

Here $R$ is the family of ready rings; $D_c,D_o$ are the current and
overflow delayed semantic views; $\mathcal E$ is an arbitrary finite family of
protected Event roots and $q_E\in\mathcal E$ is its distinguished
pending-ready root; $M$ and $C$ are root membership and container ownership;
$N,P$ are next and previous links; and $K_E:T\to 32\ \mathsf{word}$ is a
total logical map for Event-item payload keys.  Finally, $x$ is the current
task; $\tau$ is the tick; $h$ is the ready-priority hint; $s$ is the
scheduler-suspension depth; $Q$ is the ring represented at $q_E$; $m$ is the
missed-tick count; $y$ is the missed-yield flag; and $Y$ is an abstract yield
observation count.

There is deliberately no total global Generic-key map.  While a Generic item
is root-owned, its key is derived from that root's represented ring.  When the
source takes the item into transit, the proof captures its concrete key at the
last owning root and carries that phase-local value across the exact frames
until the next source write or insertion.  This covers both the wake-key write
in `vTaskDelay` and the preserved source key used while draining pending work.

For an arbitrary finite live set $T$, arbitrary positive priority-level
count $L$, and priority map

\[
  \pi:T\to\{0,\ldots,L-1\},
\]

the positive-delay transaction uses these cutpoints:

\[
\begin{aligned}
  \mathsf{Ready}
  &\longrightarrow \mathsf{Unlinked}
  \longrightarrow \mathsf{Keyed}
  \longrightarrow \mathsf{Selected}(r)\\
  &\longrightarrow \mathsf{Inserted}
  \longrightarrow \mathsf{Resumed}(b)
  \longrightarrow \mathsf{YieldPending},
\end{aligned}
\]

where $b\in\{\mathsf{InternalYield},\mathsf{OuterYieldRequired}\}$.  These are
logical proof cutpoints, not extra fields asserted to exist in the C runtime.

The phase ledger is:

| Transition | Fields allowed to change | Required stable observations |
|---|---|---|
| `Ready -> Unlinked` | source ready ring and membership; current item's container; predecessor/successor external links | delayed rings, old item key, tick, top hint, current task, suspension depth, pending-ready state, missed state, yield count |
| `Unlinked -> Keyed` | current item's key becomes the captured modular wake | all rings, ownership, links, tick, top hint, current task, suspension depth, pending-ready state, missed state, yield count |
| `Keyed -> Selected(r)` | proof-ghost root selection only | every runtime observation |
| `Selected(r) -> Inserted` | selected delayed ring and membership; current item's container; insertion-slot links | ready rings, key, tick, top hint, current task, suspension depth, pending-ready state, missed state, yield count |
| `Inserted -> Resumed(b)` | effects admitted by the resume relation, including suspension, pending/missed processing, and possibly an internal yield | only what the general resume contract frames |
| `Resumed(b) -> YieldPending` | no outer yield if `InternalYield`; exactly one outer yield if `OuterYieldRequired` | all non-yield observations framed by `YieldAbs` |

The first five phases form the suspended core.  Their tick and suspension depth
are stable.  `Ready` and `Unlinked` impose no value on the old item key: a ready
item may retain an earlier `xItemValue`.  `Keyed` is the first phase requiring

\[
  \mathsf{key}(G_x)=\tau+_{32}d.
\]

## 3. Ownership, top, and slot invariants

At stable endpoints (`Ready`, `Inserted`, and all post-resume endpoints), every
live generic item has exactly one faithful owning root.  During `Unlinked`,
`Keyed`, and `Selected`, only the current generic item may be in transit: its
container is null and it belongs to no root; every other live generic item
still has a unique faithful owner.

At the public running-task entry boundary, ownership must also be compatible
across the two item kinds of the same TCB:

\[
  \mathsf{current}=t\Longrightarrow
  \mathsf{GRole}(t)=\mathsf{Ready}(\pi(t))\land
  \mathsf{ERole}(t)=\mathsf{None}.
\]

The Event item must have a null container and be absent from every protected
Event root.  This is a scheduler API-state invariant.  It does not follow from
the fact that the Generic item is ready, nor from byte disjointness between the
same TCB's Generic and Event subregions.

### 3.1 Event-root family, container fidelity, and Event keys

An opaque per-task Event-container ghost that records only `Null` versus
`NonNull` is sufficient to predict the source test
`event.pvContainer != NULL`.  It is not sufficient for exact all-root source
refinement: in the linked branch it neither identifies the root whose ring,
count, and cursor change nor proves that every other Event root is framed.

The exact representation must instead quantify an arbitrary finite protected
Event-root family $\mathcal E$, with the pending-ready list $q_E$ distinguished
inside it.  For every $e\in\mathcal E$ it represents the physical root, ring,
count, cursor, and member keys.  It also requires:

1. unique Event-item membership across $\mathcal E$;
2. container fidelity: $E_t$ is in root $e$ iff its concrete container is the
   pointer to $e$, and absence from the whole family iff that container is
   null;
3. agreement of the represented ring key for every linked $E_t$ with
   $K_E(t)$; and
4. an exact non-target frame for every root in $\mathcal E$ other than the
   unique source root modified by the branch.

The map $K_E$ is total and independent of Event membership.  An Event item may
be unlinked with an arbitrary retained `xItemValue`, so neither null container
nor absence from $\mathcal E$ determines its key.  Link and unlink operations
must preserve $K_E(t)$ unless the generated source explicitly writes that
payload.  This is different from Generic keys: root-owned Generic keys are
derived from their owning ring, and an in-transit Generic key is captured
locally rather than stored in a global logical map.

The ready top is phase-sensitive.  At `Ready`, exactness may be required:

\[
  h<L,\qquad R_h\ne[],\qquad
  \forall p<L.\ R_p\ne[]\Longrightarrow p\le h.
\]

After removal and before the scheduler repairs the cache, only the upper-bound
form is sound:

\[
  \max(\{0\}\cup\{p<L\mid R_p\ne[]\})\le h<L.
\]

The unlink neighbours are not arbitrary witnesses.  They must be the actual
predecessor and successor in a decomposition

\[
  R_{\pi(t)}=A\mathbin{@}[t]\mathbin{@}B,
\]

with predecessor equal to the last element of $A$, or the sentinel if
$A=[]$, and successor equal to the first element of $B$, or the sentinel if
$B=[]$.  The pre-state links must agree with that slot.  The removed item's
own next and previous fields may remain stale; only the external neighbour
links are rewired.

Likewise, delayed insertion neighbours are fixed by the stable ordered scan.
For wake key $w$, the target ring must split as $A@B$ such that every item
passed by the scan has key at most $w$, while the first item of nonempty $B$
has key strictly greater than $w$.  The new item is inserted between these
two boundaries.  Relating this abstract slot to raw C pointers is a separate
representation bridge and must not be silently assumed by the phase model.

### Gate-H note: root-sentinel endpoint collision and repair

An earlier proof-only phase snapshot represented every list sentinel by the
single value `None`.  A hand trace through removal from one root followed by
insertion into a different empty root refuted that encoding: both endpoints
became `None`, so one global link map conflated two distinct concrete sentinel
cells.  This was a representation bug, not an inconvenient proof case.

The phase model now uses the root-qualified datatype

\[
  \mathsf{Endpoint}=\mathsf{Node}(p)\mid\mathsf{End}(r).
\]

Its representation relation maps `End r` to `raw_end_item r`; distinct
physical roots therefore have distinct abstract endpoints.  Tick wrap changes
the map from semantic roles to physical roots, but never renames the physical
roots or their endpoint tags.  The remaining Gate-H obligation is to connect
this repaired datatype to the raw scheduler-list relations in generated-source
composition.

The role exchange also requires a legal epoch invariant: immediately before a
wrap swaps the semantic roles, the old current delayed root must be empty.
This condition may not be inserted as an unexplained branch premise.  It must
be derived from the reachable scheduler invariant and the fact that all items
due in the ending epoch have already been removed.  The physical roots, their
rings, and `End r` identities remain where they are; only the semantic
current/overflow role map changes.

This is a **Gate-H composition-model gap**, not a failure of the local Gate-L
remove or insertion theorems.  Those raw theorems use `raw_end_item lp`, so the
sentinel identity is already qualified by the concrete list pointer, and their
legal same-ring empty alias remains expressible.  The collision arises only
when the phase model attempts to place several roots in one global link map.

## 4. General resume relation and conditional yield

The theorem architecture after `Inserted` must use two relations rather than
an unconditional outer-yield update.

First, the general relation

\[
  \mathsf{ResumeRel}(\sigma,b,\rho)
\]

describes one source execution of `xTaskResumeAll`.  It may decrement the
suspension depth, drain arbitrary pending-ready work when the depth reaches
zero, replay arbitrary missed ticks, update ready and delayed rings, repair or
raise the top hint, clear or propagate missed state according to the source,
and perform an internal yield.  Its result $b$ records whether that call
already yielded.  No theorem may frame tick, ready rings, delayed rings, top,
or current-task observations across this relation unless its premises exclude
the corresponding interference.

Second,

\[
  \mathsf{YieldAbs}(b,\rho,\omega)
\]

models the source conditional:

\[
\begin{array}{ll}
  b=\mathsf{InternalYield}: & \omega=\rho
    \quad\text{for the outer-yield observation},\\
  b=\mathsf{OuterYieldRequired}: &
    Y(\omega)=Y(\rho)+1,
\end{array}
\]

with the declared non-yield frame in the second branch.  Thus the outer yield
is conditional.  A final "one yield" observation is admissible only after
composing the two branches and showing that the internal branch increments in
`ResumeRel` exactly when the outer branch is skipped.

The sequential boundary

\[
  \mathcal Q(\sigma)\equiv
  s=1\ \land\ Q=[]\ \land\ m=0

\]

is an explicit API premise.  It is not inferred from a small witness.  Under
this boundary, resume has no pending-ready or missed-tick work, so a corollary
may frame the core rings and tick across resume.  The flag $y$ remains
symbolic:

\[
  y\Longrightarrow b=\mathsf{InternalYield},\qquad
  \neg y\Longrightarrow b=\mathsf{OuterYieldRequired}.
\]

The stronger quiescent boundary

\[
  \mathcal Q_0(\sigma)\equiv\mathcal Q(\sigma)\land\neg y
\]

therefore selects the outer-yield branch.  This is a corollary of a general
resume contract, not a replacement for it.  If the accepted whole-operation
theorem assumes \(\mathcal Q\) or \(\mathcal Q_0\), that restriction must appear
in its statement and acceptance label.

## 5. Counterexample-driven invariant refinement

### 5.1 Modular wrap and stale top

A discovery trace with tick `0xfffffffe` and delay `3` produces modular wake
`1`.  The comparison `wake < tick` is true, so insertion belongs to the
overflow delayed root.  Replacing word addition by natural addition, or
selecting the current delayed root merely because the delay is positive,
misclassifies this trace.

The accepted branch theorem is value-independent:

\[
  (\tau+_{32}d<\tau)\Longleftrightarrow
  r=\mathsf{OverflowRoot},
\]

with the complementary branch selecting the current delayed root.  The probe
does not appear as a theorem premise.

A second discovery shape has a singleton at the unique highest nonempty ready
priority.  Removing that task empties the ring while the cached hint is not
immediately repaired.  Therefore exact top is false at `Unlinked`, even though
the old hint remains a valid upper bound.  This forces the phase refinement

\[
  \mathsf{ExactTop}(\mathsf{Ready})
  \quad\leadsto\quad
  \mathsf{UpperBoundTop}(\mathsf{Unlinked}\ldots\mathsf{YieldPending}).
\]

The acceptance lemma quantifies over every level count $L>0$, every
$h<L$, every ready-ring family, and every singleton task satisfying the
premise.

### 5.2 Equal-key ordered insertion

Consider distinct old and new nodes with the same wake key $k$.  The source
scan advances while the new key is not strictly less than the current key.
Consequently the stable result is

\[
  [\mathit{old}]\longmapsto[\mathit{old},\mathit{new}],
\]

not `[new, old]`.  A before-equals invariant is therefore false.  This
counterexample forces the ordered-slot premise to use

\[
  \text{passed keys}\le k,
  \qquad
  \text{first unpassed key}>k.
\]

The accepted theorem ranges over arbitrary distinct nodes, arbitrary legal
ordered rings, and arbitrary 32-bit key $k$.  The two-node shape is only the
smallest refutation of the wrong strictness.

### 5.3 Resume interference

Suppose `Inserted` is followed by resume with a nonempty pending-ready ring, a
positive missed-tick count, or both.  A pending task may move into a ready ring
and raise the top hint.  Replayed ticks may move delayed tasks to ready rings,
change the tick, and create further scheduling work.  The resume call may then
yield internally.  Hence the following proposed frame is false in the general
case:

\[
  R'=R\land D_c'=D_c\land D_o'=D_o\land
  \tau'=\tau\land h'=h.
\]

A small probe with one higher-priority pending task or one missed tick is
sufficient to expose the failure, but the refinement it forces is general:

1. `ResumeRel` must admit every legal pending-ready population and missed-tick
   count allowed by the source invariant.
2. Any frame for ready/delayed rings, tick, or top must be derived from an
   explicit no-interference boundary such as \(Q=[]\land m=0\).
3. Internal and outer yield must remain separate until their control-flow
   results are composed.
4. A theorem proved only under \(\mathcal Q\) must be labelled as a
   sequential/quiescent corollary, not as unrestricted scheduler correctness.

There are two distinct semantic layers.  The generated AutoCorres theorem for
one sequential call of `vTaskDelay'` contains no implicit ISR environment step
between suspension and resume; pending/missed observations evolve only through
the translated program.  A theorem admitting ISR-produced work during that
interval requires a separate rely/guarantee or explicit
`SuspendedInterference` relation.  The former must not be described as
concurrent correctness, and the latter must not be smuggled into the generated
sequential execution.

### 5.4 Pending drain: owner, priority, and body-local phases

A source-order trace with pending owner order

\[
  Q=[u,v],\qquad \pi(u)<\pi(c)\leq\pi(v),
\]

exposes two observations absent from a topology-only list relation.  Reading
the pending head obtains the task through the Event item's `pvOwner`, and the
ready destination and yield comparison are selected by the owning TCB's
`uxPriority`.  The universal representation must therefore include, for every
live task $t$,

\[
\begin{aligned}
  \mathsf{owner}(G_t)&=\mathsf{owner}(E_t)=\mathsf{tcb}(t),\\
  \mathsf{uxPriority}(\mathsf{tcb}(t))&=\pi(t),
\end{aligned}
\]

with injective TCB decoding and explicit byte separation between $G_t$, $E_t$,
the priority field, every other live TCB, and every scheduler list root.
Generic and Event ownership are independent: $E_t$ may be pending while $G_t$
is delayed or suspended.  The false invariant "a TCB occurs in at most one
root" is replaced by item-kind-aware ownership.

The Generic item's payload key is also independent of the semantic wake
option.  A suspended task may legally retain a nonzero `xItemValue` from an
earlier delay.  For every pending task, let $k_t$ be the key read from the
unique physical Generic source root (delayed A, delayed B, or suspended) before
either removal.  Event removal and Generic removal must frame $k_t$, and the
ready `vListInsertEnd` must insert with exactly $k_t$.  The implication
`wake=None -> key=0` is false and must not appear as an invariant or premise.

The Event item's payload is governed separately by the total map $K_E$.
Removing $E_t$ from the distinguished pending root must preserve $K_E(t)$,
and a null Event container elsewhere still permits any value of $K_E(t)$.
Neither the captured Generic key $k_t$ nor the semantic wake option may be
used to reconstruct the Event key.

For an arbitrary initial pending order $Q_0$, the loop-head invariant freezes
the initial current task $c_0$ and quantifies a processed prefix and remaining
suffix:

\[
  Q_0=\mathit{done}@\mathit{todo},\qquad
  \sigma=\mathsf{foldl}(\mathsf{PendingStep},\sigma_0,\mathit{done}).
\]

Every task in `todo` still has its Event item in the pending root and its
Generic item in one legal blocked root.  Every task in `done` has an unlinked
Event item and a Generic item in ready root $R_{\pi(t)}$.  The exact local
yield accumulator is

\[
  Y_P\Longleftrightarrow
  \exists t\in\mathit{set}(\mathit{done}).\ \pi(t)\geq\pi(c_0).
\]

This comparison against the base current task is correct: `pxCurrentTCB` and
its priority do not change before the final yield boundary.  A separate fold
tracks the top hint.  Because the source raises the hint before calling
`vListInsertEnd`, an internal cutpoint may temporarily have a raised hint whose
new ready item has not yet been linked; exact top/list agreement is therefore
required only at the completed body boundary.

The body-local ownership phases for the current pending task are

\[
  \mathsf{BothOwned}\to\mathsf{EventUnlinked}
  \to\mathsf{BothUnlinked}\to\mathsf{TopRaised}
  \to\mathsf{GenericReady}.
\]

At each arrow the exact write footprint must preserve both owner fields, the
priority field, the captured Generic key $k_t$, the sibling list item, all
non-target roots, and all other tasks.  `TopRaised` is explicit because the
ready-queue macro raises the hint before the item is linked; a ready-ring
witness is required only at `GenericReady`.

### 5.5 Missed ticks: physical roles and an arbitrary due prefix

Let $A$ and $B$ be distinct physical delayed roots.  If the entry tick is
`MAX_WORD` and a replayed tick advances it to zero, the source swaps only the
two delayed-role pointers and increments the overflow counter:

\[
  \mathsf{role}'(\mathsf{current})=B,\qquad
  \mathsf{role}'(\mathsf{overflow})=A.
\]

The physical rings and `End A`/`End B` identities do not move.  Consequently a
task just inserted into physical root $B$ with wake key zero may immediately
become due and move to its ready root before the surrounding `vTaskDelay`
returns.  No final relation may preserve that task's delayed membership.

At the wrap boundary the old semantic-current physical root must be empty
before the role pointers exchange.  This is a required legal-epoch invariant,
not a free source precondition: the Gate-H reachability/invariant proof must
derive it.  After the exchange the same physical root and endpoint objects
remain in memory, with only their semantic roles changed.

For a non-wrap or post-wrap current delayed ring, write

\[
  D=\mathsf{takeWhile}(\lambda t.\ \mathsf{key}(G_t)\leq\tau,\mathit{ring}),
  \qquad
  F=\mathsf{dropWhile}(\lambda t.\ \mathsf{key}(G_t)\leq\tau,\mathit{ring}).
\]

Thus $\mathit{ring}=D@F$, every node in the arbitrary finite prefix $D$ has key
at most the current tick, and $F$ is empty or its first key is strictly greater
than the tick.  This is a complete `takeWhile key <= tick` characterization:
the generated delayed loop processes exactly $D$, including $|D|=0$,
$|D|=1$, and every finite $|D|=N$; an entire run of keys equal to the tick is
processed, and execution stops at exactly the first not-due item.  At a loop
head,

\[
  D=\mathit{done}@\mathit{todo},\qquad
  \sigma=\mathsf{foldl}(\mathsf{WakeStep},\sigma_e,\mathit{done}),
\]

and the current physical delayed ring is `todo @ F`.  One due task is refined
through the source-order phases

\[
  \mathsf{DueOwned}
  \to\mathsf{GenericUnlinked}
  \to\mathsf{EventChecked}
  \to\mathsf{EventUnlinked}
  \to\mathsf{TopRaised}
  \to\mathsf{GenericReady}.
\]

`EventChecked` records the concrete null/non-null branch without changing the
heap.  In the null branch, `EventUnlinked` is a no-op and $E_t$ remains absent
from all protected Event roots.  In the linked branch, container fidelity
identifies the unique $e\in\mathcal E$ that owns $E_t$; the step removes it
from exactly that root and frames every other Event root.  Both branches
preserve the independently modelled Event key $K_E(t)$.  The later phases
raise the top hint and insert $G_t$ into ready root $R_{\pi(t)}$.

Consequently a tick may modify several ready roots and several Event roots.
The loop invariant must carry a cursor fold, not a cursor frame: after
processing `done`, every affected delayed, Event, and ready root cursor is the
result of folding the exact source removal or insert-end cursor rule over the
operations on that root.  This fold, together with the exact `takeWhile`
decomposition, proves both complete processing of the due prefix and stopping
before the first future item.

For an arbitrary initial missed count $M$, replay then uses

\[
  0\leq i\leq M,\qquad
  \sigma_i=\mathsf{iterate}(\mathsf{UnlockedTick},i,\sigma_P),\qquad
  m_i=M-i.
\]

There is a necessary body cutpoint after `UnlockedTick` but before the source
decrements the missed counter.  Once the loop finishes, the preemptive frozen
configuration forces the resume yield requirement whenever $M>0$, regardless
of the priorities of the woken tasks.

## 6. Acceptance obligations

The delay/resume component is ready for whole-operation use only when the
following quantified obligations are available:

1. **Core phase preservation.**  For arbitrary legal inputs, each core
   transition establishes its phase ownership, key, top, tick, suspension,
   slot, and exact frame obligations.
2. **Raw slot refinement.**  Generated predecessor/successor pointers and the
   ordered-loop exit refine the abstract remove and insertion slots for every
   legal alias class, including the empty-ring sentinel alias.
3. **General resume refinement.**  Generated `xTaskResumeAll` refines
   `ResumeRel` for arbitrary pending-ready and missed-tick states admitted by
   the scheduler invariant.
4. **Conditional-yield refinement.**  The returned resume result selects the
   correct `YieldAbs` branch; the outer yield is never assumed unconditionally.
5. **Quiescent corollary.**  Under the explicitly stated boundary, the general
   relation simplifies to the framed sequential result, and the two yield
   branches converge to the declared single abstract yield observation.
6. **No witness leakage.**  Concrete task counts, priorities, ticks, delays,
   addresses, ring lengths, or branch choices occur only in named discovery
   probes or counterexamples, never as hidden restrictions on positive
   acceptance theorems.
7. **Protected Event-root family.**  The representation quantifies every
   finite protected Event-root family, distinguishes the pending root, proves
   count/ring/cursor/key and container fidelity, and frames all non-target
   Event roots in both linked and null branches.  A Boolean or opaque
   container ghost is not counted as this result.
8. **Total Event-key fidelity.**  One total $K_E$ represents arbitrary retained
   Event payloads even while unlinked; Generic keys remain root-derived or
   phase-locally captured rather than being conflated with $K_E$.
9. **Complete due-prefix refinement.**  The generated loop implements the
   exact finite `takeWhile key <= tick` prefix for zero, one, and arbitrary
   $N$ tasks, consumes all equal-tick items, stops at the first future item,
   and refines the six due-task phases and per-root cursor fold.
10. **Wrap-epoch reachability.**  A proved invariant establishes that the old
    current delayed root is empty at wrap; the role exchange preserves the
    physical roots and root-qualified endpoints.

Until the general resume and raw slot bridges are connected to generated
source execution, the phase model is an invariant specification and proof
decomposition, not a completed universal `vTaskDelay` correctness theorem.
