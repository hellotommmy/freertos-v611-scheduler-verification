# Universal-Input Proof Progress for the FreeRTOS V6.1.1 Scheduler

**Mathematical progress report - blind Isabelle/HOL reconstruction**

**Status date: 2 August 2026 | Result: reusable universal-input bricks checked; universal functional correctness remains open**

> **Scope warning.** This manuscript does **not** claim universal correctness of `vTaskDelay`, the five scheduler roots, or the FreeRTOS scheduler. The earlier P2 result is one fixed, non-vacuous generated-source witness. It remains useful as a regression witness, but it is not evidence for arbitrary task sets, priority assignments, ticks, delays, list populations, addresses, or source branches. The results counted here as universal have quantified statements that do not select that witness.

> **Status discipline.** The O4 transformer/frame theory, the generated
> all-key `vListInsert'` loop theorem, the generated arbitrary-member
> `vListRemove'` theorem, the finite-root removal/ownership theorem, and the
> proof-only delay phase theory are checker-green with
> `quick_and_dirty = false`.  The phase theory is a mathematical invariant
> specification; it is not a generated `xTaskResumeAll` refinement.  Universal
> `vTaskDelay` and whole-scheduler correctness remain open.

## Abstract

The proof development has moved beyond a single fixed P2 execution in several mathematically reusable directions. Isabelle now checks pure abstract delay semantics for arbitrary inputs, including modular 32-bit wake arithmetic, ready-list removal, delayed-list selection, frame facts, and a modular observation relation for the proof-port yield counter. Separate theorems show that delaying one task preserves every different ready task already present and identify the additional premise needed to conclude that some ready task remains.

At the representation layer, checker-green bridges connect generated scheduler list reads to the arbitrary-ring raw list model. A finite-task geometry theory treats an arbitrary finite live set, an injective guarded TCB map, pairwise-disjoint TCB regions, and explicit decoder laws; it derives separation and decoder round trips for whole TCBs and their embedded generic and event items. A separate finite-cardinality proof derives the formerly free `raw_count_can_increment` condition from `raw_xlist_rel` and insertion freshness, using the actual cardinality of the 32-bit pointer type.

Trace-led analysis identified the generated-loop split invariant, maximum-key
bypass, equal-key policy, six-write alias classes, stale post-removal links,
and the failure of target-local freshness to establish a global scheduler
frame.  Isabelle now checks the actual generated `vListInsert'` body for every
32-bit key and arbitrary legal ordered ring, including the empty-ring alias,
and the actual generated `vListRemove'` body for an arbitrary legal member
position and cursor.  A finite-root theorem derives global unlinkedness after
removal from unique entry ownership and other-root frames.  The next hard path
is the generated positive-delay composition and the general resume relation:
pending-ready processing and missed-tick replay may change ready/delayed roots,
tick, top hint, current task, and the yield route after the item was inserted.
Consequently Gate H and Gate D remain open, and no whole-operation universal
scheduler theorem is claimed.

## 1. Quantified acceptance boundary

The frozen build has `configMAX_PRIORITIES = 4`. Universality for this build means quantification over an arbitrary finite live-task set and an arbitrary priority function satisfying

$$
\forall t\in\mathit{live}.\;\mathit{priority}(t)<4.
$$

It does not mean checking a finite table of examples. A qualifying Level-A `vTaskDelay` theorem must range over:

- every finite live-task set;
- every valid priority assignment into the four configured priorities;
- every well-formed population, order, and cursor of all ready rings;
- both physical delayed-list role assignments and arbitrary valid delayed rings;
- every admitted current task, 32-bit tick, and 32-bit delay argument;
- every generic decoder and heap layout satisfying the stated guard, injectivity, separation, and round-trip laws;
- every source scalar and proof-port observation admitted by the declared sequential API boundary;
- every source branch reachable from that boundary, including modular wrap and non-wrap cases.

The desired theorem must establish a non-vacuous generated-source execution, the complete concrete-to-abstract post-relation, invariant preservation at the declared phase, and a complete frame. Pure abstract equations, symbolic traces, isolated list transformers, or fixed witnesses are necessary components but are not substitutes for that theorem.

This acceptance boundary is configuration-specific. It does not quantify over arbitrary values of `configMAX_PRIORITIES`, and it does not include interrupt interference unless an explicit concurrency model is added.

## 2. Fixed P2 witness versus all-input results

The earlier P2 seal and the new results have different logical forms.

| Evidence class | Quantification | What it establishes | What it does not establish |
|---|---|---|---|
| Fixed P2 witness | One artifact-specialised prestate and one selected generated-source path | Non-vacuity and correctness of that concrete path under the frozen translation and relation | Other task populations, priorities, delays, branches, heaps, or call sequences |
| Universal pure delay bricks | Arbitrary abstract state, tick/delay word, current-task option, task identity, and relevant rings | Exact abstract transition equations and preservation facts | Execution of generated C source or existence of a concrete preimage |
| Universal ABI/ring bridges | Arbitrary raw-list relation, cycle node, heap, and list pointer satisfying the bridge premises | Agreement of generated reads, raw reads, guards, keys, and successors | The generated loop's termination and poststate |
| Universal generated ordered insert | Arbitrary scheduler heap/list/item satisfying ordered relation and freshness; arbitrary ring, scan position, duplicate keys, and 32-bit item key | Actual generated `vListInsert'` returns the exact six-write transformer state | Scheduler-family ownership and complete `vTaskDelay'` composition |
| Universal generated removal | Arbitrary scheduler heap/list/member satisfying the raw relation; arbitrary member position, cursor, and legal aliases | Actual generated `vListRemove'` returns the exact removal state and frames non-heap globals | Choice of the owning root and surrounding delay call |
| Universal finite-task geometry | Arbitrary finite live set and decoder satisfying explicit storage and decoder laws | Cross-task separation, pointer inequality, and decoder round trips | Construction of such a decoder/heap for every reachable scheduler state |
| Derived count capacity | Arbitrary raw list and fresh item satisfying the legal input relations | The list count can increment without wrap | General ordered insertion or scheduler-wide ownership freshness |

The fixed witness remains a regression test. It is deliberately excluded from the evidence used to justify the universal rows.

## 3. Checker-green universal abstract delay semantics

Let $s$ be an arbitrary abstract scheduler state, $d$ an arbitrary 32-bit delay word, and $t$ the current task when one exists. For a positive delay the definition

$$
\operatorname{positive\_delay\_state}(d,t,s)
=
\operatorname{request\_yield}
  (\operatorname{block\_task\_at}(\operatorname{tick}(s)+_{32}d,t,s))
$$

uses word addition, not natural-number addition. The delayed destination is selected by the source-shaped unsigned comparison

$$
\operatorname{tick}(s)+_{32}d < \operatorname{tick}(s).
$$

The checker-green theorem `task_delay_abs_positive_universal_effects` proves, without fixing an input state:

- the current task's wake field becomes the modular sum;
- every other task's wake field is unchanged;
- the current generic item is removed from its priority's ready ring;
- every other priority's ready ring is unchanged;
- the current or overflow delayed ring receives an ordered insertion according to the modular comparison;
- the delayed ring not selected by the comparison is unchanged;
- the abstract current task and tick are unchanged at this phase;
- the abstract yield count is incremented once.

The theorem `task_delay_abs_all_inputs_capstone` covers all abstract delay inputs by splitting only on `ticks = 0` and the current-task option. It is a complete characterization of the current **pure abstract function**. It is not a generated-source refinement theorem.

The generated proof-port operation has a separate modular observation theorem. The relation

$$
\operatorname{yield\_count\_mod\_rel}(w,n)
\Longleftrightarrow
w=\operatorname{of\_nat}(n)
$$

relates the 32-bit concrete counter to the low 32 bits of the unbounded abstract event count. `eal6_port_yield_mod_refines_request_yield` checks the generated yield operation against `request_yield` without a no-wrap assumption. This closes the modular yield observation itself, not the positive-delay source path around it.

## 4. Ready-task preservation and the necessary premise

The statement that delaying the current task preserves every ready member is false: if it is the only member of its ready ring, removal empties that ring. The checker-green lemma `remove_only_ready_member_counterexample` records this failure at the abstract list level.

The correct universal statement is `task_delay_abs_preserves_other_ready_member`:

$$
\begin{aligned}
&\operatorname{current}(s)=\operatorname{Some}(c),\\
&G(u)\in\operatorname{ready}(s,p),\\
&u\ne c
\end{aligned}
\Longrightarrow
G(u)\in\operatorname{ready}(\operatorname{task\_delay\_abs}(d,s),p).
$$

Thus some ready task remains only when a different ready task is supplied. `task_delay_abs_some_ready_task_remains` makes that premise explicit and retains the configured priority bound. The idle-task corollaries are instances of the general theorem, not evidence based on one fixed scheduler state.

## 5. Generic generated/raw ABI and ring bridges

The generated scheduler and the raw list development use different record universes. `scheduler_item_of_raw` is an address-preserving coercion between their item-pointer types. The checker-green bridge layer proves, for an arbitrary raw list relation and arbitrary node in its cycle:

- the generated pointer and its raw coercion have the same machine address;
- the cycle node and its raw successor satisfy the generated `c_guard` obligations;
- the generated `pxNext` read equals the raw successor;
- the generated item-key read equals `raw_key_at`;
- for live ring nodes, that raw key equals the abstract `item_key`;
- the generated while guard is equivalent to the corresponding comparison of raw keys.

The packaged theorem is `scheduler_ordered_loop_read_bridge`. Its statement is generic in the heap, list, ring, and cycle node. The theory imports artifact-generated ABI definitions through P2-named sessions, but its theorem does not fix a P2 task, address, ring length, key, or branch.

These read bridges remove a representation mismatch. They do not by themselves prove that the generated loop maintains an invariant or reaches the correct exit.

## 6. Universal finite-task geometry and decoder laws

For a live set $L$ and decoder $D$, `universal_tcb_geometry L D` requires:

$$
\begin{aligned}
&\operatorname{finite}(L),\\
&\operatorname{inj\_on}(D.\operatorname{tcb\_ptr},L),\\
&\forall t\in L.\;\operatorname{guard}(D.\operatorname{tcb\_ptr}(t)),\\
&\forall t,u\in L.\;t\ne u\Longrightarrow
  \operatorname{Reg}_{TCB}(t)\cap\operatorname{Reg}_{TCB}(u)=\varnothing.
\end{aligned}
$$

The component type ranges over the whole TCB, the embedded generic item, and the embedded event item. `universal_different_live_component_regions_disjoint` proves that every component of one live task is disjoint from every component of a different live task. `universal_different_live_component_bases_neq` derives the corresponding base-pointer inequality. No task count, task identity, or concrete address is fixed.

Storage geometry alone is not enough to justify decoding. `universal_decoder_laws` separately states forward and inverse laws for TCB, generic-item, and event-item decoding, and requires every successfully decoded node owner to be live. The theorem `pointer_injectivity_does_not_force_decoder_roundtrip` supplies a counterexample to the tempting inference from pointer injectivity alone. The three decoder `iff` lemmas and `universal_geometry_scheduler_decode_rel` transfer the explicit laws into the existing scheduler decoder relation.

This is a conditional generic geometry theorem: later work must still derive its premises from a complete generic scheduler representation and show that the representation is inhabited where claimed.

## 7. Checker-green derivation of list-count capacity

The raw ordered-insert development previously carried

```isabelle
raw_count_can_increment xs
```

as a free premise. Gate-L capacity work now derives it from the legal list input.

From `raw_xlist_rel h lp xs`, Isabelle obtains

$$
\operatorname{distinct}(E\mathbin{\#}\operatorname{ring}(xs)),
$$

where $E$ is the list sentinel. From `raw_fresh_for_insert lp (ring xs) p`, it obtains $p\ne E$ and $p\notin\operatorname{set}(\operatorname{ring}(xs))$. Hence

$$
\operatorname{distinct}(p\mathbin{\#}E\mathbin{\#}\operatorname{ring}(xs)).
$$

The proof does not assume an address bound. It proves the pointer-cardinality bridge

$$
\operatorname{CARD}(\operatorname{raw\_node\_id})=2^{32}
$$

from the `Ptr` constructor, the 32-bit address type, `card_image`, and `card_word`. Finite-set cardinality then gives

$$
|\operatorname{ring}(xs)|+2\le 2^{32},
$$

and therefore

$$
|\operatorname{ring}(xs)|<2^{32}-1
=\operatorname{unat}(\operatorname{max\_word}:32\ \operatorname{word}).
$$

The checker-green theorem is:

```isabelle
theorem raw_xlist_rel_fresh_count_can_increment:
  assumes "raw_xlist_rel h lp xs"
      and "raw_fresh_for_insert lp (ring xs) p"
  shows "raw_count_can_increment xs"
```

There is no hidden length constant, fixed address, or retained capacity premise.

## 8. Trace-led generated-loop invariant and checked source theorem

The trace audit was invariant-design evidence, not proof evidence.  The
surviving invariant has now been checked against the actual generated source.
Let:

- $E$ be the sentinel;
- $N$ be the fresh item;
- $k$ be the key read from $N$;
- $xs=P@S$ be a ghost split of the old ring;
- $c=\operatorname{last}(E\mathbin{\#}P)$ be the generated iterator's predecessor;
- $q=\operatorname{hd}(S@[E])$ be the raw successor.

For the ordinary branch $k\ne\operatorname{MAX}$, the proposed mutable invariant carries:

```text
generated state and heap = entry state and heap
xs = P @ S
every key in P is <= k
iterator address = last (E # P)
```

The derived view gives $q=\operatorname{hd}(S@[E])$. At a continuing head $S=y\mathbin{\#}ys$, the ghost transition is

$$
(P,y\mathbin{\#}ys,c)
\longmapsto
(P@[y],ys,y),
$$

with strict variant decrease

$$
|ys|<|y\mathbin{\#}ys|.
$$

The empty suffix exposes why the sentinel key is essential. Without the checked fact that the sentinel key is `MAX`, a weak invariant could permit a true guard while $S=[]$, leaving both iterator and $|S|$ unchanged. The invariant must derive the sentinel fact from the entry relation; it may not assume the desired exit.

The maximum-key source branch bypasses the loop. Since every 32-bit key is at most `MAX`, it must join the ordinary exit description with the complete prefix and empty suffix:

$$
P=xs,\qquad S=[],\qquad
c=\operatorname{last}(E\mathbin{\#}xs),\qquad q=E.
$$

`Scheduler_Ordered_Insert_General_Loop` now checks the well-founded generated
loop, the non-maximum source path, the maximum-key bypass, and their common
six-write suffix.  Its exported theorem
`scheduler_vListInsert_ordered_general_exact_state` has only two semantic
premises: the arbitrary ordered raw-list relation and insertion freshness.  It
quantifies the scheduler globals, list pointer, item pointer, heap, ring,
length, duplicate-key population, scan position, and item key; the split on
maximum versus non-maximum key occurs only inside the proof.  The conclusion
states that the actual generated scheduler `vListInsert'` returns successfully
and that the complete post-globals equal the general raw heap transformer.
No successful execution, selected scan position, or desired post-relation is
assumed.

## 9. Six writes and legal alias classes

After scan exit the source performs exactly these writes in this order:

| Step | Target | Required value |
|---:|---|---|
| 1 | `N.next` | $q$ |
| 2 | `q.previous` | $N$ |
| 3 | `N.previous` | $c$ |
| 4 | `c.next` | $N$ |
| 5 | `N.container` | target list $L$ |
| 6 | `L.count` | old count plus one |

A correct proof must preserve the following legal alias classes rather than ruling them out globally:

- empty ring: $c=q=E$;
- insertion before the first old item: $c=E$;
- insertion after the last old item: $q=E$;
- strict middle insertion: $c$ and $q$ are ordinary adjacent nodes;
- sentinel link fields and `L.count` inhabit the same packed list object;
- the three writes to fields of $N$ inhabit the same item object.

Freshness must still prove $N\ne c$, $N\ne q$, and separation of the entire writable region of $N$ from the target root and every old target-list item. The exact byte frame is outside the union

```text
N.next, q.previous, N.previous, c.next, N.container, L.count.
```

The checker-green O4 refinement connects these field-level facts to the arbitrary raw ordered-list relation. `raw_ordered_insert_general_transformer_refines` establishes the local ordered-list transformer under its explicit legal-input premises. `raw_ordered_insert_general_heap_exact_external_frame` proves equality with the entry heap at every byte address outside the exact six-field footprint above. The frame theorem has no premise $c\ne q$; it therefore retains the legal empty-ring case $c=q=E$ instead of proving it away. These are local list results and do not establish scheduler-wide ownership freshness.

The generated-source theorem of Section 8 reaches exactly this transformer for
the scheduler translation unit.  Thus symbolic execution of the loop and the
semantic ordered-list/frame theorem are both checked; scheduler-global
ownership still comes from the separate remove-to-insert argument below.

## 10. Gate-H source order, proof-only phases, and ownership

The universal heap relation must follow the actual positive-delay source order. The source computes the modular wake value **before** it calls `vListRemove`. Removal then precedes the write of that wake value into the generic item and the ordered insertion into a delayed list. A proof may retain the already-computed wake value as a ghost observation across these cutpoints, but it must not reorder the concrete operations merely to simplify the relation.

The relevant `vListRemove` poststate is subtler than a fully cleared item:

- it rewires the predecessor and successor around the removed item;
- if the list cursor `pxIndex` points at the removed item, it moves the cursor to the removed item's predecessor; otherwise it preserves the cursor;
- it sets the removed item's `pvContainer` field to `NULL`;
- it decrements the source list count;
- it leaves the removed item's own `pxNext` and `pxPrevious` fields stale.

Therefore a sound intermediate relation must permit those stale item links. Requiring the removed item's next and previous pointers to be null, self-linked, or already shaped for the destination list would be a false strengthening.

The checker-green `Scheduler_Universal_Delay_Phases` theory uses proof-only
phase tags

```text
Ready -> Unlinked -> Keyed -> Selected(r) -> Inserted
      -> Resumed(b) -> YieldPending
```

These are logical relations at source cutpoints, not a runtime FreeRTOS
enumeration.  The abstract phase predicates, exact deltas, destructors,
counterexamples, and quiescent yield join are checked.  Refinement of the
complete generated `vTaskDelay'` and `xTaskResumeAll'` bodies to those relations
remains an open Gate-H obligation.  Their roles are:

The link domain is root-aware: ordinary items are `DelayNode n`, while each
root has its own `DelayEnd r`.  A checked parametric theorem shows that distinct
root ends can simultaneously carry independent successor values.  This avoids
the false abstraction in which every sentinel was collapsed to one `None` and
made first-node removal from one root incompatible with insertion into an
empty second root.  The concrete `raw_end_item` bridge is still to be checked.

| Proof phase | Required semantic view |
|---|---|
| `Ready` | The current generic item is uniquely owned by its source ready root and the settled entry relation holds. |
| `Unlinked` | Source neighbors, conditional cursor, and count reflect removal; `pvContainer = NULL`; the removed item's own next/previous fields may remain stale. |
| `Keyed` | The item remains globally unlinked and its key equals the modular wake value computed before removal. |
| `Selected(r)` | Root selection is a proof observation determined by modular wrap; no runtime field changes. |
| `Inserted` | The item is uniquely owned by the selected delayed root, the ordered-ring relation holds, and the other roots are framed. |
| `Resumed(b)` | A general resume relation may drain pending-ready work, replay missed ticks, and choose an internal or outer-yield route. |
| `YieldPending` | The selected conditional-yield route has been observed, but context-switch settlement has not yet been required. |

At `YieldPending`, the concrete top-ready field may still be a stale upper-bound
hint. If delaying the current task empties the highest ready ring, `vTaskDelay`
does not necessarily recompute that field; settlement is deferred until
`vTaskSwitchContext`. The checked phase model therefore distinguishes this
permitted stale upper bound from the exact highest nonempty priority required
by a settled scheduler relation.  The corresponding generated-source bridge is
still open.

### General resume relation versus the quiescent corollary

`Inserted` is the last phase whose exact source state is determined by the
delay transaction alone.  On an outermost `xTaskResumeAll` call, the source
first decrements the suspension depth, drains the pending-ready list in list
order, and only then replays every missed tick.  Pending tasks may be removed
from their former generic owners and inserted into ready rings.  Each replayed
tick may increment the tick, swap the current/overflow delayed-root roles on
wrap, wake additional delayed tasks, update the top hint, and create a
preemptive yield request.  The final internal yield is taken when that request
or the missed-yield flag is set; otherwise the caller takes its conditional
outer yield.

A discovery trace with one pending task and one missed tick is enough to kill
the tempting frame

$$
R'=R\land D_c'=D_c\land D_o'=D_o\land \tau'=\tau\land h'=h.
$$

The pending task first moves to its ready ring and may raise $h$.  Replaying
the tick then changes $\tau$ and may wake a different delayed task into another
ready ring, changing a delayed root and $h$ again; a wrap also swaps the two
delayed-role pointers.  These concrete values are a falsification probe, not a
theorem restriction.  The general postcondition must therefore have the form

$$
\operatorname{YieldAbs}
  (\operatorname{ResumeRel}(\operatorname{InsertedState})),
$$

where `ResumeRel` admits every legal pending population and missed-tick count
and preserves their source order.  Only the explicitly named boundary

```text
suspension depth = 1, pendingReady = [], missedTicks = 0
```

reduces this relation to a framed sequential corollary.  If `missedYield` is
also false, that corollary selects the outer-yield branch; otherwise the resume
helper may yield internally.  “Exactly one yield route” does not imply a frame
on roots, tick, or top in the unrestricted relation.  The detailed invariant
audit is recorded in `DELAY_RESUME_INVARIANT_REFINEMENT.md`.

`Scheduler_Resume_General_Relation` now checks this abstract architecture.  It
defines one pending-task transfer, source-order pending drain, missed-tick
replay, the conditional `YieldAbs`, and a general `ResumeRel`, all over
arbitrary populations and missed counts.  A named discovery lemma proves that
pending drain and tick replay do not commute.  The actual generated
`eal6_port_yield'` leaf is connected to the yielding branch and to the modular
abstract yield observation.  This does **not** yet refine the whole generated
`xTaskResumeAll'` body.

### Local spatial freshness is not global ownership freshness

`raw_fresh_for_insert L xs N` is a local target-list predicate. It says that $N$ is distinct from the sentinel and old ring of $L$ and spatially separated from their relevant regions. This is enough for a local target-list transformer.

It is not enough for a scheduler-wide frame. Consider two valid roots $L$ and $M$. Let $L$ be empty and let $N$ be the sole member of $M$. Then $N$ can satisfy spatial freshness relative to $L$, yet inserting it into $L$ overwrites the links and container by which $M$ represents $N$. The local postcondition may hold while the global scheduler representation is destroyed.

Therefore Gate H needs a separate remove-to-insert intermediate invariant, including the concrete observation

$$
N.\operatorname{container}=\operatorname{NULL}
$$

However, `N.container = NULL` alone does not prove global unlinkedness. The
derivation also needs an entry invariant giving $N$ unique ownership by the
source ready root, correctness of removal for that root, and frame theorems
showing that every other scheduler-owned root is unchanged.  The checker-green
theorem `raw_family_remove_owner_globally_unlinked` performs this derivation for
an arbitrary finite root family.  A separate faithful-container theorem states
the managed-universe membership/container frames needed to preserve the
correspondence.

This ownership fact must be **derived from the preceding removal**. It must not be added as a postcondition-shaped premise to the local ordered-insert theorem. In particular, the stale next/previous fields left by removal are compatible with global unlinkedness; ownership is determined by the root relations and faithful container discipline, not by requiring those stale fields to be cleared.

The checker-green theorem `scheduler_vListRemove_general_exact_state` executes
the actual generated scheduler `vListRemove'` for an arbitrary legal member
position and yields the exact raw removal heap while framing every non-heap
global.  `raw_vListRemove_general_unlinked_effect` and
`raw_family_remove_owner_globally_unlinked` supply the local and family-level
ownership consequences.  On the insertion side,
`raw_ordered_insert_general_transformer_refines_unconditionally` composes the
derived capacity theorem with O4, and the generated theorem reaches that
transformer.  What remains is one source-order `vTaskDelay'` composition that
threads the same decoded item and root family through these independently
checked results.

## 11. Open gates

### Gate L - universal list layer: open

QAD-false theorems now execute the actual generated general ordered-insert and
remove bodies over arbitrary legal raw rings.  Separate QAD-false results
provide ordered relation preservation, derived count capacity, exact
ordered/remove frames, and the legal empty-ring alias.  Gate L nevertheless
remains open: the accepted dependency graph lacks one source-level list-layer
capstone joining generated execution to the capacity-free post-relation and
scheduler-wide Generic/Event frames.  Fresh insert-end also lacks an exported
exact byte-frame theorem in that common scheduler relation.  The obligation
table and minimum capstone are recorded in `GATE_L_CLOSURE_AUDIT.md`.

### Gate H - universal heap/state `vTaskDelay`: open

Checker-green sub-obligations include all-input pure delay equations, modular
yield observation, preservation of a distinct ready task, conditional
finite-task geometry/decoder laws, actual generated general remove and ordered
insert, finite-root global-unlinked derivation, and the proof-only phase/delta
specification. Gate H remains open because there is no checker-green generated
`vTaskDelay'` theorem for arbitrary positive delays and arbitrary scheduler
states. Still required are:

- one complete generic scheduler relation over all relevant roots, TCB fields, scalars, cursors, and delayed roles;
- generic preimage or inhabitation evidence for the claimed state class;
- a raw-sentinel to root-tagged abstract-endpoint bridge for every protected root;
- a source-order generated core proof that retains the wake value computed before removal and threads the same decoded item/root family through removal, key update, root selection, and delayed insertion;
- a generated `xTaskResumeAll'` refinement to a general `ResumeRel` that drains arbitrary pending-ready work before replaying arbitrary missed ticks;
- the conditional internal/outer-yield join without framing roots, tick, top, or current state in the unrestricted resume relation;
- cross-root and unrelated-TCB frame theorems;
- suspend/resume, branch, guard, and termination composition around the now-checked list primitives;
- an audited capstone whose assumptions contain the declared API boundary and no selected poststate.

### Gate D - five-root dispatcher and trace gate: open

No checker-green universal dispatcher or arbitrary finite-call trace theorem exists. The remaining obligations include whole-operation refinements for all five roots, their reachable helper closure and branches, preservation of one common invariant, and sequential composition over arbitrary finite valid call traces. Concurrency, port context switching, lifecycle operations, allocator correctness, compiler correctness, and machine-code refinement remain separate stronger layers unless explicitly added.

## 12. Tool and trust boundary

The accepted logical evidence is ordinary Isabelle theorem checking with `quick_and_dirty = false`. The listed checker-green theories contain no accepted `sorry`, `oops`, admitted desired axiom, or oracle shortcut.

The trust and evidence boundary is:

```text
frozen source/configuration and externally validated artifact metadata
                         |
                         v
              CParser / AutoCorres2 translation
                         |
                         v
        generated monadic source semantics and ABI records
                         |
                         v
             Isabelle/HOL definitions and proofs
                         |
                         v
              Isabelle kernel theorem objects
```

The builder, artifact ledger, CParser, AutoCorres2, and Isabelle implementation remain toolchain assumptions. The correspondence from the frozen binary/layout evidence to generated address definitions is externally validated; it is not an Isabelle theorem. The universal abstract theories do not repair that artifact link, and abstract execution equations do not imply generated-source execution.

ChatGPT Pro contributes design review and adversarial source-order traces, not
theorem objects. CParser/AutoCorres2 already provides the relevant symbolic
execution and verification-condition generation; another generic C symbolic
executor or SMT backend would not synthesize the missing loop, ownership, or
resume invariant.  The useful optional accelerator is a narrow untrusted trace
normalizer that reports generated locals, guards, aliases, field writes, root
changes, and exit states for symbolic phase inputs.  Its output remains a
candidate or falsification probe. A fact enters the proof inventory only when
replayed as an ordinary theorem in the declared Isabelle session.

## 13. Theorem ledger

| Status | Theory / theorem | Quantified content | Boundary |
|---|---|---|---|
| CHECKER-GREEN | `eal6_port_yield_mod_refines_request_yield` | Generated proof-port yield refines modular abstract `request_yield` | Yield primitive only |
| CHECKER-GREEN | `task_delay_abs_positive_universal_effects` | Arbitrary positive delay, state, current task, modular branch, ready/delayed effects | Pure abstract semantics |
| CHECKER-GREEN | `task_delay_abs_all_inputs_capstone` | All abstract delay words and current-task options | Pure abstract semantics |
| CHECKER-GREEN | `task_delay_abs_preserves_other_ready_member` | Preservation of every different ready task | Requires an existing distinct ready member |
| CHECKER-GREEN | `task_delay_abs_some_ready_task_remains` | Existence of a post-delay ready task under an explicit distinct-member premise | Does not create a ready task from no premise |
| CHECKER-GREEN | `scheduler_ordered_loop_read_bridge` | Generated/raw next, key, guard, and cycle-node agreement for arbitrary valid rings | Read bridge, not loop correctness |
| CHECKER-GREEN | `universal_different_live_component_regions_disjoint` | Cross-task separation for TCB/generic/event components over arbitrary finite live sets | Conditional on explicit geometry |
| CHECKER-GREEN | `universal_different_live_component_bases_neq` | Cross-task component pointer inequality | Conditional on explicit geometry |
| CHECKER-GREEN | decoder `iff` lemmas and `universal_geometry_scheduler_decode_rel` | Forward/inverse decoder facts and transfer to existing relation | Conditional on explicit decoder laws |
| CHECKER-GREEN | `raw_node_id_card` | Actual raw pointer type has cardinality $2^{32}$ | Frozen 32-bit address model |
| CHECKER-GREEN | `raw_xlist_rel_fresh_count_can_increment` | Legal raw list plus fresh item implies count capacity | Local list input |
| CHECKER-GREEN | `Scheduler_Ordered_Insert_General_Source` scan/split lemmas | Pure $P/S$ split, prefix/suffix, predecessor/successor, and maximum-key facts | Foundation for generated loop theorem |
| CHECKER-GREEN | `scheduler_vListInsert_ordered_general_exact_state` | Actual generated `vListInsert'`, arbitrary legal ordered ring and scan position, duplicates, all 32-bit keys, exact post-globals | List primitive; global ownership supplied separately |
| CHECKER-GREEN | `raw_ordered_insert_general_effect_refines` and `raw_ordered_insert_general_transformer_refines` / O4 | Universal local raw ordered-insert effect and relation | Explicit legal-input premises; not scheduler-global ownership |
| CHECKER-GREEN | `raw_ordered_insert_general_heap_exact_external_frame` / O4 | Heap equality outside the exact six-field write footprint | No $c\ne q$ premise; includes empty-ring alias |
| CHECKER-GREEN | `raw_ordered_insert_general_transformer_refines_unconditionally` | Ordered raw-list relation plus local freshness imply the transformed ordered relation; count capacity is derived internally | Local list refinement; no global ownership claim |
| CHECKER-GREEN | `scheduler_vListRemove_general_exact_state` | Actual generated `vListRemove'`, arbitrary legal member position/cursor/aliases, exact removal heap and non-heap-global frame | List primitive, not full delay call |
| CHECKER-GREEN | `raw_family_remove_owner_globally_unlinked` | Unique entry owner plus owner post and other-root frames imply the removed item belongs to no protected root | Finite protected root family |
| CHECKER-GREEN | `Scheduler_Universal_Delay_Phases` cutpoint/delta/yield theorems | Arbitrary finite live set, positive priority-level count, roots/rings/cursors/tick/delay; stale links/top and conditional yield | Abstract phase specification, not generated ResumeAll refinement |
| CHECKER-GREEN ABSTRACT / OPEN SOURCE BRIDGE | `Scheduler_Resume_General_Relation` | Arbitrary pending-ready drain followed by arbitrary missed-tick replay, conditional yield; generated yield leaf connected | Whole generated `xTaskResumeAll'` theorem missing |
| FIXED WITNESS ONLY | frozen P2 capstone | One inhabited generated-source refinement path | Regression evidence, not universal evidence |

## 14. Current conclusion

The development now contains genuine universal-input mathematics: arbitrary
abstract delay arithmetic and effects, a modular generated yield observation,
ready-member preservation, arbitrary-ring generated/raw read bridges,
finite-task component geometry with explicit decoder laws, a derived 32-bit
count-capacity theorem, and actual generated general `vListInsert'` and
`vListRemove'` executions. None of these relies on enumerating priority
combinations or fixing a semantic witness.

The central source-level theorem is nevertheless still missing. Gate L awaits
one checked dependency closure joining generated execution, capacity-free list
relations, insert-end, and scheduler-wide frames. Gate H awaits the root-tagged
raw/phase endpoint bridge, the generated suspended-core composition, and the
general `xTaskResumeAll'`/`ResumeRel` theorem; the quiescent result is only a
labelled corollary. Gate D remains open independently. The correct current
result is therefore:

> **Reusable universal-input proof bricks are checker-green; universal FreeRTOS V6.1.1 scheduler functional correctness is not yet proved.**
