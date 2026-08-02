# Universal ordered insertion: trace-led invariant audit

Status: invariant-design evidence, **not proof evidence**.

This note records the symbolic traces used to design and falsify the loop
invariant for the generated FreeRTOS V6.1.1 `vListInsert` scan.  No trace fixes
a semantic input in the final theorem.  The accepted theorem must quantify over
every legal ring, key, list/item address and generated source state and must be
checked by Isabelle with `quick_and_dirty = false`.

## Notation

- `E`: the list mini-sentinel, viewed as a full item through the checked ABI.
- `N`: the fresh item to insert.
- `M`: `max_word :: 32 word`.
- `k`: the key read from `N`.
- `xs = P @ S`: the current ghost split of the old ring.
- `c = last (E # P)`: raw predecessor denoted by the generated iterator.
- `q = hd (S @ [E])`: raw successor read through `c.next`.

For the ordinary loop branch, `k != M`.  A continuing loop head has

```text
S = y # ys
key y <= k
(P, y # ys, c)  ->  (P @ [y], ys, y)
```

The scan performs no heap write.  Its natural variant is `length S`.

## Representative symbolic traces

| Shape | Loop/exit trace | Required alias treatment |
| --- | --- | --- |
| Empty, non-max | `P=[]`, `S=[]`, `c=q=E`; the sentinel key `M` makes the guard false | `c=q` is legal; never assume otherwise |
| Before head | `P=[]`, `S=x#X`, `c=E`, `q=x`, `key x > k`; exit immediately | predecessor may be the sentinel |
| One equal key | the guard uses `<=`, so an equal item is consumed before exit | insertion is after the old equal item |
| Many equal keys | consume every equal-key head in turn | stable source order requires `<=`, not `<` |
| Strict middle | consume all `P` keys `<= k`; exit at first `q` with `k < key q` | predecessor and successor are ordinary distinct nodes |
| Tail, non-max | consume the whole old ring; finish with `P=xs`, `S=[]`, `q=E` | successor may be the sentinel |
| Empty, max | bypass the loop; `E.previous=E`, so `c=q=E` | same empty-ring alias class |
| Nonempty, max | bypass the loop; `c=last xs`, `q=E` | all 32-bit keys are `<= M` |

The max branch and normal branch must join at the same scan-exit statement:

```text
c = last (E # takeWhile (\x. key x <= k) xs)
q = hd (dropWhile (\x. key x <= k) xs @ [E])
```

## Candidate killed by the empty ring

The split equations alone are insufficient.  With

```text
xs=[]; P=[]; S=[]; c=q=E
```

all prefix facts hold vacuously.  If the entry relation does not expose
`key E = M`, a heap satisfying only those weak facts could make the generated
guard true at `S=[]`.  The iterator would remain at `E` and `length S` would
remain zero, so the proposed variant would not decrease.

Therefore the generated-loop proof must derive the sentinel-key theorem from
the entry relation (or carry it in the fixed entry context).  It must not add a
postcondition-shaped premise to rule the trace out.

## Refined universal invariant

Separate immutable entry facts from mutable loop facts.

The fixed context `Gamma` contains:

- the complete raw ordered-list relation for arbitrary `xs`;
- checked scheduler/raw ABI pointer and read lenses;
- ring distinctness and pointer-map injectivity;
- exact next/previous topology and all generated read guards;
- the sentinel key `M`;
- freshness and full byte-region separation of `N`;
- `key N = k`; and, in the loop branch, `k != M`.

For an explicit ghost split `P,S`, the mutable invariant should contain only:

```text
state = entry_state
xs = P @ S
all x in set P. key x <= k
abi_item_ptr (iterator carrier) = last (E # map node P)
```

If the actual generated while carrier contains cached arguments in addition to
the iterator, record only that those components retain their entry values.
Do not invent an inverse `scheduler_item_of_raw`; use the already-proved ABI
direction.

The following are derived view lemmas, not mutable ghost state:

```text
q = hd (map node S @ [E])
raw_next entry_heap list c = q
the scheduler next/key reads agree with the raw reads
all exact CParser guards for those reads hold
Guard <-> (exists y ys. S = y # ys and key y <= k)
```

The last equivalence uses `k != M` to eliminate the empty-suffix sentinel
case.  The body preserves the entry heap/state, updates the ghost split to
`P@[y],ys`, and strictly decreases `length S`.  At a false guard, sortedness
and the prefix facts reconstruct the exact `takeWhile`/`dropWhile` split.

Forbidden strengthening:

```text
all x in set S. k < key x
```

It is false at every continuing head.  It is available only as an exit
consequence for the first element of a nonempty suffix.

## Six-write alias audit

After scan exit the source performs, in order:

```text
N.next      := q
q.previous  := N
N.previous  := c
c.next      := N
N.container := L
L.count     := L.count + 1
```

The proof must allow:

- `c=q=E` exactly for the empty ring;
- `c=E` at head insertion;
- `q=E` at tail insertion;
- sentinel fields and list count sharing one packed list object;
- the three writes to distinct fields of `N` sharing the same object.

Freshness must exclude `N=c` and `N=q` and, more importantly, separate the
entire writable item region of `N` from the list root and every existing item.
Root-level disjointness between sentinel fields and list count is false; field
offset/size theorems must justify preservation there.

This spatial predicate is sufficient for the **local target-list** transformer,
but it is not by itself sufficient for a scheduler-wide frame.  A smallest
counterexample has two valid roots `L` and `M`, with `L` empty and `N` the sole
member of `M`: `N` is spatially fresh relative to `L`, yet insertion into `L`
overwrites the links and container by which `M` represents `N`.  The scheduler
composition must therefore derive an ownership-fresh intermediate fact from
the preceding removal, such as `N.container = NULL` under a global invariant
that makes the container field faithful to list membership.  This fact belongs
to remove-to-insert composition, not as a postcondition-shaped premise of the
local insertion theorem.

The strongest common byte frame uses the exact six target field regions:

```text
N.next, q.previous, N.previous, c.next, N.container, L.count
```

For every byte address outside their union, the final heap equals the entry
heap.  This remains valid when `c=q=E`, when a sentinel field and count share
the packed list root, and when three target fields share `N`.  A frame stated
only outside the enclosing list/item objects is sound but weaker and should
not be presented as the exact footprint.

## Optional untrusted invariant probe

AutoCorres2 already provides symbolic execution and verification-condition
generation.  A second generic SMT/executor would not solve the missing
invariant problem.  A narrow trace normalizer could still save iteration time.

Its inputs should be the source hash, generated loop condition/body, max-key
bypass, generated layouts/offsets, checked ABI lenses, raw relation view
lemmas, comparator, sentinel value and the candidate indexed invariant.

Its output should normalize:

1. the loop head (`c`, `q`, scheduler next/key reads and guards);
2. the guard equivalence above;
3. the body ghost transition and unchanged heap/state;
4. the two exit cases and `takeWhile`/`dropWhile` obligations;
5. the six-write alias matrix and required separation facts.

The tool is untrusted.  It may not add assumptions, guess a final predecessor,
suppress a generated guard, declare an alias impossible without a checked
relation theorem, or promote finitely many traces to a universal claim.  Its
only acceptable endpoint is ordinary Isabelle proof text replayed by the
kernel.
