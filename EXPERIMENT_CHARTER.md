# Experiment charter

## Research question

Starting only from the unannotated FreeRTOS V6.1.1 C source, its public user
requirements, and explicitly allowed papers, can we independently reconstruct:

- an executable top-level scheduler ADT;
- a source-to-ITP mapping;
- the concrete/abstract representation relation;
- global and per-operation invariants;
- a dependency-ordered lemma graph; and
- a machine-checked Isabelle/HOL refinement proof?

After the blind result is sealed, compare its structure and measured cost with
the original VCC/Z formalization and with E1 (the earlier proof-body-only
baseline, once its data are supplied).

## Frozen semantic boundary

- Upstream release: FreeRTOS V6.1.1.
- Component: scheduler-related core APIs in `tasks.c` plus the `xList`
  implementation in `list.c` and the minimal types/helpers/macros they execute.
- Concurrency model for this experiment: operations are atomic at public API
  boundaries. Interrupt arrival inside an API, context-switch assembly, port
  code, allocator correctness, and client-task execution are external.
- The unmodified upstream release is revision 0. Any bug discovered against
  public requirements is preserved as a counterexample before a separately
  hashed semantic revision is proposed.

## Provisional target gate

The target is accepted only when all are true:

1. the exact physical C slice is 500--800 lines under a recorded counting rule;
2. each included line is justified by an executed dependency, not padding;
3. host build/tests execute representative list and scheduler paths;
4. `list` init/insert/remove translate with the real unannotated bodies;
5. at least one scheduler operation translates without a semantic source
   rewrite;
6. all port/config substitutions are documented contracts or preprocessing
   choices, with satisfiable witnesses.

## Blindness boundary

Before `BLIND_SEAL.md` exists and its commit/hash is recorded, nobody working
on this tree may download, open, search, quote, or inspect the original VCC
annotations, Z models, abstraction relation, invariants, proof scripts, or
supplementary archive.  Repository-tree metadata that exposes proof filenames
is also avoided.  The original artifact must live outside this worktree and is
not fetched during the blind phase.

## Evidence classes

- `CHECKER_GREEN`: an exact theorem checked by Isabelle with the recorded
  command and hash.
- `EXECUTED_EVIDENCE`: build/test/trace output with command and hash.
- `PAPER_REPORTED`: a fact reported by an allowed paper, not locally replayed.
- `EXPERT_JUDGMENT`: a design or cost judgment.
- `PLANNING_EXTRAPOLATION`: an unmeasured forecast.

## Stop or redesign conditions

- the 500--800 LOC gate fails after honest dependency accounting;
- C translation requires observable-behaviour changes rather than an audited
  proof port/configuration;
- the abstraction premises exclude a core public behaviour;
- the intended public requirements are inconsistent;
- the same proof architecture fails three materially different ways after a
  checked counterexample/design review;
- the toolchain cannot be reproduced in a clean bounded run.

