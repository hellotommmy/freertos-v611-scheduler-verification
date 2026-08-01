# Cost comparison schema

Compare the blind reconstruction, E1 proof-body-only baseline, and the original
formalization on the same dimensions:

- target C LOC and API count;
- model/specification LOC;
- representation/invariant LOC;
- proof/annotation LOC;
- executable examples and counterexamples;
- number of invariant revisions;
- number and depth of lemma-graph revisions;
- checker calls, red/green ratio, and bounded checker wall time;
- active design time, proof time, tooling time, and environment time;
- source changes needed for verification;
- strongest checked theorem and concurrency/TCB boundary;
- mutation kills and vacuity/non-vacuity evidence.

E1 fields remain `NOT_AVAILABLE` until the user supplies its artifact or cost
record.  Missing values must not be guessed.

