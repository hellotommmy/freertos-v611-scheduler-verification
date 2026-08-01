# Handoff: frozen-build data-layout certificate for P2 non-vacuity

## Objective

Close the remaining deployment-instance non-vacuity gap for the already-green
conditional theorem `scheduler_vTaskDelay_2_p2_refines_task_delay_abs`.

Do not add another symbolic executor, SMT backend, axiom, oracle theorem,
`sorry`, `oops`, or proof-motivated C/source change.  The operational and
relation proofs are already green.  This task is solely about binding the
unconstrained addressed-data constants to one exact linked FreeRTOS build.

## Required distinction

Keep four milestones separate:

1. conditional source functional correctness -- already green;
2. synthetic-layout satisfiability -- useful but not a deployment claim;
3. exact frozen-build layout instantiation -- required for deployment-instance
   P2 non-vacuity;
4. reachability from boot/initialisation -- a later milestone.

## Inputs to freeze

Record hashes and versions for the exact:

- official FreeRTOS V6.1.1 source and selected port/configuration;
- compiler, assembler, linker, and flags;
- linker script;
- ELF and supporting link map/DWARF/symbol-table outputs;
- current Isabelle/CParser/AutoCorres2 session inputs.

Treat the ELF as authoritative; a textual link map is supporting evidence.

## Proof interface

Design a locale or equivalent checked interface for the concrete addresses of:

- ready roots 0..3;
- delayed-A and delayed-B roots;
- pending and suspended roots;
- the P2_IDLE and P2_RUN TCB objects;
- the embedded Generic and Event list items and list sentinels.

The interface must provide the exact guards, alignment, object extents,
containment, distinctness, and byte-region separation needed by
`p2_source_footprint`.  It must also connect the locale values to the actual
CParser addressed-data constants; assumptions that are never discharged do
not close the task.

## Certificate path

Prefer this architecture:

1. an untrusted extractor reads the frozen ELF and emits candidate addresses,
   sizes, and hashes as data;
2. a small independently reviewable checker validates symbol identity,
   extents, alignment, containment, and pairwise interval separation;
3. Isabelle checks the resulting concrete arithmetic/interval certificate and
   instantiates the data-layout locale;
4. construct the two-task decoder, byte heap, and globals satisfying
   `scheduler_endpoint_rel StableRunning ... p2_pre` and
   `p2_source_footprint`;
5. prove the final existential witness for the exact frozen build.

If a verified ELF parser is unavailable, document the residual extractor or
binary-analysis trust boundary explicitly.  Never smuggle extracted facts in
as axioms.

## Minimum final theorem

The result must imply an artifact-bound instance of:

```isabelle
\<exists>D c.
  scheduler_endpoint_rel StableRunning D generated_scheduler_roots c p2_pre
  \<and>
  p2_source_footprint D generated_scheduler_roots
    (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
```

The concrete root constants in this theorem must be linked, by checked
certificate facts, to the symbols in the frozen ELF.

## Existing reusable proof bricks

- `p2_pre_conditional_endpointI`
- `raw_xlist_rel_emptyI` and `raw_xlist_rel_singletonI`
- `sched_xlist_rel_emptyI` and `sched_xlist_rel_ready_singletonI`
- scheduler/raw ABI read and write lenses
- `p2_source_footprint` destructors
- `scheduler_vTaskDelay_2_p2_refines_task_delay_abs`

The fixed raw-list `0x1000/0x2000` witnesses are templates only; they do not
establish the frozen scheduler ELF layout.

## Acceptance

- unique bounded Isabelle build, `quick_and_dirty=false`, exit 0;
- no forbidden proof constructs;
- hashes for the ELF, linker inputs, extracted certificate, theory, and run;
- explicit statement of any remaining parser/checker trust boundary;
- ledger wording changes from `frozen-build-layout P2 non-vacuity: open` to
  `green` only after the exact artifact-bound existential theorem is checked.
