# Row/Block Checker Roadmap for Jittered EDF Witnesses

This roadmap describes how to make the jittered periodic EDF compact DBF
checker parallelizable by decomposing the Rocq checker into row/block-level
pure boolean checkers and then evaluating those extracted checkers in Haskell.

The goal is not to change the witness format or the schedulability theorem.
The goal is to expose a proof-backed checker frontier that Haskell can schedule
in parallel.

## 1. Goal

The current extracted checker accepts a schema-v3 compact DBF certificate by
running one monolithic boolean:

```text
check_jittered_edf_compact_dbf_certificate_extracted
```

That boolean combines:

- extracted task-set well-formedness;
- cutoff and compact-basis field checks;
- `all_basis_checked`;
- compact basis DBF/NDBF checks over all flattened basis windows.

The roadmap is to split that checker-internal work into smaller pure checkers:

```text
scalar/header checker
row checker
block checker
block-list checker
```

The decomposed checker must prove the same abstract schedulability claim as the
existing monolithic checker.  Haskell parallelism is only an execution strategy
for evaluating extracted booleans; it is not a new semantic assumption.

## 2. Terminology

- `row checker`: a pure checker for one compact DBF basis row
  `(t2, left_edges)`. A row is only the existing grouping by right endpoint
  `t2`; it is not a new semantic object.
- `block checker`: a pure checker for a finite contiguous batch of basis rows.
- `checker frontier`: a Rocq-defined boolean that is extracted to Haskell and
  paired with a Rocq soundness lemma.
- `runner`: the Haskell command-line wrapper that parses inputs, chooses
  blocks, evaluates extracted booleans, and aggregates results.

In this document, `block` means a checker batch.  It does not mean job
blocking, wait states, suspension, backlog, or OS-level ineligibility.

## 3. Existing Checker Surface

The current proof-facing compact DBF basis is:

```coq
Definition JitteredCompactDbfBasis := list (Time * list Time).
```

It is grouped by right endpoint and flattened by:

```coq
jittered_compact_basis_windows
```

The current top-level compact checker is:

```coq
check_jittered_edf_compact_dbf_certificate_extracted
```

Its soundness path is:

```text
compact basis field equality
  + compact basis DBF/NDBF test
  + reduced compact basis coverage
  => bounded window DBF test by cutoff
  => extracted_jittered_offset_window_dbf_ok_global
```

The existing schema-v3 certificate must remain unchanged:

```coq
Record JitteredEDFCompactDbfCertificate := {
  jedf_compact_cutoff : Time;
  jedf_compact_basis : JitteredCompactDbfBasis;
  jedf_all_basis_checked : bool
}.
```

The CBOR witness keeps the same `cert.dbf.basis` rows:

```text
{ "t2": <nat>, "left_edges": [<nat>, ...] }
```

## 4. Refinement Boundary

The abstract interface is the decoded jittered task set and the compact DBF
certificate obligation.  It contains task parameters, cutoff, basis rows, and
proof-backed boolean checker frontiers over those inputs.  The runner's
evaluated `Bool` results are adapter/tool execution artifacts, not certificate
fields or runtime events.  The proof-facing semantics remain over the flattened
`(t1, t2)` windows produced by `jittered_compact_basis_windows`.

The common layer is responsible for:

- defining row/block checker booleans;
- proving row/block checker soundness;
- proving that block aggregation implies the same obligation as the current
  monolithic checker;
- keeping proof-facing time and DBF semantics over the existing natural-number
  interface, with checker-local `N` kernels hidden behind soundness lemmas.

The adapter/tool layer is responsible for:

- decoding CBOR into the same certificate fields;
- splitting the certificate basis into contiguous blocks;
- preserving row order under `concat`;
- evaluating every required extracted checker result;
- rejecting on parse errors, missing blocks, worker failures, or any `False`.

The concrete runtime layer is intentionally unaffected.  This roadmap adds no
Awkernel scheduler hooks, interrupt paths, timer behavior, queue state, trace
rows, adapter-visible scheduler policy, or runtime event surface.

Thread count, chunk size, cancellation, GHC RTS flags, Rust generator
threading, generator caps, benchmark timing, and local memory use are execution
details.  They are not part of the common certificate interface.

## 5. Rocq Decomposition Roadmap

### Phase R1: Name row and block windows

Add helpers near `JitteredPeriodicCompactDBF.v`:

```coq
Definition jittered_compact_basis_row_windows
    (row : Time * list Time) : list (Time * Time) := ...

Definition jittered_compact_basis_block_windows
    (block : JitteredCompactDbfBasis) : list (Time * Time) := ...
```

Prove flattening lemmas:

```coq
jittered_compact_basis_windows basis =
concat (map jittered_compact_basis_row_windows basis)
```

and the corresponding block/concat lemmas needed to rewrite `forallb`.

### Phase R2: Add row/block DBF checks

Add pure boolean checks:

```coq
jittered_fast_compact_basis_row_dbf_test
jittered_fast_compact_basis_block_dbf_test
jittered_fast_compact_basis_blocks_dbf_test
```

Then add NDBF variants near the final certificate checker:

```coq
jittered_fast_compact_basis_row_ndbf_test
jittered_fast_compact_basis_block_ndbf_test
jittered_fast_compact_basis_blocks_ndbf_test
```

The NDBF variants should reuse the existing N-to-nat bridge, including the
existing equivalence between fast NDBF and nat DBF window checks.

### Phase R3: Add scalar/header checker

Add an extracted scalar/header checker that does the cheap certificate checks
once:

```coq
check_jittered_edf_compact_dbf_scalar_fields_extracted
```

It should cover:

- `extracted_jittered_taskset_wf ts`;
- expected cutoff equality;
- `jedf_all_basis_checked = true`;
- structural basis field requirements that are independent of block execution.

Do not leave full expected-basis equality only in this scalar checker if that
would keep the main bottleneck serial.  Expected row content should be checked
inside row/block checkers or by a block-list checker whose work can be divided.

### Phase R4: Add block checker entry points

Add extracted checker frontiers:

```coq
check_jittered_edf_compact_dbf_basis_block_extracted
check_jittered_edf_compact_dbf_certificate_blocks_extracted
```

Recommended shape:

```coq
check_jittered_edf_compact_dbf_certificate_blocks_extracted
  ts cert blocks :=
    check_jittered_edf_compact_dbf_scalar_fields_extracted ts cert
    && compact_dbf_basis_eqb (concat blocks) cert.(jedf_compact_basis)
    && jittered_fast_compact_basis_blocks_ndbf_test ... blocks.
```

For better parallel payoff, add a block checker that validates expected row
content and NDBF for the block.  Haskell can then run one scalar check plus many
block checks.  If expected-basis equality is split into blocks, the proof must
include either `concat blocks = jittered_edf_compact_dbf_certificate_expected_basis ts`
or an equivalent theorem showing that the block checker implies the same
flattened-basis obligation as the current checker.

### Phase R5: Prove equivalence and soundness

Required common-layer lemmas:

- row/block `forallb` over concat is equivalent to the current flat checker;
- singleton block `[cert.(jedf_compact_basis)]` is equivalent to the current
  monolithic compact basis check;
- if `concat blocks = cert.(jedf_compact_basis)` and the certificate basis is
  exactly the expected basis, then all true block checks imply the current
  compact basis DBF/NDBF obligation;
- scalar fields plus all block checks imply
  `extracted_jittered_offset_window_dbf_ok_global ts`.

The main theorem should be:

```coq
check_jittered_edf_compact_dbf_certificate_blocks_extracted_sound
```

It must conclude the same property as:

```coq
check_jittered_edf_compact_dbf_certificate_extracted_sound
```

### Phase R6: Export during transition

Export both old and new entry points from
`JitteredPeriodicEDFExtraction.v`.

Keep the monolithic checker available until:

- decomposed serial checker matches monolithic checker on fixtures;
- decomposed parallel checker matches decomposed serial checker;
- benchmark results show the row/block frontier moves the 10M-basis bottleneck.

## 6. Haskell Parallel Runner Roadmap

The current Haskell wrapper is serial: it parses CSV and CBOR, validates
metadata, builds one `JitteredEDFCompactDbfCertificate`, and calls the
monolithic extracted checker once.

After the Rocq checker frontier exists, preserve existing invocations and add
optional flags:

```text
jittered_edf_witness_check --tasks TASKS.csv --witness WITNESS.cbor
  [--threads 1|N|auto]
  [--block-windows N]
  [--metrics-out PATH]
```

Initial defaults:

- `--threads 1` for compatibility;
- `--block-windows` chosen to produce enough blocks for large witnesses without
  making tiny witnesses expensive;
- benchmark and pipeline scripts may pass `--threads auto` explicitly.

The runner should:

1. Parse CSV and CBOR once.
2. Validate schema, policy, domain, and task hash before spawning workers.
3. Convert basis rows to extracted row values once.
4. Run the scalar/header checker once.
5. Split rows into contiguous blocks by basis-window count, not raw row count.
6. Evaluate each extracted block checker in a worker.
7. Force every worker result to `Bool`.
8. Aggregate deterministically and reject on the lowest failing block index.

Use only `base` concurrency initially:

```haskell
forkIO
MVar
evaluate
GHC.Conc.setNumCapabilities
```

Avoid adding `async`, `parallel`, or `stm` in the first implementation.  Forcing
the exported checker result to `Bool` with `evaluate` should be sufficient; add
`deepseq` only if a later implementation introduces structured result values or
lazy diagnostic payloads.  Worker cleanup must be structured so an exception in
one worker cannot leave sibling workers running or produce partial output.

Build the checker with:

```text
ghc -O2 -threaded -rtsopts
```

Do not bake in `-with-rtsopts=-N`.  Let `--threads auto|N` call
`setNumCapabilities`; users may still pass `+RTS -s -RTS` for runtime stats.

## 7. Testing Roadmap

Rocq tests and builds:

- row/block helper modules compile;
- row/block flattening lemmas compile;
- block equivalence lemmas compile;
- block checker soundness theorem compiles;
- extraction emits monolithic and decomposed entry points.

Haskell and pipeline tests:

- accepted fixture passes with `--threads 1`, `--threads 2`, and
  `--threads auto`;
- tiny witness passes with `--threads 2 --block-windows 1`;
- monolithic checker, decomposed serial checker, and decomposed parallel
  checker agree on accepted fixtures;
- mutated witnesses still reject under all thread modes:
  - hash mismatch;
  - bad cutoff;
  - extra basis row;
  - changed left edge;
  - `all_basis_checked = false`;
- invalid CLI rejects:
  - `--threads 0`;
  - `--threads nope`;
  - `--block-windows 0`;
- RTS smoke test runs with `+RTS -N2 -RTS` to catch missing `-threaded`.

Benchmark tests:

- record monolithic, decomposed serial, and decomposed parallel checker rows;
- include `thread_mode`, `block_windows`, `block_count`,
  `basis_window_count`, `real_s`, `peak_kb`, and `status`;
- rerun the `cap_stress` case from `edf_witness_performance.md`.

## 8. Open Risks

The main proof risk is not parallel execution.  The main proof risk is
accidentally weakening coverage when converting a total monolithic checker into
independently supplied blocks.

Specific risks:

- incomplete block coverage;
- duplicated blocks masking missing rows;
- row reordering that breaks exact certificate equality;
- keeping expected-basis equality serial, which would leave the main bottleneck
  in place;
- laziness hiding failed work unless each worker result is forced;
- non-threaded Haskell builds silently running on one capability;
- load imbalance because late `t2` rows may have many more left edges;
- diagnostics diverging from boolean semantics;
- confusing checker blocks with OS/job blocking.

Mitigations:

- require `concat blocks = cert.(jedf_compact_basis)` in the proof-facing
  checker path;
- chunk by basis-window count;
- keep monolithic fallback during transition;
- test `--threads 1` and `--threads auto` equivalence;
- keep all runtime/threading details outside the common interface.
