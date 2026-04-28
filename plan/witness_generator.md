# CSV-Driven Rust Witness Generator Roadmap

This roadmap changes the schedulability-witness pipeline from the current
Haskell-generated witness flow to a split architecture:

- Rust generates schedulability witnesses from the existing CSV taskset input.
- Haskell, extracted from Rocq, checks the generated witness.

Awkernel traces are intentionally out of scope for this roadmap.  The generator
must consume the same CSV task data used by the existing checker frontends.

This document is the v1 roadmap.  After v1 is completed, do not proceed
directly to v2 implementation.  First draft the v2 roadmap, append it to this
file, and use that roadmap to decide the next implementation batch.  The v2
roadmap should cover the next checker-facing extension, with release-jitter
CSV witness generation as the primary candidate once the Rocq / extracted
Haskell side exposes a checked sidecar certificate API for jittered EDF.

---

## 1. Semantic assumptions

- The Rust witness generator is not trusted.  It may perform heavy search,
  prefix simulation, transport construction, DBF-table construction, and
  parallel generation, but its output is accepted only after Haskell checking.
- The Haskell checker remains the trusted executable boundary because it calls
  functions extracted from Rocq.
- The initial target is periodic EDF with optional offsets:

  ```text
  cost,period,deadline[,offset]
  ```

- `cost`, `period`, and `deadline` must be positive.  `offset` must be
  nonnegative and defaults to `0`.
- The witness must encode certificate data, not an operational trace.
- No Awkernel trace, timestamp normalization, runtime event vocabulary, YAML
  witness, or GraphML witness is part of this batch.
- Jittered EDF remains on the existing cutoff-checker path until a
  jittered-periodic checked sidecar certificate API exists on the Rocq /
  extracted-Haskell side.

---

## 2. Required observable events

No runtime observable event is required.

The CSV-driven generator does not consume scheduler events.  It computes a
certificate directly from task metadata and a generated EDF prefix.  Therefore:

- do not add new common-layer Rocq events;
- do not add Awkernel trace dependencies;
- do not require `job_release`, `dispatch`, `preempt`, or `job_complete`
  events in this implementation batch;
- keep any future trace integration as a separate adapter-layer roadmap.

---

## 3. Interface delta

### Rust generator

Add a Rust CLI crate, preferably under the Awkernel workspace:

```text
tools/sched-witness-gen
```

Required command surface:

```text
sched-witness-gen periodic-edf --tasks TASKS.csv --out WITNESS.json --threads auto
sched-witness-gen periodic-edf --tasks TASKS.csv --out WITNESS.json --threads N
```

The generator accepts the same periodic CSV shape as
`scripts/periodic_edf_schedulability_csv.hs`:

```text
cost,period,deadline
cost,period,deadline,offset
```

Rows may omit the header if they follow the same column order.

### Haskell checker

Add a Haskell checker frontend:

```text
scripts/periodic_edf_witness_check.hs
```

Required command surface:

```text
periodic_edf_witness_check --tasks TASKS.csv --witness WITNESS.json
periodic_edf_witness_check --tasks TASKS.csv --offsets --witness WITNESS.json
```

The checker parses CSV tasks and witness JSON, reconstructs extracted Haskell
certificate values, and calls:

- `check_periodic_edf_checked_sidecar_extracted`
- `check_periodic_edf_checked_sidecar_extracted_with_offsets`

depending on whether offsets are enabled.

### Witness JSON

Use canonical JSON for the first implementation.  The JSON schema should map
directly to extracted Haskell constructor shapes:

- `EDFPrefixCert`
- `EDFTransportClass`
- `EDFTransportCert`
- `EDFDBFCert`
- `EDFInfiniteCert`
- `EDFWindowTransportPairCert`
- `EDFWindowTransportTargetCert`
- `PeriodicEDFCheckedSidecarCert`

Required top-level fields:

```json
{
  "schema_version": 1,
  "policy": "periodic-edf",
  "domain": "uniprocessor",
  "task_hash": "sha256:...",
  "generator": {
    "name": "sched-witness-gen",
    "version": "0.1"
  },
  "cert": {},
  "sidecar": {},
  "generator_stats": {}
}
```

The checker must reject mismatched `schema_version`, `policy`, `domain`, or
`task_hash`.

The `cert.prefix` object stores:

- `horizon`
- `basis_jobs`
- `slots`
- `completed_by`
- `backlog_free_matrix`

The `cert.transport` object stores:

- `period`
- `basis_jobs`
- `classes`
- `job_class`
- `job_shift`

The `cert.dbf` object stores:

- `cutoff`
- `ok_table`

The `sidecar` object stores:

- `candidate_jobs`
- `class_relevant_jobs`
- `window_target_certs`
- `post_reset_window_target_certs`

JSON arrays must be serialized in deterministic order.

---

## 4. Implementation roadmap

### PR 1: Schema and Haskell checker frontend

- Define the JSON schema in `plan/witness_generator.md` and mirror it in the
  Haskell parser.
- Parse CSV using the same validation policy as
  `scripts/periodic_edf_schedulability_csv.hs`.
- Convert JSON fields into extracted Haskell constructors:
  `Build_EDFPrefixCert`, `Build_EDFTransportClass`,
  `Build_EDFTransportCert`, `Build_EDFDBFCert`, `Build_EDFInfiniteCert`,
  `Build_EDFWindowTransportPairCert`,
  `Build_EDFWindowTransportTargetCert`, and
  `Build_PeriodicEDFCheckedSidecarCert`.
- Call the extracted checker and print `ACCEPT` or `REJECT`.
- On rejection, report the first failed frontend check available at the
  Haskell layer: malformed JSON, task hash mismatch, invalid task CSV, or
  extracted checker rejection.

### PR 2: Single-threaded Rust periodic EDF generator

- Implement CSV parsing and task hashing.
- Generate periodic jobs with the same job-id convention expected by the
  extracted periodic codec.
- Compute:
  - prefix horizon,
  - prefix basis jobs,
  - EDF prefix slots,
  - per-job completion times,
  - backlog-free matrix,
  - transport period,
  - transport classes,
  - transport job class / shift tables,
  - DBF cutoff table,
  - window target certificates,
  - post-reset window target certificates.
- Emit canonical JSON accepted by the Haskell frontend.

### PR 3: Parallel Rust generation

Use Rayon for independent certificate-generation phases:

- per-task job enumeration;
- per-job completion-time computation;
- backlog-free matrix rows;
- transport target certificates;
- post-reset target certificates;
- DBF table entries.

Parallel workers must return indexed results.  The final serializer must sort
by stable indices before writing JSON.

### PR 4: Determinism and reproducibility

- Add `--threads N` and `--threads auto`.
- Ensure `--threads 1`, `--threads 2`, and `--threads auto` produce
  byte-identical JSON for the same CSV and generator version.
- Use canonical JSON serialization:
  - stable object field order,
  - stable array order,
  - no nondeterministic map iteration,
  - normalized integer representation.
- Include `generator_stats` for observability, but keep fields deterministic
  unless the user asks for timing data.  Timing data should be optional because
  it breaks byte-for-byte reproducibility.

### PR 5: Integration scripts and fixtures

- Add a wrapper script that runs:

  ```text
  sched-witness-gen periodic-edf --tasks TASKS.csv --out WITNESS.json
  periodic_edf_witness_check --tasks TASKS.csv --witness WITNESS.json
  ```

- Add small golden CSV fixtures:
  - zero-offset accepted taskset;
  - offset accepted taskset;
  - unschedulable taskset whose generated witness is either absent or rejected;
  - malformed CSV rejection.
- Add witness mutation tests:
  - slot mutation;
  - completion-time mutation;
  - transport class-id mutation;
  - DBF table mutation;
  - task-hash mutation.

### PR 6: Performance and scaling

- Add synthetic large-taskset benchmarks.
- Compare the Rust generator against the current Haskell-side prefix
  generation path.
- Record:
  - task count,
  - generated job count,
  - prefix horizon,
  - DBF window count,
  - target certificate count,
  - thread count,
  - wall-clock runtime,
  - peak memory if available.

---

## 5. Proof obligations

- Haskell checker must not trust Rust-generated certificate fields.
- Parsed JSON must be converted into extracted constructor values without
  semantic shortcuts.
- The extracted checker remains responsible for:
  - prefix semantic checking,
  - generated EDF prefix matching,
  - hyperperiod reset checking,
  - transport certificate checking,
  - transport basis `NoDup` checking,
  - class backlog checking,
  - generated periodic transport checking,
  - transport residue coverage,
  - transport residue shifts,
  - window target completeness,
  - generated pair semantics and completion checks,
  - post-reset target coverage,
  - DBF schedulability decision.
- Rust generator correctness is validated by tests and benchmarks, not trusted
  by the proof story.
- No Rocq common-layer semantics need to change for the CSV-driven generator.

---

## 6. Test plan

- Acceptance tests:
  - zero-offset periodic EDF CSV generates a witness accepted by Haskell;
  - offset periodic EDF CSV generates a witness accepted by Haskell with
    `--offsets`.
- Rejection tests:
  - malformed CSV is rejected by Rust and Haskell frontend parsing;
  - mutated slots are rejected;
  - mutated completion times are rejected;
  - mutated transport class IDs are rejected;
  - mutated DBF table entries are rejected;
  - mismatched `task_hash` is rejected.
- Determinism tests:
  - compare generator output for `--threads 1`, `--threads 2`, and
    `--threads auto`;
  - compare output across repeated runs with the same thread count.
- Compatibility tests:
  - existing `scripts/periodic_edf_schedulability_csv.hs` behavior remains
    unchanged;
  - existing jittered CSV cutoff checker behavior remains unchanged.
- Performance tests:
  - benchmark small, medium, and large synthetic CSV tasksets;
  - ensure parallel mode improves large cases without changing output.

---

## 7. Risks for the Rust design

- Do not combine generation and checking into a single trusted Rust binary.
- Do not make Rust-side witness generation part of the soundness boundary.
- Do not introduce Awkernel trace assumptions in this batch.
- Do not let Rayon scheduling order affect JSON output.
- Do not make timing fields part of canonical witness hashes.
- Do not extend jittered witness generation until the Haskell / Rocq side has a
  checked sidecar certificate API for jittered EDF.
- Do not encode runtime-specific event vocabulary into common Rocq schedule
  semantics.

---

## Progress

Update this section after each implementation batch.

- PR 1 started:
  - added `scripts/periodic_edf_witness_check.hs`
  - the checker parses periodic EDF CSV input and witness JSON with `aeson`
  - task identity is checked with `crypton` SHA-256 over canonicalized CSV task
    metadata
  - parsed JSON is converted into extracted Haskell certificate constructors
  - the checker calls the extracted periodic EDF checked-sidecar entry points
    for zero-offset and offset-aware modes
  - generated checker binaries are ignored by `.gitignore`
- Verification:
  - `stack exec -- ghc -package aeson -package crypton -iextracted/haskell ...`
    builds `scripts/periodic_edf_witness_check`
- PR 2 started:
  - added Rust workspace crate `tools/sched-witness-gen`
  - implemented `sched-witness-gen periodic-edf --tasks TASKS.csv --out WITNESS.json`
  - PR2 accepts `--threads auto` and `--threads 1`; multi-threaded generation
    remains reserved for PR3
  - generator parses legacy periodic EDF CSV input, computes the canonical task
    hash, simulates a deterministic EDF prefix, builds transport/window
    sidecar certificate data, and emits schema v1 JSON for the Haskell checker
- PR 3 started:
  - added Rayon-based generation paths to the Rust witness generator
  - `--threads 1` keeps serial generation, `--threads N` uses a fixed Rayon
    pool, and `--threads auto` uses Rayon default parallelism
  - parallelized independent certificate construction phases while preserving
    deterministic vector ordering and JSON serialization
- PR 4 started:
  - added `test-sched-witness-gen-determinism` to exercise reproducible witness
    generation from the scheduling_theory make layer
  - the test generates zero-offset and offset CSV witnesses with `--threads 1`,
    `--threads 2`, and `--threads auto`, then compares the JSON byte-for-byte
  - the test also locks the `--threads 0` validation error so invalid thread
    modes continue to fail before witness generation
- PR 5 started:
  - added CSV fixtures for zero-offset, offset, unschedulable, and malformed
    periodic EDF witness pipeline cases
  - added `scripts/run_periodic_edf_witness_pipeline` to run Rust witness
    generation followed by extracted-Haskell witness checking
  - added make targets to build `periodic_edf_witness_check` with `aeson` and
    `crypton`, then test accepted cases, rejected CSV/tasksets, and mutated
    witness fields
- PR 6 started:
  - added generator-side `--metrics-out` for deterministic structural metrics
    outside the canonical witness JSON
  - added a benchmark script and make target for synthetic small, medium,
    large, and limit-near periodic EDF CSV cases
  - benchmark rows compare Rust witness generation across `--threads 1`,
    `--threads 2`, and `--threads auto` with the existing Haskell prefix
    checker path
- v1 complete:
  - PR 1 through PR 6 establish the CSV-driven periodic EDF witness pipeline
    with Rust generation, extracted-Haskell checking, deterministic output,
    integration tests, and benchmark tooling
  - the next batch must start from the v2 roadmap below before any
    release-jitter witness generator implementation begins

---

## V2 Roadmap: Release-Jitter Witness Generation

This v2 roadmap extends the CSV-driven witness pipeline toward release-jitter
periodic EDF tasksets.  It is a roadmap for future implementation, not an
implementation batch.  The first v2 work item is checker-facing: expose a
jittered-periodic checked sidecar certificate API on the Rocq / extracted
Haskell side.  Rust-side jittered witness generation must wait until that
checker API exists.

### V2 semantic assumptions

- The Rust witness generator remains untrusted.
- The extracted Haskell checker remains the trusted executable boundary.
- V2 remains CSV-driven; Awkernel traces, runtime event vocabularies, GraphML,
  and YAML witnesses remain out of scope.
- Release jitter is task-generation metadata, not part of the core `Task`
  record and not a runtime event.
- Arrival offset and release jitter are separate parameters.
- Until a checked sidecar API exists for jittered periodic EDF, jittered CSVs
  stay on the existing cutoff/window DBF checker path.

### V2 interface direction

The intended future CSV shape is:

```text
cost,period,deadline,offset,jitter
```

The v1 CSV shapes remain valid for the v1 periodic EDF witness pipeline:

```text
cost,period,deadline
cost,period,deadline,offset
```

Jittered witnesses should use a new witness schema version rather than
overloading schema v1 with optional jitter fields.  The checker must reject
schema/policy/domain/task-hash mismatches before calling extracted certificate
checking code.

### V2 implementation roadmap

#### V2 PR 1: Jittered checked sidecar API design

- Define the Rocq-side certificate shape needed for jittered periodic EDF.
- Expose extracted Haskell checker entry points for jittered sidecar
  certificates.
- Keep the API checker-facing and independent from Rust generation details.
- Required obligations include:
  - jittered release-window coverage;
  - offset and jitter bound checking;
  - window DBF coverage;
  - certificate field well-formedness;
  - rejection of malformed or incomplete certificate data.

#### V2 PR 2: Haskell JSON checker frontend

- Add a schema-v2 JSON parser for jittered periodic EDF witnesses.
- Parse CSV tasks with explicit `offset,jitter` columns.
- Recompute the canonical task hash over `cost,period,deadline,offset,jitter`.
- Convert parsed JSON into extracted jittered certificate constructors.
- Print `ACCEPT` only when the extracted checker accepts.

#### V2 PR 3: Rust CSV parsing and task identity

- Extend Rust-side task parsing for the v2 jittered CSV shape.
- Keep v1 periodic CSV parsing unchanged.
- Add v2 task hashing that includes jitter separately from offset.
- Reject jittered witness generation when the checker-facing API is not
  available.

#### V2 PR 4: Rust jittered certificate generation

- Implement jittered witness generation only after V2 PR 1 and V2 PR 2 exist.
- Generate certificate data accepted by the extracted Haskell jittered checker.
- Preserve deterministic ordering and thread-independent output.
- Keep timing and performance data outside canonical witness JSON.

#### V2 PR 5: Integration and mutation tests

- Add accepted jittered CSV fixtures.
- Add rejected malformed and unschedulable jittered cases.
- Add mutation tests for jitter, offset, release-window coverage, DBF table
  fields, and task hash.
- Keep existing v1 periodic EDF pipeline tests unchanged.

#### V2 PR 6: Performance and limit tuning

- Reuse the v1 benchmark infrastructure for jittered tasksets.
- Compare jittered Rust generation against the extracted cutoff/window DBF
  path.
- Use benchmark data before raising generator limits or adding limit override
  flags.

### V2 risks for the Rust design

- Do not implement jittered Rust witness generation before the extracted
  checker can validate jittered certificates.
- Do not encode release jitter as Awkernel trace behavior.
- Do not collapse offset and jitter into one field.
- Do not make schema v1 accept optional jitter fields.
- Do not add timing or worker-count fields to canonical witness JSON.

### V2 progress

- V2 PR 1 started:
  - added a DBF-only `JitteredEDFDbfCertificate` Rocq certificate shape
  - added an extraction-facing jittered EDF DBF certificate checker
  - the checker recomputes task well-formedness, cutoff, critical windows, and
    the cutoff DBF decision instead of trusting Rust-provided fields
  - proved that accepted DBF certificates imply the existing global jittered
    offset-window DBF property
  - exposed the certificate constructor and checker entry point in the
    extracted Haskell jittered schedulability module
- V2 PR 2 started:
  - added `scripts/jittered_edf_witness_check.hs`
  - the checker parses schema-v2 JSON with a DBF-only jittered EDF certificate
  - jittered witness checking requires explicit five-column CSV input:
    `cost,period,deadline,offset,jitter`
  - task identity is checked with `crypton` SHA-256 over canonicalized jittered
    CSV task metadata
  - parsed JSON is converted into extracted `JitteredEDFDbfCertificate`
    constructors and checked by `check_jittered_edf_dbf_certificate_extracted`
  - added make targets to build and test the jittered witness checker frontend
- V2 PR 3 started:
  - added a `jittered-periodic-edf` Rust generator subcommand
  - added Rust parsing for explicit five-column jittered CSV tasksets
  - added schema-v2 jittered task hashing that keeps `offset` and `jitter`
    separate and matches the Haskell witness checker canonical metadata
  - the jittered Rust path validates `--threads`, parses CSV, computes the
    task hash, and then rejects generation until V2 PR4
  - kept the existing schema-v1 `periodic-edf` generator path unchanged
- V2 PR 4 started:
  - implemented DBF-only schema-v2 witness generation for
    `sched-witness-gen jittered-periodic-edf`
  - generated jittered witnesses contain cutoff, checked critical windows, and
    `all_windows_checked` for the extracted Haskell checker
  - Rust computes critical windows in the same order as the Rocq/extracted
    checker and rejects unschedulable tasksets before writing output
  - `--threads 1`, fixed-thread, and `--threads auto` preserve deterministic
    JSON output for the same jittered CSV
  - integration tests now generate a jittered witness and validate it with
    `scripts/jittered_edf_witness_check`
- V2 PR 5 started:
  - added fixture-backed jittered EDF witness pipeline coverage
  - added `scripts/run_jittered_edf_witness_pipeline` as the schema-v2
    generator/checker wrapper
  - added accepted zero-jitter and nonzero-release-jitter CSV fixtures
  - added malformed, four-column, and unschedulable rejected fixtures
  - added pipeline mutation coverage for task hash, offset, jitter, cutoff,
    checked DBF windows, and `all_windows_checked`
- V2 PR 6 started:
  - added generator-side `--metrics-out` for deterministic jittered DBF
    structural metrics outside canonical schema-v2 witness JSON
  - added a jittered benchmark script and make target for small, medium,
    large, and limit-near CSV tasksets
  - benchmark rows compare Rust witness generation across `--threads 1`,
    `--threads 2`, and `--threads auto` with the extracted Haskell jittered
    cutoff checker path
  - the limit-near Haskell comparison is skipped by default because the
    extracted cutoff checker is intentionally much heavier on that case

---

## V3 Roadmap: Compact Jittered DBF Certificates And Fast Checking

V3 reduces the cost of the release-jitter witness path introduced in V2.  The
current schema-v2 certificate records every bounded critical window and the
checker recomputes that full list before calling the cutoff DBF decision.  This
keeps the trust boundary simple, but it makes large witnesses and checker runs
expensive.

V3 replaces the full `checked_windows` list with a compact, checker-validated
basis and adds a faster arithmetic demand checker.  The goal is to reduce
witness size, Rust generation time, and extracted-Haskell checking time without
trusting Rust-provided demand values.

### V3 semantic assumptions

- The Rust witness generator remains untrusted.
- The extracted Haskell checker remains the trusted executable boundary.
- V3 remains CSV-driven; Awkernel traces, runtime event vocabularies, GraphML,
  and YAML witnesses remain out of scope.
- Release jitter remains task metadata, not part of a runtime event stream.
- Schema v2 remains supported until schema v3 has stable benchmarks and
  mutation tests.
- Metrics and timing data remain outside canonical witness JSON.

### V3 interface direction

Add schema version 3 for jittered periodic EDF witnesses.  Schema v2 keeps:

```json
"checked_windows": [[0, 0]],
"all_windows_checked": true
```

Schema v3 should replace this full list with a compact basis:

```json
"basis": [
  { "t2": 0, "left_edges": [0] }
],
"all_basis_checked": true
```

The Rust generator should support:

```text
sched-witness-gen jittered-periodic-edf --tasks TASKS.csv --out WITNESS.json --witness-schema 2
sched-witness-gen jittered-periodic-edf --tasks TASKS.csv --out WITNESS.json --witness-schema 3
```

Default to schema v3 only after the schema-v3 extracted Haskell checker exists.
Extend generator metrics with `basis_window_count`, still outside canonical
witness JSON.

### V3 implementation roadmap

#### V3 PR 1: Compact basis theory

- Define a compact jittered DBF basis at the Rocq analysis layer.
- Keep all bounded right endpoints `t2 <= cutoff`, but reduce left endpoints to
  demand-plateau right edges.
- Prove that checking the compact basis implies the current bounded window DBF
  property for every `t1 <= t2 <= cutoff`.
- Keep the proof independent from Rust ordering, JSON shape, and thread count.

#### V3 PR 2: Fast arithmetic demand checker

- Add an extraction-friendly closed-form release count for one task/window.
- Prove that the arithmetic count equals the current enumerated
  `jittered_periodic_dbf_window` count.
- Use the closed-form count in the extracted checker path for compact basis
  validation.
- Keep the old enumerating checker available until schema-v3 regression tests
  are stable.

#### V3 PR 3: Schema-v3 Haskell checker frontend

- Parse schema-v3 compact basis certificates in
  `scripts/jittered_edf_witness_check.hs`.
- Convert schema-v3 JSON into a new Rocq/extracted compact certificate type.
- Reject malformed basis rows, unsorted basis data, duplicate rows, incomplete
  basis coverage, cutoff mismatch, schema/policy/domain mismatch, and task-hash
  mismatch.
- Continue accepting schema-v2 witnesses through the existing DBF-only checker.

#### V3 PR 4: Rust schema-v3 generator

- Generate compact basis rows instead of full `checked_windows` for schema v3.
- Preserve deterministic output for `--threads 1`, fixed-thread modes, and
  `--threads auto`.
- Keep `--witness-schema 2` for compatibility during the transition.
- Do not emit Rust-computed demand values as trusted certificate fields.

#### V3 PR 5: Integration, mutation, and benchmark comparison

- Add accepted and rejected schema-v3 jittered fixtures.
- Add mutation tests for omitted basis rows, altered left edges, duplicate
  rows, cutoff mismatch, `all_basis_checked`, and task hash.
- Compare schema v2 and schema v3 for witness size, Rust generation time,
  Haskell checking time, full window count, and compact basis count.
- Use benchmark data before raising any generator or checker limits.

### V3 proof obligations

- Compact basis completeness: every bounded window is covered by a checked
  basis window.
- Left-edge monotonicity: within a demand plateau, the selected basis left edge
  is sufficient to imply all represented windows.
- Closed-form demand equivalence: arithmetic release counting equals the
  existing enumerated window-demand definition.
- Schema-v3 checker soundness: accepted compact certificates imply
  `extracted_jittered_offset_window_dbf_ok_global`.
- Compatibility: schema-v2 soundness remains unchanged.

### V3 test plan

- Build the affected Rocq files, then run `make -j2`.
- Run Rust formatting and unit tests.
- Run schema-v2 and schema-v3 jittered checker tests.
- Run schema-v3 pipeline mutation tests.
- Run jittered benchmarks and verify schema v3 reduces witness size and
  extracted-Haskell check time versus schema v2.
- Run `git diff --check`.

### V3 risks for the Rust design

- Do not let Rust choose an unchecked subset of windows; the checker must
  recompute and validate the expected compact basis.
- Do not trust Rust-provided demand values unless the checker independently
  validates them.
- Do not remove schema-v2 support until schema-v3 benchmarks and mutation tests
  are stable.
- Do not raise `MAX_JITTERED_DBF_WINDOWS` as a substitute for compact
  certificates.
- Do not add timing or worker-count fields to canonical witness JSON.

### V3 progress

- V3 PR 1 started:
  - added `JitteredPeriodicCompactDBF.v` as a proof-facing compact DBF basis
    layer for jittered-periodic task sets
  - represented compact bases as right-endpoint rows with selected left edges
  - defined coverage by a later left edge with equal jittered window demand
  - proved that a DBF test over covered basis windows implies bounded jittered
    window DBF for every `t1 <= t2 <= H`
  - added an identity compact basis helper that covers all bounded windows and
    preserves the schema-v2 proof baseline
- V3 PR 2 started:
  - added a proof-facing fast jittered DBF layer for arithmetic release counts
  - kept the semantic checker boundary at the existing enumerated window DBF
    definition
- V3 PR 2 completed:
  - defined extraction-friendly arithmetic helpers for counting nominal releases
    in a jitter-adjusted window
  - proved the fast per-task and task-set DBF windows equal the existing
    enumerated jittered window DBF
  - added a fast compact-basis DBF test and proved its soundness through
    equivalence with the existing compact-basis DBF test
- V3 PR 3 started:
  - added `JitteredEDFCompactDbfCertificate` with cutoff, compact basis, and
    `all_basis_checked` fields
  - added field-equality helpers and a compact certificate field soundness
    lemma
  - exposed extraction-facing expected cutoff, expected compact basis, compact
    checker, and compact checker soundness theorem
  - the compact checker uses the fast compact-basis DBF test and derives the
    existing global jittered offset-window DBF property through the cutoff
    theorem
  - extended `scripts/jittered_edf_witness_check.hs` to keep schema v2 support
    unchanged and accept schema v3 `cert.dbf.basis` rows with
    `all_basis_checked`
  - added a schema-v3 expected-witness emit option for frontend-only checker
    tests, leaving Rust schema-v3 generation to V3 PR4
  - extended local make coverage for schema-v3 accept/reject checks without
    requiring Rust schema-v3 generation
