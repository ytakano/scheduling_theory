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
