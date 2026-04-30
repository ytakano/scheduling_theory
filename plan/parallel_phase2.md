# Haskell Checker Parallelization Phase 2 Roadmap

This roadmap continues `parallel_report.md` and `row_block_checker.md`.
Phase 1 exposed a proof-backed NDBF block checker and a threaded Haskell
runner.  The Phase 1 measurement showed that this is not enough for the 10M
compact-basis stress case, because the checker still computes the full expected
compact basis before worker execution.

Phase 2 moves the parallel checker frontier earlier: expected compact-basis
generation, expected-vs-actual equality, and NDBF checking should become
row/range-local work items.

## 1. Phase 1 Finding

For the `cap_stress` task set:

```text
cost=1, period=169, deadline=169, offset=0, jitter=1
```

the schema-version 3 compact basis has:

```text
cutoff        = 57,630
basis rows    = 57,631
basis windows = 9,855,243
witness bytes = 30,556,592
```

The relevant measured checker results are:

| checker | threads | real s | user s | sys s | peak KiB | user/real |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| monolithic/default | 1 effective | 875.53 | 873.26 | 3.68 | 1,297,152 | 1.00 |
| block checker | 16 | 882.85 | 941.72 | 157.94 | 1,525,376 | 1.07 |
| block checker with phase metrics | 16 | 931.92 | 997.93 | 151.02 | 1,733,504 | 1.07 |

The phase-instrumented run attributed:

| phase | wall s | share of checker real |
| --- | ---: | ---: |
| expected compact-basis generation | 924.759710 | 99.23% |
| parallel NDBF workers | 0.485768 | 0.05% |

The next performance problem is therefore not worker scheduling.  It is the
serial call to:

```text
jittered_edf_compact_dbf_certificate_expected_basis
  -> jittered_reduced_compact_basis_upto
  -> jittered_reduced_left_edges_for_t2
  -> jittered_reduced_left_edge_b
```

## 2. Goal

Phase 2 should preserve the existing abstract claim:

```text
accepted schema-v3 compact DBF certificate
  => extracted_jittered_offset_window_dbf_ok_global ts
```

while changing the execution frontier from:

```text
compute full expected basis serially
split actual and expected bases
check full aggregation equality
run NDBF blocks in parallel
```

to:

```text
plan ordered row ranges
for each range:
  compute expected rows for the range
  compare actual rows for the same range
  check NDBF for the range
combine all range results under a range-coverage theorem
```

The witness format remains schema version 3.  The compact DBF certificate still
contains a cutoff, compact basis rows, and `all_basis_checked`.  Threading,
range size, metrics, and Haskell worker scheduling are tool-layer execution
choices, not certificate fields.

## 3. Terminology

- `compact basis row`: one `(t2, left_edges)` row of
  `JitteredCompactDbfBasis`.  The row groups compact DBF windows by right
  endpoint `t2`.
- `time range`: a half-open interval `[lo, hi)` over row right endpoints.
  Since `bounded_time_points H = seq 0 (S H)`, complete coverage for cutoff
  `H` is `[0, S H)`.
- `range cover`: an ordered, gap-free, non-overlapping list of time ranges
  whose concatenation covers `[0, S H)`.
- `checker frontier`: a Rocq-defined boolean exported to Haskell together with
  a Rocq soundness lemma.
- `runner`: the Haskell command-line checker that decodes CBOR, plans ranges,
  schedules workers, aggregates booleans, writes metrics, and rejects on any
  parse error, worker exception, or extracted `False`.
- `range-local expected equality`: the check that actual certificate rows for
  one range exactly equal the expected compact-basis rows generated for that
  range.

## 4. Refinement Boundary

The abstract interface is the decoded jittered task set plus the existing
schema-v3 compact DBF certificate obligation.  The new common-layer interface
should expose proof-backed row/range checker frontiers, but it should not expose
Haskell threads, worker IDs, memory layout, metrics, file paths, or CBOR parser
details.

The concrete projection is the adapter/tool runner's ordered list of ranges and
the corresponding contiguous slices of the decoded certificate basis.  Haskell
may choose ranges by row count, estimated basis-window count, or another local
policy, provided the extracted range-cover checker accepts the range list and
all range-local checker booleans are true.

Common layer obligations:

- define expected compact-basis generation for one row and for a half-open
  range;
- define and prove ordered, gap-free, non-overlapping range coverage for
  `[0, S H)`;
- prove that valid ranges reconstruct the same expected compact basis as
  `jittered_reduced_compact_basis_upto`;
- prove that per-range actual-vs-expected equality reconstructs the current
  full expected-basis equality;
- prove that per-range NDBF checks imply the current concatenated compact-basis
  NDBF obligation;
- prove a final extracted range checker soundness theorem with the same
  conclusion as the existing compact certificate checker.

Adapter/tool obligations:

- decode the same schema-v3 CBOR fields;
- validate schema, policy, domain, task hash, cutoff, and `all_basis_checked`
  before trusting the certificate;
- split certificate rows into contiguous actual ranges while preserving row
  order;
- pass every planned range to an extracted checker frontier;
- reject missing, duplicated, overlapping, reordered, empty, failed, or false
  ranges;
- avoid computing the full expected compact basis in the hot path.

Concrete runtime layer:

- unchanged.  Phase 2 adds no Awkernel scheduler hooks, timers, queues,
  interrupts, trace rows, runtime event sources, adapter-visible scheduling
  policy, or GEDF runtime API.

## 5. Common-Layer Interface Delta

Recommended Rocq-facing additions:

```coq
Definition TimeRange := Time * Time.
```

`TimeRange` is interpreted as `[lo, hi)`.

Expected basis helpers:

```coq
Definition jittered_reduced_compact_basis_row
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jitter : TaskId -> Time)
    (enumT : list TaskId)
    (t2 : Time) : Time * list Time := ...

Definition jittered_reduced_compact_basis_range
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jitter : TaskId -> Time)
    (enumT : list TaskId)
    (lo hi : Time) : JitteredCompactDbfBasis := ...

Definition jittered_edf_compact_dbf_certificate_expected_basis_range
    (ts : list ExtractedJitteredPeriodicTask)
    (lo hi : Time) : JitteredCompactDbfBasis := ...
```

Range coverage and checker frontiers:

```coq
Definition jittered_time_ranges_cover_upto_b
    (H : Time)
    (ranges : list TimeRange) : bool := ...

Definition check_jittered_edf_compact_dbf_certificate_range_extracted
    (ts : list ExtractedJitteredPeriodicTask)
    (lo hi : Time)
    (actual_range : JitteredCompactDbfBasis) : bool := ...

Definition check_jittered_edf_compact_dbf_certificate_ranges_extracted
    (ts : list ExtractedJitteredPeriodicTask)
    (ranges : list TimeRange)
    (actual_ranges : list JitteredCompactDbfBasis)
    (cert : JitteredEDFCompactDbfCertificate) : bool := ...
```

The final checker should validate:

```text
taskset well-formed
header fields match expected cutoff and all_basis_checked
ranges cover [0, S cutoff)
cert.basis = concat actual_ranges
for each range:
  actual_range = expected_range(ts, lo, hi)
  actual_range passes NDBF
```

This shape reconstructs the same compact-basis certificate obligation without
requiring one serial full expected-basis value in the Haskell runner.

Likely Rocq files:

- `JitteredPeriodicCompactDBF.v`: row/range expected-basis constructors and
  range concatenation lemmas near `jittered_reduced_left_edges_for_t2` and
  `jittered_reduced_compact_basis_upto`.
- `JitteredPeriodicEDFCertificate.v`: equality helpers and range coverage
  soundness if placed at the certificate level.
- `JitteredPeriodicEDFFinalCertificateChecker.v`: extraction-facing range
  checker frontiers and final soundness theorem.
- `JitteredPeriodicEDFExtraction.v`: export the new range frontiers while
  keeping the monolithic and current block entry points during transition.

## 6. Phase Breakdown

### P2-A: Specify Range Coverage

Define `TimeRange` and `jittered_time_ranges_cover_upto_b`.  The accepted range
list must be ordered, gap-free, non-overlapping, and cover `[0, S H)`.

Proof obligations:

- accepted coverage starts at `0`;
- every range has `lo < hi`;
- each next range starts at the previous `hi`;
- the final range ends at `S H`;
- coverage excludes duplicates, gaps, and reordering.

### P2-B: Add Expected-Range Generation

Factor expected-basis generation so each row can be generated independently by
`t2`, then lift that to a half-open range.

Proof obligations:

- one-row helper equals the row generated by the existing full-basis function;
- range helper equals the corresponding slice of
  `jittered_reduced_compact_basis_upto`;
- concatenating expected ranges under a valid range cover equals the current
  full expected compact basis.

### P2-C: Add Range-Local Checker Frontiers

Add extracted booleans for range-local expected equality and NDBF.  The range
checker should return only a boolean in the first implementation; diagnostics
remain adapter/tool output.

Proof obligations:

- `compact_dbf_basis_eqb actual expected = true` implies `actual = expected`;
- per-range equality plus valid coverage implies
  `cert.(jedf_compact_basis) = expected_full_basis`;
- per-range NDBF booleans imply NDBF over the concatenated certificate basis;
- the final range checker implies
  `extracted_jittered_offset_window_dbf_ok_global ts`.

### P2-D: Move Haskell To Range Work Items

Change `scripts/jittered_edf_witness_check.hs` so the hot path no longer binds:

```haskell
expectedBasis = EDF.jittered_edf_compact_dbf_certificate_expected_basis input
```

before worker scheduling.

The new runner should:

1. parse CSV and CBOR once;
2. validate metadata before spawning workers;
3. build the compact certificate once;
4. plan ordered ranges over certificate rows;
5. run the header/range-cover checker once;
6. run one extracted range checker per range in workers;
7. force each worker result to `Bool`;
8. aggregate deterministically and reject on the lowest failing range index.

Keep existing CLI compatibility:

```text
jittered_edf_witness_check --tasks TASKS.csv --witness WITNESS.cbor
  [--threads 1|N|auto]
  [--block-windows N]
  [--metrics-out PATH]
```

Use `--block-windows` as the first range planning knob.  Add `--range-rows N`
only if basis-window planning cannot express a stable range plan.  Keep
`--threads 1` as the compatibility default and use `--threads auto` explicitly
in benchmarks.

Implementation note:

- `check_jittered_edf_compact_dbf_certificate_ranges_extracted` is exported as
  proof/reference tooling for the aggregate range obligation.
- The normal Haskell checker path does not call the aggregate checker, because
  that would recompute every expected range serially.  Instead it validates the
  header, range cover, and certificate-basis concatenation once, then evaluates
  `check_jittered_edf_compact_dbf_certificate_range_extracted` for each planned
  range work item.
- Range planning, worker scheduling, metrics, and `--block-windows` are
  adapter/tool-layer execution choices.  They are not schema-v3 certificate
  fields, common-layer proof data, or Awkernel runtime semantics.

### P2-E: Metrics And Benchmarks

Preserve existing phase metrics and add range-specific metrics:

```text
phase_range_plan_s
phase_range_cover_s
phase_expected_ranges_s
phase_range_equality_s
phase_range_ndbf_s
range_count
range_rows_min
range_rows_max
range_windows_min
range_windows_max
failed_range_index
```

For accepted runs, `failed_range_index` should be omitted or set to `none`.
For rejected runs, report the lowest failing range index.

`actual_blocks`, `expected_rows`, `expected_windows`, `expected_blocks`,
`phase_expected_basis_generate_s`, `phase_actual_split_s`, and
`phase_expected_split_s` are compatibility fields from the Phase 1 block
checker metrics.  In the Phase 2 range checker, `actual_blocks` aliases
`range_count`, while the expected-basis compatibility fields are reported as
zero because the normal checker path intentionally does not build the full
expected compact basis before scheduling range workers.

`phase_expected_ranges_s` is emitted as a Phase 2 placeholder and currently
reports zero.  Expected range construction is performed inside the extracted
per-range checker work item, so the first implementation folds that cost into
`phase_range_ndbf_s` / `phase_workers_s`.  A later checker frontier may split
range-local expected-basis generation and NDBF into separate timed calls.

Benchmark after P2-D:

```text
threads:       1, 2, 4, auto
block_windows: 100000, 50000, 20000, 10000
case:          cap_stress
```

Record `real_s`, `user_s`, `sys_s`, `peak_kb`, `user/real`, range counts,
range window distribution, and result.

## 7. Non-Goals

- no schema-v3 CBOR change;
- no new witness certificate fields;
- no proof dependency on Haskell scheduling fairness;
- no Awkernel runtime hooks, trace rows, timers, queues, interrupts, or GEDF
  runtime APIs;
- no scheduler-tuning-first work before expected-basis generation is moved out
  of the serial pre-worker path;
- no diagnostic payloads in Rocq checker booleans during the first Phase 2
  implementation.

## 8. Testing Roadmap

Rocq tests and builds:

- range coverage checker compiles and proves ordered/gap-free/non-overlap
  soundness;
- expected-row and expected-range helpers compile;
- range concatenation reconstructs full expected basis under valid coverage;
- range equality and NDBF soundness lemmas compile;
- final range checker theorem concludes
  `extracted_jittered_offset_window_dbf_ok_global ts`;
- extraction exports old, block, and range checker entry points.

Haskell and pipeline tests:

- accepted fixture passes with `--threads 1`, `--threads 2`, and
  `--threads auto`;
- tiny witness passes with `--threads 2 --block-windows 1`;
- monolithic checker, serial range checker, and parallel range checker agree on
  accepted fixtures;
- mutated witnesses still reject in all modes:
  - hash mismatch;
  - bad cutoff;
  - extra basis row;
  - changed left edge;
  - `all_basis_checked = false`;
- missing, duplicated, overlapping, empty, and reordered ranges reject;
- invalid CLI rejects:
  - `--threads 0`;
  - `--threads nope`;
  - `--block-windows 0`;
- metrics output includes range fields.

Benchmark acceptance:

- `cap_stress` materially improves over the `875.53s` monolithic baseline and
  the `931.92s` phase-instrumented block run;
- `user / real` rises clearly above `1.07` under `--threads auto`;
- peak RSS remains bounded and is documented;
- schema-version 3 CBOR compatibility remains unchanged;
- monolithic and current block checkers remain available until serial range,
  parallel range, and mutated-witness tests agree.

## 9. Open Risks

The main proof risk is weakening coverage while replacing one full expected
basis with many range-local checks.

Specific risks:

- off-by-one coverage of `[0, S H)`;
- duplicated or overlapping ranges masking missing rows;
- row reordering that still passes a weak local equality check;
- accidentally retaining full expected-basis generation in the Haskell hot path;
- load imbalance because later `t2` rows may contain more left edges;
- laziness hiding range work unless worker booleans are forced;
- phase metrics double-counting work after the range split;
- confusing range/checker blocks with OS-level blocking or Awkernel runtime
  behavior.

Mitigations:

- make range coverage a common-layer checked obligation;
- prove concatenation of valid expected ranges equals the current full expected
  basis;
- require `cert.(jedf_compact_basis) = concat actual_ranges`;
- keep range order part of the checked representation;
- chunk by basis-window count before tuning row-count policies;
- keep monolithic and block checkers as transition fallbacks;
- record range distribution and peak RSS in every benchmark table.
