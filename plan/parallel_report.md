# Haskell Checker Parallelization Report

This report analyzes the current Haskell checker hotspot for schema-version 3
jittered periodic EDF witnesses and identifies where further parallelization is
likely to pay off.

The conclusion is that the current threaded runner exposes parallel work only
after a large serial structural phase.  For the 10M compact-basis stress case,
that serial phase dominates enough that the threaded block checker does not
improve wall-clock time.

## Current Measurement

The current measurement baseline is recorded in
`design/edf_witness_performance.md`.

For the `cap_stress` task set:

```text
cost=1, period=169, deadline=169, offset=0, jitter=1
```

the compact basis contains:

```text
cutoff        = 57,630
basis windows = 9,855,243
witness bytes = 30,556,592
```

The old/default checker result was:

| checker | threads | real s | user s | sys s | peak KiB |
| --- | ---: | ---: | ---: | ---: | ---: |
| monolithic/default | 1 effective | 875.53 | 873.26 | 3.68 | 1,297,152 |

The current block checker result was:

| checker | threads | block windows | actual blocks | expected blocks | real s | user s | sys s | peak KiB |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| block checker | 16 | 100,000 | 99 | 99 | 882.85 | 941.72 | 157.94 | 1,525,376 |

The `user / real` ratio is approximately `1.07`.  This indicates that some
parallel work happened, but most elapsed time remained effectively serial.

## Current Checker Shape

The Haskell runner performs these steps in `scripts/jittered_edf_witness_check.hs`:

```text
parse CSV
parse CBOR
validate schema/policy/domain/task hash
build compact DBF certificate
compute expected compact basis
split actual basis into blocks
split expected basis into blocks
run extracted header check
run extracted block aggregation equality
run per-block NDBF workers
aggregate worker booleans
```

The relevant implementation points are:

- `runParallelBlockCheck`
- `jittered_edf_compact_dbf_certificate_expected_basis`
- `splitBasisByWindows`
- `check_jittered_edf_compact_dbf_certificate_block_basis_for_expected`
- `jittered_fast_compact_basis_ndbf_block_test`
- `parallelAll`

The current worker phase is only the per-block NDBF part:

```text
actual block -> jittered_fast_compact_basis_ndbf_block_test
```

Before worker execution, the runner has already built the entire expected
compact basis and checked full concatenated basis equality.

## Hotspots

### Expected Basis Generation

The likely dominant hotspot is:

```text
jittered_edf_compact_dbf_certificate_expected_basis
  -> jittered_reduced_compact_basis_upto
  -> jittered_reduced_left_edges_for_t2
  -> jittered_reduced_left_edge_b
```

This recomputes the expected compact basis from the task set.  For `cap_stress`,
it produces 57,631 rows and 9,855,243 basis windows.  The computation happens
before the parallel block worker phase.

This work is naturally row-parallel by right endpoint `t2`, because each row:

```text
(t2, reduced left edges for t2)
```

depends on the task set and `t2`, but not on neighboring rows.

### Block Aggregation Equality

The current extracted aggregation check validates:

```text
expected_basis = concat expected_blocks
cert.basis     = concat actual_blocks
concat actual_blocks = concat expected_blocks
```

This is proof-facing safe because it preserves complete flat-basis equality and
row order.  However, it is still a large serial traversal over the full basis
after the expected basis has already been generated.

The check is safe but not yet performance-optimal.

### Per-Block NDBF Workers

The current parallelized work is:

```text
jittered_fast_compact_basis_ndbf_block_test
```

This is a valid proof-backed frontier, but for `cap_stress` it is not the
dominant phase.  The measured block checker still runs about as long as the old
default checker.

### Haskell Runner Overhead

The current runner also pays tool-layer costs:

- converting extracted lists with `fromEDFList` and `toEDFList`;
- splitting rows by basis-window count;
- counting rows and windows for metrics;
- scheduling worker chunks with `forkIO` and `MVar`;
- forcing only final `Bool` results.

These are adapter/tool implementation details.  They are not part of the common
certificate interface.

## Parallelization Opportunities

### Opportunity 1: Phase Metrics

Before changing proof interfaces again, add phase timing in the Haskell runner.
The report should distinguish:

```text
CSV parse
CBOR parse
certificate construction
expected basis generation
actual basis splitting
expected basis splitting
block aggregation equality
parallel NDBF worker phase
metrics output
```

This can confirm whether expected basis generation or equality checking is the
dominant serial phase.

### Opportunity 2: Expected-Basis Row Frontier

Move expected-basis generation behind a row or range checker frontier.

Instead of computing the full expected basis serially, Rocq should expose a
checker for a bounded row range:

```text
expected compact basis rows for t2 in [lo, hi)
```

The Haskell runner can then dispatch independent work items:

```text
range -> expected rows for range -> actual rows for range -> row equality -> NDBF
```

The common proof obligation is that the ranges form an ordered, gap-free,
non-overlapping cover of `[0, S cutoff)`, matching the existing
`bounded_time_points cutoff = seq 0 (S cutoff)` row domain.

### Opportunity 3: Per-Range Equality

Replace full-basis concatenated equality in the hot path with per-range
equality plus a range-coverage proof.

The current complete equality proof is safe:

```text
cert.basis = concat actual_blocks
concat actual_blocks = concat expected_blocks
expected_basis = concat expected_blocks
```

The next proof-facing shape should preserve that guarantee without requiring
one serial full-basis traversal.  A safe alternative is:

```text
range cover is ordered and complete
each range validates actual rows = expected rows for that range
each range validates NDBF for its actual rows
```

Then the common theorem can reconstruct the same full compact-basis obligation.

### Opportunity 4: Worker Granularity Sweep

After the serial phase is reduced, tune block size.  The current `cap_stress`
run used:

```text
--threads auto
--block-windows 100000
actual blocks = 99
```

That provides more blocks than capabilities, but the measured user/real ratio
shows worker work was not dominant.  A useful sweep after phase splitting is:

```text
threads:       1, 2, 4, auto
block_windows: 100000, 50000, 20000, 10000
```

Record `real_s`, `user_s`, `sys_s`, `peak_kb`, `actual_blocks`,
`expected_blocks`, and `result`.

## Recommended Next Implementation

The next implementation should not start by changing the worker scheduler.
The scheduler is not the limiting factor in the current measurement.

Recommended order:

1. Add Haskell phase metrics without changing acceptance semantics.
2. Measure `cap_stress` again and confirm the dominant serial phase.
3. Add Rocq row/range frontiers for expected compact basis generation.
4. Prove ordered range cover implies the same full expected-basis obligation.
5. Move Haskell work items to range-local expected generation, equality, and
   NDBF checking.
6. Keep the existing full checker as a transition fallback until serial,
   decomposed serial, and decomposed parallel results agree on fixtures.

## Refinement Boundary

The common layer should remain responsible for:

- row/range checker definitions;
- range coverage and ordering obligations;
- soundness lemmas connecting range-local checks to the existing compact DBF
  certificate obligation;
- preserving proof-facing natural-number DBF semantics, with `N` kernels hidden
  behind equivalence lemmas.

The adapter/tool layer should remain responsible for:

- CBOR decoding;
- choosing thread count;
- choosing range or block size;
- scheduling workers;
- producing metrics;
- rejecting on parse errors, worker failures, or any extracted `False`.

The concrete runtime layer is unaffected.  This report does not require
Awkernel scheduler hooks, timers, queues, interrupts, trace rows, or runtime
event changes.

## Acceptance Criteria For Future Work

Future parallelization should be considered successful only if:

- `cap_stress` shows clear wall-clock improvement over the 875 second baseline;
- `user / real` increases substantially when `--threads auto` is used;
- memory growth remains bounded and documented;
- reordered, missing, or duplicated ranges reject;
- serial and parallel decomposed checkers agree on accepted and mutated
  witnesses;
- no CBOR schema change is required unless explicitly designed as a separate
  witness-format revision.

## Follow-up Measurement: 2026-04-30 cap_stress Phase Run

### Goal

This run measures the phase breakdown behind the current Haskell block checker.
It preserves the existing schema-version 3 compact DBF certificate interface and
changes no common-layer proof obligation.  The only implementation change for
this run is adapter/tool-layer phase timing in the extracted Haskell checker's
existing `--metrics-out` file.

### Measurement Conditions

| field | value |
| --- | --- |
| Date | 2026-04-30T16:28:36Z |
| Source snapshot | `scheduling_theory` at `a666bd4`, with local changes to `scripts/jittered_edf_witness_check.hs`, `plan/parallel_report.md`, and `plan/parallel_phase2.md`; unrelated untracked `scripts/test.csv` present |
| OS / kernel | Linux 6.8.0-110-generic x86_64 |
| CPU | AMD Ryzen 9 5900HX with Radeon Graphics |
| CPU topology | 1 socket, 8 cores, 16 threads |
| Memory | 62 GiB RAM, 2.0 GiB swap |
| Rust | `rustc 1.93.0-nightly`, `cargo 1.93.0-nightly` |
| Haskell | Stack 3.7.1, GHC 9.10.3 |
| Time command | GNU `/usr/bin/time -f '%e,%U,%S,%M'` |
| Witness encoding | CBOR |
| Schema version | `3` |
| Task set | `cost=1, period=169, deadline=169, offset=0, jitter=1` |
| Witness cap | `10,000,000` |
| Checker flags | `--threads auto --block-windows 100000 --metrics-out /tmp/jittered_parallel_phase_bench/check_auto.metrics` |
| Resolved checker capabilities | `16` |
| Benchmark directory | `/tmp/jittered_parallel_phase_bench` |

Build and measurement commands:

```sh
make build-jittered-edf-witness-check
cargo build --release -p sched-witness-gen

/usr/bin/time -f '%e,%U,%S,%M' \
  -o /tmp/jittered_parallel_phase_bench/generate.time \
  ./target/release/sched-witness-gen jittered-periodic-edf \
    --tasks /tmp/jittered_parallel_phase_bench/cap_stress.csv \
    --out /tmp/jittered_parallel_phase_bench/cap_stress.cbor \
    --threads auto \
    --basis-window-cap 10000000 \
    --metrics-out /tmp/jittered_parallel_phase_bench/generate.metrics

/usr/bin/time -f '%e,%U,%S,%M' \
  -o /tmp/jittered_parallel_phase_bench/check_auto.time \
  ./scripts/jittered_edf_witness_check \
    --tasks /tmp/jittered_parallel_phase_bench/cap_stress.csv \
    --witness /tmp/jittered_parallel_phase_bench/cap_stress.cbor \
    --threads auto \
    --block-windows 100000 \
    --metrics-out /tmp/jittered_parallel_phase_bench/check_auto.metrics
```

The phase metrics explicitly force basis row/window counts so that lazy
evaluation does not hide expected-basis construction inside a later phase.

### Witness Context

| cutoff | basis rows | basis windows | witness bytes |
| ---: | ---: | ---: | ---: |
| 57,630 | 57,631 | 9,855,243 | 30,556,592 |

Rust generator result:

| threads | cap | real s | user s | sys s | peak KiB | status |
| ---: | ---: | ---: | ---: | ---: | ---: | --- |
| auto | 10,000,000 | 1.79 | 24.88 | 0.21 | 123,904 | ok |

### Checker Result

| checker | threads | block windows | actual blocks | expected blocks | real s | user s | sys s | peak KiB | user/real | status |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| block checker with phase metrics | 16 | 100,000 | 99 | 99 | 931.92 | 997.93 | 151.02 | 1,733,504 | 1.07 | accept |

### Phase Timing

The share column uses the external checker wall-clock time, `931.92s`, as the
denominator.

| phase | wall s | share of checker real | rows/windows touched | layer |
| --- | ---: | ---: | --- | --- |
| CSV read | 0.000160 | 0.00% | one task row | adapter/tool |
| CSV parse | 0.000085 | 0.00% | one task row | adapter/tool |
| CBOR decode | 0.000029 | 0.00% | CBOR term stream entry point | adapter/tool |
| witness decode | 1.452973 | 0.16% | 57,631 basis rows / 9,855,243 windows | adapter/tool |
| metadata validation | 0.000053 | 0.00% | policy, domain, task hash | adapter/tool |
| DBF certificate construction | 1.099302 | 0.12% | certificate wrapper and lazy basis fields | adapter/tool |
| resolve threads | 0.000003 | 0.00% | `auto -> 16` | adapter/tool |
| actual basis count | 0.512813 | 0.06% | 57,631 rows / 9,855,243 windows | adapter/tool forcing of certificate basis |
| expected basis generation | 924.759710 | 99.23% | 57,631 rows / 9,855,243 windows | common checker evaluation via extracted code |
| actual basis split | 0.351708 | 0.04% | 99 blocks | adapter/tool |
| expected basis split | 0.315592 | 0.03% | 99 blocks | adapter/tool |
| structural/header/block-basis equality | 0.862487 | 0.09% | full expected and actual block aggregation | proof-backed checker frontier |
| parallel NDBF workers | 0.485768 | 0.05% | 99 actual blocks | proof-backed checker frontier evaluated by adapter/tool |
| checker core total | 927.304457 | 99.50% | post-decode checker work | adapter/tool measurement envelope |

### Interpretation

This run confirms the hotspot hypothesis more strongly than the previous
`user / real` ratio alone.  The current threaded checker exposes parallel work
only after the full expected compact basis has already been generated.  For the
10M `cap_stress` case, expected-basis generation alone accounts for about
`99.23%` of external checker wall-clock time, while the parallel NDBF worker
phase accounts for about `0.05%`.

The next performance-relevant change should therefore not tune worker
scheduling first.  The next proof-facing frontier should decompose expected
basis generation by ordered row or row-range blocks, then combine range-local
expected-row equality and NDBF checks under a coverage theorem that reconstructs
the existing full compact-basis obligation.

The higher wall-clock and peak RSS relative to the previous block-checker run
should be read as a measurement-run effect: this checker build forces basis
counts at named phase boundaries so that lazy expected-basis work is attributed
to the expected-basis phase instead of being hidden inside a later traversal.

### Refinement Boundary

Common layer: unchanged schema-version 3 compact DBF certificate obligation,
proof-facing natural-number DBF semantics, and soundness of the extracted
checker frontiers.

Adapter/tool layer: CBOR decoding, witness paths, block sizing, thread count,
GHC capabilities, phase metrics, worker scheduling, and rejection on parse
errors, worker failures, or extracted `False`.

Concrete runtime layer: no Awkernel scheduler hooks, timers, queues,
interrupts, trace rows, runtime event sources, or adapter-visible scheduling
behavior are introduced by this measurement.
