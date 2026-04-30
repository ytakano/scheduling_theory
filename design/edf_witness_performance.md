# EDF Witness Performance

This note records local performance data for jittered periodic EDF witnesses.
Runtime witness generation and checking now support only schema version 3.  The
older schema version 2 numbers below are a historical baseline from the
transition to compact bases; they are not a currently supported runtime mode.

Benchmark measurements are outside canonical witness JSON and are not part of
the trusted certificate interface.

Command:

```sh
make bench-jittered-edf-witness BENCH_OUT=/tmp/jittered_v3_only_bench.csv
```

Date: 2026-04-28.

## Benchmark Cases

- `small`: one zero-jitter task, `cost=1`, `period=2`, `deadline=2`,
  `offset=0`, `jitter=0`.
- `medium`: two tasks; the `small` task plus `cost=1`, `period=3`,
  `deadline=3`, `offset=0`, `jitter=1`.
- `large`: one release-jitter high-cutoff workload case, `cost=1`,
  `period=8`, `deadline=8`, `offset=0`, `jitter=1`.
- `limit_near`: one larger-period release-jitter task, `cost=1`,
  `period=16`, `deadline=16`, `offset=0`, `jitter=1`. This case preserves the
  historical stress point while the current benchmark exercises only the
  schema-v3 path.

## Current V3-Only Output

The current benchmark script emits:

| column | meaning |
| --- | --- |
| `case` | synthetic workload name |
| `engine` | `rust-generator` or `haskell-witness-check` |
| `thread_mode` | requested generator thread mode; witness-check rows use `auto` for the generated witness they check |
| `task_count` | number of CSV tasks for witness rows |
| `schema_version` | `3` for witness-generation and witness-check rows |
| `cutoff` | checker-facing DBF cutoff for witness rows |
| `basis_window_count` | compact basis window count for schema-v3 witnesses |
| `witness_bytes` | serialized witness size for witness rows |
| `wall_ms` | local wall-clock runtime |
| `peak_kb` | currently unavailable |
| `status` | `ok`, `failed`, or `skipped` |

Representative v3-only rows from the optimized compact-basis benchmark:

| case | schema | cutoff | basis windows | witness bytes | Rust auto gen ms | Haskell witness check ms | status |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| small | 3 | 14 | 64 | 2,687 | 4 | 4 | ok |
| medium | 3 | 70 | 1,715 | 33,063 | 5 | 22 | ok |
| large | 3 | 153 | 1,560 | 37,470 | 5 | 45 | ok |
| limit_near | 3 | 561 | 10,152 | 213,293 | 11 | 1,628 | ok |

## Stage 2 N Kernel Result

After the schema-v3 compact-basis optimization, the checker gained
checker-local `N` kernels for the DBF arithmetic that dominates periodic and
jittered-periodic EDF witness checking.  These kernels are an implementation
result, not a new witness schema and not a new common time domain.

Implemented kernels:

- `TaskModels/Periodic/PeriodicNDBF.v` adds `N`-valued scalar DBF, window DBF,
  taskset DBF, and bounded cutoff tests.
- `TaskModels/Jitter/JitteredPeriodicNDBF.v` adds `N`-valued jittered fast
  window DBF, taskset demand, capacity, and bounded window tests.
- The periodic and jittered extraction decisions route the checker-facing DBF
  tests through these `N` kernels while preserving the existing public
  extracted entry points.
- The compact jittered final-certificate checker uses the `N` fast compact
  basis predicate for its DBF check.

Proof status:

- Periodic lemmas show that every `N` DBF result projects back to the existing
  `nat` DBF/window DBF definitions by `N.to_nat`.
- `n_dbf_test_by_cutoff_eq` and `n_window_dbf_test_by_cutoff_eq` connect the
  periodic checker booleans back to the previous `nat` cutoff tests.
- `jittered_window_fast_ndbf_test_upto_eq_nat` connects the jittered `N`
  window checker back to the existing `nat` jittered window DBF test.
- These lemmas keep the proof-facing semantics over `nat`; `N` is only the
  executable arithmetic representation used inside the checker kernel.

Verification performed for the implementation included compiling the new
periodic and jittered `N` modules, their extraction-decision modules, and the
corresponding extraction soundness wrappers.

### Measured Stage 2 N Kernel Output

Measured with the same schema-v3 benchmark cases and CSV columns described
above. These rows exercise the extracted Haskell checker after the
checker-local `N` DBF kernels; they do not change the witness schema, the
common `nat` interface, or the runtime trace surface.

Date: 2026-04-30.

Command sequence:

```sh
cargo build -p sched-witness-gen
stack exec -- ghc -O2 -package aeson -package crypton \
  -iextracted/haskell -outputdir scripts/.build \
  -o scripts/jittered_edf_witness_check scripts/jittered_edf_witness_check.hs
./scripts/bench_jittered_edf_witness_pipeline /tmp/jittered_n_kernel_bench.csv
```

This direct sequence avoids re-running extraction while measuring the current
generated Haskell checker. The equivalent make target is
`make bench-jittered-edf-witness BENCH_OUT=/tmp/jittered_n_kernel_bench.csv`,
but that target may rebuild extraction artifacts when they are stale.

| case | schema | cutoff | basis windows | witness bytes | Rust auto gen ms | Stage 2 Haskell witness check ms | status |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| small | 3 | 14 | 64 | 2,656 | 4 | 4 | ok |
| medium | 3 | 70 | 1,715 | 33,032 | 5 | 11 | ok |
| large | 3 | 153 | 1,560 | 37,439 | 5 | 14 | ok |
| limit_near | 3 | 561 | 10,152 | 213,262 | 9 | 93 | ok |

There is no concrete Awkernel runtime impact.  Stage 2 adds no scheduler hooks,
interrupt hooks, queue state, trace rows, or adapter-visible scheduler
policies.  The Rust witness generator and Haskell witness wrapper keep the same
schema-v3 artifact boundary; only the extracted checker implementation behind
the stable entry points changes.

## Operational Generator Guard

The Rust schema-v3 generator caps compact basis windows with
`MAX_JITTERED_DBF_BASIS_WINDOWS = 2,000,000`. This is an operational generator
guard for local resource use, not a proof or theory limit. The value is chosen
under the user's stated tolerance for witnesses in the hundreds of MB and for
multi-hour local runs. The checker and Rocq proof story remain parameterized by
the compact basis certificate obligations, not by this Rust-side cap.

## Historical V2 Baseline

These rows record the pre-v3 full-window baseline used to justify compact
basis certificates.  They are kept only as historical comparison data.

| case | schema | cutoff | full windows | witness bytes | Rust auto gen ms | Haskell witness check ms | status |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| small | 2 | 14 | 260 | 12,721 | 5 | 8 | ok |
| medium | 2 | 70 | 8,454 | 404,138 | 11 | 1,434 | ok |
| large | 2 | 153 | 15,070 | 732,647 | 17 | 6,207 | ok |
| limit_near | 2 | 561 | 178,538 | 8,858,096 | 140 | skipped | too heavy |

## Observations

- Against the historical full-window baseline, schema v3 reduces certificate
  windows by 75.4% on `small`, 79.7% on
  `medium`, 89.6% on `large`, and 94.3% on `limit_near`.
- Witness JSON size falls by 78.9% on `small`, 91.8% on `medium`, 94.9% on
  `large`, and 97.6% on `limit_near`.
- Extracted-Haskell witness checking improves from 1,434 ms to 22 ms on
  `medium`, and from 6,207 ms to 45 ms on `large`.
- With the Stage 2 `N` checker kernel, the same schema-v3 Haskell witness
  check improves further from 22 ms to 11 ms on `medium`, from 45 ms to 14 ms
  on `large`, and from 1,628 ms to 93 ms on `limit_near`.
- Optimized schema-v3 Rust generation uses the same closed-form release count
  as the checker-facing fast DBF path and reuses adjacent demand values while
  scanning each right endpoint row.
- On `limit_near`, schema-v3 Rust generation dropped from the earlier
  reduced-basis baseline of 5,144 ms to 11 ms.
- The historical schema-v2 `limit_near` witness-check run was skipped because
  it did not complete in a practical local benchmark window; schema v3
  completed in
  1,636 ms.

## Trust Boundary

Rust remains untrusted. The checker recomputes the expected reduced compact
basis and compares it against the witness before running the fast compact DBF
test. Rust-provided demand values are still not serialized or trusted.

The Stage 2 `N` kernels do not change that boundary.  The common layer remains
`nat`-based, adapters remain responsible for rejecting negative external
numeric inputs before extraction maps checker naturals to Haskell `Integer`,
and runtime trace emission is unchanged.  The only trusted change is the Rocq
proof bridge showing that the checker-local `N` booleans coincide with the
existing `nat` DBF obligations.
