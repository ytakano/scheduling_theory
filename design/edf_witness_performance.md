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
| `engine` | `rust-generator`, `haskell-witness-check`, or `haskell-cutoff` |
| `thread_mode` | requested generator thread mode, or `na` for cutoff checks |
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
