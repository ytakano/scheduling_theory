# EDF Witness Performance

This note records the local performance comparison for jittered periodic EDF
witnesses after replacing schema-v3 identity bases with reduced compact bases
and optimizing Rust-side reduced-basis generation.  The measurements are
outside canonical witness JSON and are not part of the trusted certificate
interface.

Command:

```sh
make bench-jittered-edf-witness BENCH_OUT=/tmp/jittered_optimized_basis_bench.csv
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
  `period=16`, `deadline=16`, `offset=0`, `jitter=1`. This case is intended
  to stress the old schema-v2 full-window path near the current benchmark
  limit.

## Jittered EDF Schema Comparison

| case | schema | cutoff | windows checked | basis windows | witness bytes | Rust auto gen ms | Haskell witness check ms | status |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| small | 2 | 14 | 260 | 0 | 12,721 | 5 | 8 | ok |
| small | 3 | 14 | 0 | 64 | 2,687 | 4 | 4 | ok |
| medium | 2 | 70 | 8,454 | 0 | 404,138 | 11 | 1,434 | ok |
| medium | 3 | 70 | 0 | 1,715 | 33,063 | 5 | 22 | ok |
| large | 2 | 153 | 15,070 | 0 | 732,647 | 17 | 6,207 | ok |
| large | 3 | 153 | 0 | 1,560 | 37,470 | 5 | 45 | ok |
| limit_near | 2 | 561 | 178,538 | 0 | 8,858,096 | 140 | skipped | too heavy |
| limit_near | 3 | 561 | 0 | 10,152 | 213,293 | 11 | 1,628 | ok |

## Observations

- Schema v3 reduces certificate windows by 75.4% on `small`, 79.7% on
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
- The schema-v2 `limit_near` witness-check run was skipped because it did not
  complete in a practical local benchmark window; schema v3 completed in
  1,636 ms.

## Trust Boundary

Rust remains untrusted. The checker recomputes the expected reduced compact
basis and compares it against the witness before running the fast compact DBF
test. Rust-provided demand values are still not serialized or trusted.
