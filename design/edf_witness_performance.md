# EDF Witness Performance

This note records the local performance comparison for jittered periodic EDF
witnesses after replacing schema-v3 identity bases with reduced compact bases.
The measurements are outside canonical witness JSON and are not part of the
trusted certificate interface.

Command:

```sh
make bench-jittered-edf-witness BENCH_OUT=/tmp/jittered_reduced_basis_bench.csv
```

Date: 2026-04-28.

## Benchmark Cases

- `small`: one zero-jitter task, `cost=1`, `period=2`, `deadline=2`,
  `offset=0`, `jitter=0`.
- `medium`: two tasks; the `small` task plus `cost=1`, `period=3`,
  `deadline=3`, `offset=0`, `jitter=1`.
- `large`: one release-jitter task, `cost=1`, `period=8`, `deadline=8`,
  `offset=0`, `jitter=1`.
- `limit_near`: one larger-period release-jitter task, `cost=1`,
  `period=16`, `deadline=16`, `offset=0`, `jitter=1`. This case is intended
  to stress the old schema-v2 full-window path near the current benchmark
  limit.

## Jittered EDF Schema Comparison

| case | schema | cutoff | windows checked | basis windows | witness bytes | Rust auto gen ms | Haskell witness check ms | status |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| small | 2 | 14 | 260 | 0 | 12,721 | 5 | 8 | ok |
| small | 3 | 14 | 0 | 64 | 2,687 | 5 | 4 | ok |
| medium | 2 | 70 | 8,454 | 0 | 404,138 | 17 | 1,437 | ok |
| medium | 3 | 70 | 0 | 1,715 | 33,063 | 29 | 23 | ok |
| large | 2 | 153 | 15,070 | 0 | 732,647 | 27 | 5,897 | ok |
| large | 3 | 153 | 0 | 1,560 | 37,470 | 114 | 46 | ok |
| limit_near | 2 | 561 | 178,538 | 0 | 8,858,096 | 552 | skipped | too heavy |
| limit_near | 3 | 561 | 0 | 10,152 | 213,293 | 5,144 | 1,636 | ok |

## Observations

- Schema v3 reduces certificate windows by 75.4% on `small`, 79.7% on
  `medium`, 89.6% on `large`, and 94.3% on `limit_near`.
- Witness JSON size falls by 78.9% on `small`, 91.8% on `medium`, 94.9% on
  `large`, and 97.6% on `limit_near`.
- Extracted-Haskell witness checking improves from 1,437 ms to 23 ms on
  `medium`, and from 5,897 ms to 46 ms on `large`.
- Schema-v3 Rust generation is slower for larger cases because the generator
  currently computes adjacent demand values while constructing the reduced
  basis. This remains outside the trusted boundary, but it is the next obvious
  generator-side optimization target.
- The schema-v2 `limit_near` witness-check run was skipped because it did not
  complete in a practical local benchmark window; schema v3 completed in
  1,636 ms.

## Trust Boundary

Rust remains untrusted. The checker recomputes the expected reduced compact
basis and compares it against the witness before running the fast compact DBF
test. Rust-provided demand values are still not serialized or trusted.
