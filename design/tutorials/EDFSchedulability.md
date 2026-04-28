# Verifying EDF Schedulability for Concrete Task Sets

This tutorial shows how to verify schedulability for concrete CSV task sets
using the supported runtime path:

1. build the Rust witness generator in release mode;
2. generate a JSON witness from the CSV task set;
3. check that witness with the extracted Haskell checker.

The Rust generator is not trusted.  A task set is accepted only when the
extracted checker prints `ACCEPT`.

Run all commands from the repository root:

```sh
cd /awkernel_refinement/scheduling_theory
```

## Build the Tools

Build the Rust generator with optimizations enabled:

```sh
cargo build --release -p sched-witness-gen
```

Build the extracted Haskell witness checkers:

```sh
make build-periodic-edf-witness-check
make build-jittered-edf-witness-check
```

The commands below use `./target/release/sched-witness-gen`.  Do not replace it
with the debug binary for large task sets.

## Periodic EDF Without Offsets

Create a periodic EDF task set:

```sh
cat > /tmp/periodic.csv <<'CSV'
cost,period,deadline
1,4,4
CSV
```

Generate a witness:

```sh
./target/release/sched-witness-gen periodic-edf \
  --tasks /tmp/periodic.csv \
  --out /tmp/periodic-witness.json \
  --threads auto
```

Check the witness:

```sh
./scripts/periodic_edf_witness_check \
  --tasks /tmp/periodic.csv \
  --witness /tmp/periodic-witness.json
```

Expected result:

```text
ACCEPT
```

## Periodic EDF With Offsets

Use the four-column CSV form when tasks have release offsets:

```sh
cat > /tmp/periodic-offset.csv <<'CSV'
cost,period,deadline,offset
1,4,4,1
CSV
```

Generate a witness:

```sh
./target/release/sched-witness-gen periodic-edf \
  --tasks /tmp/periodic-offset.csv \
  --out /tmp/periodic-offset-witness.json \
  --threads auto
```

Check the witness with `--offsets`:

```sh
./scripts/periodic_edf_witness_check \
  --tasks /tmp/periodic-offset.csv \
  --offsets \
  --witness /tmp/periodic-offset-witness.json
```

Expected result:

```text
ACCEPT
```

## Jittered Periodic EDF

Use the five-column CSV form for release jitter:

```sh
cat > /tmp/jittered.csv <<'CSV'
cost,period,deadline,offset,jitter
1,2,2,0,1
CSV
```

Generate a jittered EDF witness:

```sh
./target/release/sched-witness-gen jittered-periodic-edf \
  --tasks /tmp/jittered.csv \
  --out /tmp/jittered-witness.json \
  --threads auto
```

Check the witness:

```sh
./scripts/jittered_edf_witness_check \
  --tasks /tmp/jittered.csv \
  --witness /tmp/jittered-witness.json
```

Expected result:

```text
ACCEPT
```

## Thread Control

`--threads auto` lets the generator choose a practical parallelism level.  For
reproducible fixed parallelism, pass a positive integer:

```sh
./target/release/sched-witness-gen jittered-periodic-edf \
  --tasks /tmp/jittered.csv \
  --out /tmp/jittered-witness.threads2.json \
  --threads 2
```

The checker command is unchanged.

## Interpreting Failures

If witness generation fails, no checker-accepted certificate was produced.
For example, malformed CSV input or a task set outside the generator's
operational resource limits can stop generation.

If the checker prints `REJECT`, the witness is not accepted for that CSV task
set.  Regenerate the witness after every CSV edit; the checker validates that
the witness task hash matches the input CSV.

Only `ACCEPT` from the extracted Haskell checker should be treated as validated
schedulability.
