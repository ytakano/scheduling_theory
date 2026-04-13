# Copilot Instructions

## Project Overview

This project formalizes scheduling theory in Rocq. The current codebase already
contains:

- a reusable single-CPU scheduler/alignment core
- generic canonicalization / normalization / finite-optimality infrastructure
- EDF / LLF / FIFO / RR policy files
- multicore-common definitions
- partitioned multicore composition and policy lifts
- an initial global EDF theorem layer

Primary planning documents:

- Proof roadmap: `plan/what_to_prove.md`
- Development roadmap: `plan/roadmap.md`

Supporting directories:

- `progress/` — proof planning / progress notes
- `plan/` — higher-level roadmap and theorem inventory
- `docker/` — container helpers

## Build

```bash
make
make clean
```

Compile a single file with the project mapping:

```bash
rocq compile -R theories SchedulingTheory theories/Foundation/Base.v
rocq compile -R theories SchedulingTheory theories/Semantics/Schedule.v
rocq compile -R theories SchedulingTheory theories/Abstractions/SchedulingAlgorithm/SchedulerBridge.v
rocq compile -R theories SchedulingTheory theories/Abstractions/SchedulingAlgorithm/TopMSchedulerBridge.v
rocq compile -R theories SchedulingTheory theories/Multicore/Global/GlobalEDF.v
rocq compile -R theories SchedulingTheory theories/Multicore/Partitioned/Partitioned.v
```

Compilation is the test mechanism in this repository.

## Module Architecture

Follow the dependency flow when adding definitions or lemmas:

```text
Foundation/Base.v
  -> Semantics/Schedule.v
  -> Abstractions/Scheduler/Interface.v
  -> Abstractions/SchedulingAlgorithm/Interface.v
  -> Abstractions/SchedulingAlgorithm/SchedulerBridge.v
  -> Abstractions/SchedulingAlgorithm/TopMInterface.v
  -> Abstractions/SchedulingAlgorithm/TopMSchedulerBridge.v
  -> Uniprocessor/Policies/*.v
  -> Multicore/Partitioned/*.v
  -> Multicore/Global/*.v
```

Useful current anchors:

- `theories/Abstractions/SchedulingAlgorithm/SchedulerBridge.v`
  - single-CPU bridge
  - `CandidateSourceSpec`
  - subset-aware `schedulable_by_on` helpers
- `theories/Abstractions/SchedulingAlgorithm/TopMSchedulerBridge.v`
  - generic top-`m` bridge for global-style policies
- `theories/Multicore/Partitioned/Policies/PartitionedPolicyLift.v`
  - common wrapper pattern for partitioned policies
- `theories/Multicore/Partitioned/Policies/PartitionedFiniteOptimalityLift.v`
  - reusable finite-job lifting result for partitioned EDF
- `theories/Multicore/Global/GlobalEDF.v`
  - initial global policy theorem layer

## Proof Workflow

Before changing proofs, inspect the current theory files first and treat them as
the source of truth. Use `progress/` for proof notes when the argument is large
enough to benefit from decomposition, but do not assume every theorem already
has a corresponding progress file.

Verify proof changes by compiling the edited file and any impacted dependents.
For cross-cutting changes, run `make`.

## Key Conventions

### `eligible` vs `ready`

- `eligible` means released and not completed.
- `ready` means eligible and not currently running.
- `valid_schedule` is stated using `eligible`, not `ready`.

### Constructive vs classical

- Keep constructive results in the main theory/policy files.
- Put classical lemmas in `Abstractions/SchedulingAlgorithm/ClassicalLemmas.v`
  or similarly named classical files.

### Current project status

- Single-CPU infrastructure is largely mature.
- Partitioned multicore is already substantial and not just a thin wrapper layer.
- Global scheduling has started: `GlobalEDF.v` is present and should be treated
  as the initial theorem layer for future global policies such as LLF.

## External Libraries

`rocq-stdpp` 1.13.0 is installed and available. Prefer it when it materially
improves proofs for decidability, finite maps, sets, or list reasoning.
