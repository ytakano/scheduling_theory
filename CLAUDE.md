# CLAUDE.md

This file provides guidance for agentic work in this repository.

## Project Overview

This project formalizes real-time scheduling theory in Rocq.

- Proof roadmap: `plan/what_to_prove.md`
- Development roadmap: `plan/roadmap.md`
- Planning/progress notes: `progress/`
- Accumulated proof notes: `proof_knowledge_base.md`

## Build

```bash
make
make clean
```

Representative single-file compilation order:

```bash
rocq compile -R theories SchedulingTheory theories/Foundation/Base.v
rocq compile -R theories SchedulingTheory theories/Semantics/Schedule.v
rocq compile -R theories SchedulingTheory theories/Abstractions/Scheduler/Interface.v
rocq compile -R theories SchedulingTheory theories/Abstractions/SchedulingAlgorithm/Interface.v
rocq compile -R theories SchedulingTheory theories/Abstractions/SchedulingAlgorithm/SchedulerBridge.v
rocq compile -R theories SchedulingTheory theories/Uniprocessor/Policies/EDF.v
rocq compile -R theories SchedulingTheory theories/Uniprocessor/Policies/FIFO.v
rocq compile -R theories SchedulingTheory theories/Multicore/Partitioned/Partitioned.v
rocq compile -R theories SchedulingTheory theories/Examples/SchedulableExamples.v
rocq compile -R theories SchedulingTheory theories/Examples/FeasibleExamples.v
```

## Module Architecture

```text
Foundation/Base.v
  -> Semantics/Schedule.v
  -> Abstractions/Scheduler/Interface.v
  -> Abstractions/SchedulingAlgorithm/Interface.v
  -> Abstractions/SchedulingAlgorithm/SchedulerBridge.v
  -> Uniprocessor/Policies/EDF.v / FIFO.v
  -> Multicore/Partitioned/Partitioned.v
```

| File | Contents |
|------|----------|
| `Foundation/Base.v` | Core types and job/task records |
| `Semantics/Schedule.v` | `eligible`, `ready`, `valid_schedule`, `feasible_schedule`, `feasible_schedule_on` and schedule lemmas |
| `Abstractions/Scheduler/Interface.v` | `Scheduler` record with `scheduler_rel`; `schedulable_by`, `schedulable_by_on` |
| `Abstractions/SchedulingAlgorithm/Interface.v` | `GenericSchedulingAlgorithm` with `choose_eligible`, `choose_some_if_eligible_candidate`, `choose_none_if_no_eligible_candidate`, `choose_in_candidates` |
| `Abstractions/SchedulingAlgorithm/SchedulerBridge.v` | single-CPU algorithm-to-scheduler bridge, `CandidateSourceSpec`, subset schedulability helpers |
| `Uniprocessor/Policies/EDF.v` | EDF algorithm, `edf_generic_spec`, `edf_scheduler` |
| `Uniprocessor/Policies/FIFO.v` | FIFO algorithm, `fifo_generic_spec`, `fifo_scheduler` |
| `Multicore/Partitioned/Partitioned.v` | partitioned multiprocessor scheduler, `partitioned_scheduler`, validity/feasibility lifting theorems |
| `Examples/SchedulableExamples.v` | concrete `edf_scheduler`, `fifo_scheduler`, `partitioned_scheduler` usage examples |
| `Examples/FeasibleExamples.v` | direct feasibility examples over explicit schedules |

## Proof Workflow

- Keep schedule semantics in `Semantics/Schedule.v`
- Keep abstract scheduler reasoning in `Abstractions/Scheduler/Interface.v`
- Keep policy-independent algorithm reasoning in `Abstractions/SchedulingAlgorithm/Interface.v` or `Abstractions/SchedulingAlgorithm/SchedulerBridge.v`
- Keep policy-specific lemmas in `Uniprocessor/Policies/EDF.v`, `Uniprocessor/Policies/FIFO.v`, and multiprocessor lifting in `Multicore/Partitioned/`
- Validate changes by compiling the edited file and affected dependents

## Notes on Historical Documents

Some files in `plan/` and `progress/` are historical refactoring records and may mention superseded names such as `run_scheduler`, `dispatch_ready`, or `local_to_global_validity`. Treat current `.v` files as the source of truth.

## External Libraries

### rocq-stdpp (version 1.13.0)

[rocq-stdpp](https://plv.mpi-sws.org/coqdoc/stdpp/) is installed and available. Prefer stdpp over the Rocq standard library when it offers a more convenient interface — in particular for decidability, finite maps, sets, and list automation.

**Import syntax:**

```coq
From stdpp Require Import base.        (* general automation: done, naive_solver, set_solver *)
From stdpp Require Import decidable.   (* Decision typeclass; decide tactic *)
From stdpp Require Import fin_maps.    (* FinMap interface *)
From stdpp Require Import gmap.        (* generic finite map *)
From stdpp Require Import list.        (* rich list lemmas and list_simplifier tactic *)
From stdpp Require Import sets.        (* set typeclasses; ∈, ∪, ∩, ⊆ notation *)
From stdpp Require Import sorting.     (* Sorted, StronglySorted, merge_sort *)
From stdpp Require Import relations.   (* rtc, tc — reflexive/transitive closure *)
From stdpp Require Import numbers.     (* extra nat/Z lemmas *)
```

Or import the full prelude at once: `From stdpp Require Import prelude.`

**When to use:** use stdpp's `done`/`naive_solver`/`set_solver` tactics in place of `tauto`/`auto`/`firstorder`; use `gmap` for finite maps; use `Decision` for decidability goals. Avoid mixing stdpp `list` with `Stdlib.List` in the same file unless import order is carefully managed.
