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
rocq compile Base.v
rocq compile ScheduleModel.v
rocq compile SchedulerInterface.v
rocq compile DispatchInterface.v
rocq compile DispatchSchedulerBridge.v
rocq compile UniPolicies/EDF.v
rocq compile UniPolicies/FIFO.v
rocq compile Partitioned.v
rocq compile SchedulableExamples.v
rocq compile FeasibleExamples.v
```

## Module Architecture

```text
Base.v
  -> ScheduleModel.v
  -> SchedulerInterface.v
  -> DispatchInterface.v
  -> DispatchSchedulerBridge.v
  -> EDF.v / FIFO.v / Partitioned.v  (EDF.v, FIFO.v live in UniPolicies/)
```

| File | Contents |
|------|----------|
| `Base.v` | Core types and job/task records |
| `ScheduleModel.v` | `eligible`, `ready`, `valid_schedule`, `feasible_schedule`, `feasible_schedule_on` and schedule lemmas |
| `SchedulerInterface.v` | `Scheduler` record with `scheduler_rel`; `schedulable_by`, `schedulable_by_on` |
| `DispatchInterface.v` | `GenericDispatchSpec` with `dispatch_eligible`, `dispatch_some_if_eligible_candidate`, `dispatch_none_if_no_eligible_candidate`, `dispatch_in_candidates` |
| `DispatchSchedulerBridge.v` | single-CPU dispatch-to-scheduler bridge, `CandidateSourceSpec`, subset schedulability helpers |
| `UniPolicies/EDF.v` | EDF dispatcher, `edf_generic_spec`, `edf_scheduler` |
| `UniPolicies/FIFO.v` | FIFO dispatcher, `fifo_generic_spec`, `fifo_scheduler` |
| `Partitioned.v` | partitioned multiprocessor scheduler, `partitioned_scheduler`, validity/feasibility lifting theorems |
| `SchedulableExamples.v` | concrete `edf_scheduler`, `fifo_scheduler`, `partitioned_scheduler` usage examples |
| `FeasibleExamples.v` | direct feasibility examples over explicit schedules |

## Proof Workflow

- Keep schedule semantics in `ScheduleModel.v`
- Keep abstract scheduler reasoning in `SchedulerInterface.v`
- Keep policy-independent dispatch reasoning in `DispatchInterface.v` or `DispatchSchedulerBridge.v`
- Keep policy-specific lemmas in `UniPolicies/EDF.v`, `UniPolicies/FIFO.v`, and multiprocessor lifting in `Partitioned.v`
- Validate changes by compiling the edited file and affected dependents

## Notes on Historical Documents

Some files in `plan/` and `progress/` are historical refactoring records and may mention superseded names such as `run_scheduler`, `dispatch_ready`, or `local_to_global_validity`. Treat current `.v` files as the source of truth.
