# Foundation

## Scope

This document describes the foundation layer of the current RocqSched implementation.

Its scope is intentionally small and currently centers on:

- `theories/Foundation/Base.v`

This layer fixes the basic scalar domains and the minimal records that later layers consume.

It does not define schedule meaning, scheduler interfaces, task-generation semantics, analysis theorems, or operational traces.

## Purpose of the Foundation layer

The foundation layer provides the smallest stable vocabulary shared by the rest of the development.

Its role is to fix:

- the identifier types used for tasks and jobs,
- the discrete time and CPU domains,
- the minimal task and job records,
- the first derived schedule shape used by later semantic developments.

The design goal is stability. Later layers should be able to grow without forcing churn in these base definitions.

## Core concepts and guarantees

The current implementation defines four scalar aliases:

- `JobId`
- `TaskId`
- `CPU`
- `Time`

All are currently `nat`. This keeps the base layer constructive and lightweight.

The layer also defines the two central records:

- `Task`, with `task_cost`, `task_period`, and `task_relative_deadline`
- `Job`, with `job_task`, `job_index`, `job_release`, `job_cost`, and `job_abs_deadline`

These records are deliberately minimal.

- `Task` is a task-level parameter container, not yet a full periodic or sporadic generation rule.
- `Job` is the current execution unit used by schedule semantics.

`Base.v` also introduces the derived schedule shape:

```coq
Schedule := Time -> CPU -> option JobId
```

This is already multicore-capable even though many developments later specialize to one CPU.

Finally, the foundation file includes a few very close-to-the-data predicates such as:

- `released`
- `pre_release`
- `valid_jobs`
- `valid_job_of_task`

These remain foundational because they only relate jobs and tasks at the data level. They do not yet define completion, readiness, validity of schedules, or schedulability.

## Public entry points

The default downstream entry point for this layer is:

- `theories/Foundation/Base.v`

Clients reading the library from the bottom up should start here to learn:

- the base identifiers,
- the minimal task and job records,
- the shared discrete-time schedule shape.

## Design boundaries

This layer includes:

- base identifiers and scalar domains,
- minimal task and job records,
- the raw schedule carrier type,
- simple data-facing predicates closely attached to the records.

This layer does not include:

- semantic notions such as `eligible`, `ready`, `completed`, `valid_schedule`, or `feasible`,
- scheduler or algorithm interfaces,
- periodic, sporadic, or jitter-aware job generation,
- busy-window, demand-bound, or interference reasoning,
- operational state machines or trace projection.

Those belong respectively to:

- `design/Semantics.md`
- `design/Abstractions.md`
- `design/TaskModels.md`
- `design/Analysis.md`
- `design/Operational.md`

## Extension points

The current base layer leaves room for later growth without committing to it yet.

The main visible extension directions are:

- richer task records or auxiliary task-model metadata,
- future DAG-aware execution units layered above the current job-centric core,
- alternate finite or abstract CPU domains if the project later needs them.

Any such extension should preserve the base role of this layer as a small shared vocabulary rather than push higher-level semantics downward.

## File map

- `theories/Foundation/Base.v`
  Base identifiers, task and job records, the raw `Schedule` type, and simple foundational predicates.

## Summary

The foundation layer is the minimal data layer of the project.

It defines the stable base objects that every higher layer talks about, while deliberately avoiding schedule semantics, scheduler logic, task-generation policy, and operational behavior. That small scope is intentional and should remain stable.
