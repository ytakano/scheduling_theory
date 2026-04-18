# Semantics

## Scope

This document describes the semantic layer of the current RocqSched implementation.

Its scope is:

- `theories/Semantics/Schedule.v`
- `theories/Semantics/ScheduleLemmas/ScheduleFacts.v`
- `theories/Semantics/ScheduleLemmas/SchedulePrefix.v`
- `theories/Semantics/ScheduleLemmas/ScheduleRestriction.v`
- `theories/Semantics/ScheduleLemmas/ScheduleTruncationCore.v`
- `theories/Semantics/ScheduleLemmas/ScheduleTruncation.v`
- `theories/Semantics/ScheduleLemmas/ScheduleTransform.v`

This layer defines what schedules mean and packages the prefix, restriction, truncation, and local-transformation facts that later proofs reuse.

## Purpose of the Semantics layer

The semantics layer gives meaning to the raw `Schedule` carrier introduced in the foundation layer.

Its role is to define:

- what it means for a job to run,
- how service accumulates,
- when a job is completed, eligible, or ready,
- what makes a schedule valid,
- what it means for deadlines to be met,
- which semantic facts are preserved under common schedule manipulations.

This layer is intentionally policy-neutral. It defines the semantic universe in which scheduler, analysis, and refinement layers operate.

## Core concepts and guarantees

The central object remains:

```coq
Schedule := Time -> CPU -> option JobId
```

Built on top of it, `Schedule.v` defines the core semantic notions:

- `runs_on`, `running`, and `cpu_count` for slot-level execution
- `service_job` for cumulative service
- `completed`, `eligible`, and `ready` for job-state reasoning
- `valid_schedule` and feasibility predicates for semantic correctness
- `remaining_cost` and `laxity` for downstream metric and analysis arguments

The schedule-lemmas files then package reusable semantic tooling:

- reflection and basic service lemmas in `ScheduleFacts.v`
- prefix extensionality via `agrees_before` in `SchedulePrefix.v`
- single-CPU and subset restriction operators in `ScheduleRestriction.v`
- finite-horizon truncation in `ScheduleTruncationCore.v`
- local rewrites such as `swap_at` in `ScheduleTransform.v`

Two design choices are especially important:

- the layer is multicore-aware from the start, even for later uniprocessor clients
- `eligible` and `ready` are kept distinct, so running jobs remain eligible but are not ready

## Public entry points

The stable entry points for this layer are:

- `theories/Semantics/Schedule.v`
- `theories/Semantics/ScheduleLemmas/ScheduleFacts.v`
- `theories/Semantics/ScheduleLemmas/SchedulePrefix.v`
- `theories/Semantics/ScheduleLemmas/ScheduleRestriction.v`
- `theories/Semantics/ScheduleLemmas/ScheduleTruncationCore.v`
- `theories/Semantics/ScheduleLemmas/ScheduleTruncation.v`
- `theories/Semantics/ScheduleLemmas/ScheduleTransform.v`

In practice:

- downstream definitions should start from `Schedule.v`
- downstream proofs should prefer the packaged lemmas from `ScheduleLemmas/*` instead of re-unfolding raw definitions

## Design boundaries

This layer includes:

- schedule meaning,
- service and completion semantics,
- validity and feasibility semantics,
- prefix-preservation and finite-horizon semantic tooling,
- local schedule transformations used by later structural proofs.

This layer does not include:

- concrete scheduling policies such as EDF, LLF, FIFO, RR, or top-`m`,
- scheduler or algorithm interfaces,
- periodic, sporadic, or jitter-aware job generation,
- interval analysis concepts such as busy windows or processor demand,
- operational traces or implementation-facing state machines.

Those belong respectively to:

- `design/Uniprocessor.md` and `design/Multicore.md`
- `design/Abstractions.md`
- `design/TaskModels.md`
- `design/Analysis.md`
- `design/Operational.md`

## Extension points

The current semantic layer already exposes natural growth directions:

- richer finite-set or finite-horizon reasoning through the restricted feasibility interfaces,
- future node-level or DAG-aware execution models,
- deeper multicore semantic facts that still remain independent of policy choice,
- additional transformation lemmas that preserve the same semantic core.

Such extensions should preserve the role of this layer as the place where schedule meaning is fixed, not the place where policies or analyses are defined.

## File map

- `theories/Semantics/Schedule.v`
  Core schedule semantics: execution, service, completion, readiness, validity, feasibility, remaining cost, and laxity.
- `theories/Semantics/ScheduleLemmas/ScheduleFacts.v`
  Foundational facts, reflection lemmas, and basic service/count consequences.
- `theories/Semantics/ScheduleLemmas/SchedulePrefix.v`
  Prefix agreement and prefix-extensionality theorems.
- `theories/Semantics/ScheduleLemmas/ScheduleRestriction.v`
  Single-CPU and job-set restriction operators and preservation lemmas.
- `theories/Semantics/ScheduleLemmas/ScheduleTruncationCore.v`
  Policy-neutral finite-horizon truncation operator and core prefix lemmas.
- `theories/Semantics/ScheduleLemmas/ScheduleTruncation.v`
  Compatibility wrapper that re-exports truncation core plus higher-layer preservation lemmas.
- `theories/Semantics/ScheduleLemmas/ScheduleTransform.v`
  Local schedule rewrites used by exchange and normalization arguments.

## Summary

The semantics layer defines what schedules mean and packages the reusable facts that depend only on that meaning.

It is the stable policy-neutral core beneath abstractions, refinement, analysis, uniprocessor, multicore, task-model, and operational developments. Its job is to keep schedule meaning small, explicit, and reusable.
