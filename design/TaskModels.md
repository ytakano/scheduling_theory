# TaskModels

## Scope

This document describes the task-model layer of the repository.

Its scope is:

- `theories/TaskModels/Common/*`
- `theories/TaskModels/Periodic/*`
- `theories/TaskModels/Sporadic/*`
- `theories/TaskModels/Jitter/*`

This layer explains how task parameters generate semantic jobs and how those generated job sets are exposed to policy and analysis layers.

## Purpose of the TaskModels layer

The task-model layer exists to separate task-generation logic from both schedule semantics and schedulability analysis.

Its responsibilities are:

- relating task parameters to concrete semantic jobs,
- packaging finite-horizon witnesses and enumeration infrastructure,
- exposing bridge modules from generated job sets to policy-specific and analysis-specific theorem layers,
- organizing periodic, sporadic, and jitter-aware task families without redefining the semantic notion of a schedule.

## Core concepts and guarantees

The current organization is:

`TaskModels/Common`
- finite-horizon witness packaging and shared witness-to-policy lifts

`TaskModels/Periodic`
- periodic task parameters, finite-horizon job enumeration, workload and demand bridges, EDF/LLF theorem lifts, and packaged periodic EDF analysis entry points

`TaskModels/Sporadic`
- sporadic task generation, finite-horizon enumeration, workload and demand bridges, EDF/LLF theorem lifts, and periodic/sporadic bridge modules

`TaskModels/Jitter`
- jittered-periodic generation, jitter-aware workload and demand bridges, EDF/LLF lifts, and jitter-to-sporadic bridge modules

Two recurring patterns matter across the task-model layer:

- horizon-bounded enumeration of generated jobs
- bridge-first packaging for downstream theorem use

For example, periodic EDF uses:

- `PeriodicEDFBridge.v` as the canonical bridge-first public module
- `PeriodicEDFBridgeCompat.v` only as a compatibility wrapper for older unpackaged interfaces
- `PeriodicEDFAnalysisEntryPoints.v` as the default downstream import for the packaged periodic EDF analysis surface

## Public entry points

The main public entry points for this layer are:

- `theories/TaskModels/Common/FiniteHorizonWitness.v`
- `theories/TaskModels/Periodic/PeriodicTasks.v`
- `theories/TaskModels/Periodic/PeriodicEDFBridge.v`
- `theories/TaskModels/Periodic/PeriodicEDFAnalysisEntryPoints.v`
- `theories/TaskModels/Sporadic/SporadicTasks.v`
- `theories/TaskModels/Sporadic/SporadicEDFBridge.v`
- `theories/TaskModels/Jitter/JitteredPeriodicTasks.v`
- `theories/TaskModels/Jitter/JitteredPeriodicEDFBridge.v`

Supporting modules include:

- the various `*Enumeration.v`, `*FiniteHorizon.v`, `*Workload.v`, and `*DemandBound.v` files
- the periodic/sporadic/jitter bridge modules
- the partitioned finite-optimality lifts for each task family

## Design boundaries

This layer includes:

- task parameters and generated job sets,
- finite-horizon witness and enumeration infrastructure,
- task-family-specific bridge modules that connect generated jobs to existing policy and analysis theorem layers.

This layer does not include:

- the meaning of schedules,
- the generic scheduler and scheduling-algorithm interfaces,
- interval-analysis concepts as such,
- implementation-facing state machines.

Those belong respectively to:

- `design/Semantics.md`
- `design/Abstractions.md`
- `design/Analysis.md`
- `design/Operational.md`

The key separation is:

- `TaskModels` says where jobs come from,
- `Semantics` says what schedules mean for those jobs,
- `Analysis` says how to reason about schedulability over intervals for those jobs.

## Extension points

The current task-model layer is prepared for:

- additional task families built on the same generated-job and finite-horizon discipline,
- stronger packaged entry points for sporadic and jitter-aware analysis clients,
- richer workload and demand bridges that remain task-model-facing rather than policy-local.

New task-model work should prefer bridge-first public APIs and compatibility wrappers only when preserving older downstream imports matters.

## File map

- `theories/TaskModels/Common/FiniteHorizonWitness.v`
  Finite-horizon witness packaging for generated job subsets.
- `theories/TaskModels/Common/WitnessCandidates.v`
  Candidate-source support for witness-based finite job sets.
- `theories/TaskModels/Common/WitnessFiniteOptimalityLift.v`
  Shared witness-to-policy finite-optimality lift.
- `theories/TaskModels/Periodic/PeriodicTasks.v`
  Periodic task model definitions.
- `theories/TaskModels/Periodic/PeriodicFiniteHorizon.v`
  Periodic finite-horizon infrastructure.
- `theories/TaskModels/Periodic/PeriodicEnumeration.v`
  Periodic job enumeration.
- `theories/TaskModels/Periodic/PeriodicWorkload.v`
  Periodic workload bridge.
- `theories/TaskModels/Periodic/PeriodicDemandBound.v`
  Periodic demand-bound bridge.
- `theories/TaskModels/Periodic/PeriodicWindowDemandBound.v`
  Periodic window-DBF bridge layer.
- `theories/TaskModels/Periodic/PeriodicEDFBridge.v`
  Canonical periodic EDF bridge-first theorem layer.
- `theories/TaskModels/Periodic/PeriodicEDFBridgeCompat.v`
  Compatibility wrappers for older periodic EDF bridge APIs.
- `theories/TaskModels/Periodic/PeriodicEDFAnalysisEntryPoints.v`
  Canonical downstream import for packaged periodic EDF analysis.
- `theories/TaskModels/Sporadic/*`
  Sporadic task definitions, enumeration, workload/demand bridges, and policy lifts.
- `theories/TaskModels/Jitter/*`
  Jittered-periodic task definitions, bridges, workload/demand layers, and policy lifts.

## Summary

The task-model layer explains how task parameters generate the concrete jobs that the rest of the library reasons about.

It owns generated-job structure, finite-horizon packaging, and bridge-first theorem modules for periodic, sporadic, and jitter-aware families. It should stay separate from both schedule semantics and interval-analysis logic.
