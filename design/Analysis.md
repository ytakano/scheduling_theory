# Analysis

## Scope

This document describes the analysis layer of the current repository.

Its scope is:

- `theories/Analysis/Common/*`
- `theories/Analysis/Uniprocessor/*`
- `theories/Analysis/Multicore/*`

This layer hosts reusable interval-based schedulability reasoning built on top of semantic schedules and scheduler theorem layers.

## Purpose of the Analysis layer

The analysis layer packages concepts and lemmas used to reason about schedulability over intervals without mixing them into schedule semantics or scheduler implementation correctness.

Its job is to host reusable analysis notions such as:

- busy intervals, busy windows, and busy prefixes,
- processor demand, request bound, and demand bound,
- processor supply and interference,
- workload absorption and fairness-facing contradiction hooks.

The layer is organized so that policy theorem layers remain structural and analysis clients can import packaged entry points instead of rebuilding interval arguments from scratch.

## Core concepts and guarantees

The current analysis layer is split into three sublayers.

`Analysis/Common`
- shared workload aggregation and arithmetic-facing helpers used by multiple clients

`Analysis/Uniprocessor`
- busy-interval and busy-window reasoning
- response-time and search-space reduction lemmas
- processor-demand, request-bound, and demand-bound facts
- EDF-facing processor-demand wrappers and packaged busy-prefix bridges

`Analysis/Multicore`
- processor-supply accounting
- interference and covering-list reasoning
- workload absorption
- fairness contradiction and must-run client theorems
- packaged multicore global analysis entry points

Two packaged public boundaries are especially important:

- `TaskModels/Periodic/PeriodicEDFAnalysisEntryPoints.v` for the current periodic EDF processor-demand / busy-prefix line
- `Analysis/Multicore/GlobalAnalysisEntryPoints.v` for the current multicore global-analysis line

The design rule is bridge-first packaging:

- expose packaged bridge records and entry-point modules as the default API,
- keep compatibility wrappers and internal helper lemmas out of the primary downstream surface.

## Public entry points

The main public entry points for this layer are:

- `theories/Analysis/Uniprocessor/BusyWindowSearch.v`
- `theories/Analysis/Uniprocessor/EDFProcessorDemand.v`
- `theories/Analysis/Multicore/GlobalAnalysisEntryPoints.v`
- `theories/TaskModels/Periodic/PeriodicEDFAnalysisEntryPoints.v`

Additional foundational modules include:

- `theories/Analysis/Common/WorkloadAggregation.v`
- `theories/Analysis/Uniprocessor/BusyInterval.v`
- `theories/Analysis/Uniprocessor/ProcessorDemand.v`
- `theories/Analysis/Uniprocessor/RequestBound.v`
- `theories/Analysis/Uniprocessor/DemandBound.v`
- `theories/Analysis/Multicore/ProcessorSupply.v`
- `theories/Analysis/Multicore/Interference.v`
- `theories/Analysis/Multicore/GlobalWorkloadAbsorption.v`
- `theories/Analysis/Multicore/GlobalFairness.v`

## Design boundaries

This layer includes:

- analysis concepts and interval lemmas,
- packaged analysis-facing bridges,
- workload and supply/demand accounting,
- fairness-facing client theorems built from those analysis concepts.

This layer does not include:

- the definition of schedule meaning,
- scheduler implementation correctness or executable-to-spec refinement,
- policy-local chooser proofs,
- task-generation semantics themselves.

Those belong respectively to:

- `design/Semantics.md`
- `design/Refinement.md`
- `design/Uniprocessor.md` and `design/Multicore.md`
- `design/TaskModels.md`

In particular, analysis is not the same as refinement. Analysis proves interval reasoning and deadline-related consequences assuming semantic schedules and theorem-layer boundaries; refinement proves that implementation-facing behavior matches those abstract boundaries.

## Extension points

The current analysis layer is ready to expand in several ways:

- more packaged entry points for sporadic and jitter-aware analysis clients,
- richer multicore tardiness and interference bounds,
- delay-aware analysis that consumes explicit operational or refinement-side delay parameters,
- stronger reuse between uniprocessor and multicore interval reasoning.

These extensions should keep the same discipline: put analysis facts in `Analysis`, not in the policy theorem files that happen to consume them.

## File map

- `theories/Analysis/Common/WorkloadAggregation.v`
  Shared workload aggregation and arithmetic helpers.
- `theories/Analysis/Uniprocessor/BusyInterval.v`
  Busy-interval definitions and first-layer facts.
- `theories/Analysis/Uniprocessor/BusyIntervalLemmas.v`
  Supporting busy-interval lemmas.
- `theories/Analysis/Uniprocessor/BusyWindowSearch.v`
  Busy-window and busy-prefix search interfaces.
- `theories/Analysis/Uniprocessor/ProcessorDemand.v`
  Generic processor-demand reasoning.
- `theories/Analysis/Uniprocessor/RequestBound.v`
  Request-bound functions and associated lemmas.
- `theories/Analysis/Uniprocessor/DemandBound.v`
  Demand-bound interfaces and lemmas.
- `theories/Analysis/Uniprocessor/ResponseTimeSearch.v`
  Response-time search-space infrastructure.
- `theories/Analysis/Uniprocessor/EDFProcessorDemand.v`
  EDF-facing processor-demand wrappers and packaged busy-prefix bridges.
- `theories/Analysis/Multicore/ProcessorSupply.v`
  Machine-supply accounting over intervals.
- `theories/Analysis/Multicore/Interference.v`
  Interference and covering-list infrastructure.
- `theories/Analysis/Multicore/GlobalWorkloadAbsorption.v`
  Workload-absorption bridge layer above supply and interference facts.
- `theories/Analysis/Multicore/GlobalFairness.v`
  Fairness-facing contradiction and must-run clients.
- `theories/Analysis/Multicore/GlobalAnalysisEntryPoints.v`
  Canonical downstream import for the current multicore global-analysis theorem layer.

## Summary

The analysis layer is where interval-based schedulability reasoning lives.

It sits above schedule semantics and scheduler theorem layers, exposes packaged public entry points, and keeps analysis concepts separate from both scheduler implementation correctness and task-generation semantics.
