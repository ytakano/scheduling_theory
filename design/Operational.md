# Operational

## Scope

This document describes the current operational layer.

Its scope is:

- `theories/Operational/Common/*`
- `theories/Operational/Awkernel/*`

The current implementation is a minimal operational projection slice: it records implementation-facing state and traces and explains how they project back into schedule semantics.

## Purpose of the Operational layer

The operational layer exists to model implementation-facing scheduler state without replacing the abstract schedule semantics.

Its role is to define:

- operational state and trace objects,
- small-step execution structure,
- trace projection into semantic schedules,
- the invariants needed to recover schedule validity from operational behavior,
- thin Awkernel-facing wrappers over that common projection layer.

This layer is intentionally modest. It is not yet a full OS semantics with the full range of timer, wakeup, migration, and interrupt behavior.

## Core concepts and guarantees

The core common operational objects are:

- `OpState`
- `OpTrace`
- `op_step`
- `execution`

The key bridge back into the semantic core is:

- `project_schedule : OpTrace -> Schedule`

The projection layer and its lemmas show how operational traces recover schedule-level execution facts such as running and validity when suitable structural invariants hold.

`ProjectionLemmas.v` packages the current soundness boundary:

- `projectable_trace`
- `execution_projection_sound`
- consequences such as `execution_projection_sound_implies_valid_schedule`

The Awkernel wrapper layer then exposes:

- `AwkernelState`
- `AwkernelTrace`
- `awk_project_schedule`
- `awk_execution`
- `awk_trace_sound`

This keeps the operational common layer reusable while still providing an implementation-facing wrapper for Awkernel-oriented developments.

## Public entry points

The stable public entry points for this layer are:

- `theories/Operational/Common/Projection.v`
- `theories/Operational/Common/ProjectionLemmas.v`
- `theories/Operational/Awkernel/MinimalProjection.v`

Important supporting modules include:

- `theories/Operational/Common/State.v`
- `theories/Operational/Common/Trace.v`
- `theories/Operational/Common/Step.v`
- `theories/Operational/Common/Invariants.v`
- `theories/Operational/Common/Execution.v`

## Design boundaries

This layer includes:

- implementation-facing state and traces,
- stepwise operational execution structure,
- projection from traces to abstract schedules,
- operational invariants used to recover semantic schedule validity.

This layer does not include:

- the definition of schedule meaning itself,
- declarative or executable scheduler interfaces,
- interval schedulability analysis,
- full implementation-to-spec refinement theorems beyond the current projection soundness slice.

Those belong respectively to:

- `design/Semantics.md`
- `design/Abstractions.md`
- `design/Analysis.md`
- `design/Refinement.md`

The key split is that `Operational` records machine-facing behavior, while `Semantics` continues to own the abstract schedule model that those traces project into.

## Extension points

The current operational layer is prepared for:

- richer step relations and event structure,
- stronger trace invariants,
- more explicit delay, wakeup, migration, and timer modeling,
- deeper implementation-facing bridges that feed the refinement layer.

These extensions should continue to project into the same semantic schedule layer rather than redefine schedule meaning locally.

## File map

- `theories/Operational/Common/State.v`
  Core operational state.
- `theories/Operational/Common/Trace.v`
  Operational traces.
- `theories/Operational/Common/Step.v`
  Small-step operational relation.
- `theories/Operational/Common/StepLemmas.v`
  Supporting lemmas for the step relation.
- `theories/Operational/Common/Invariants.v`
  Structural invariants over operational states.
- `theories/Operational/Common/Execution.v`
  Packaged stepwise execution objects.
- `theories/Operational/Common/Projection.v`
  Projection from operational traces to semantic schedules.
- `theories/Operational/Common/ProjectionLemmas.v`
  Projection soundness lemmas linking operational traces to schedule validity.
- `theories/Operational/Awkernel/MinimalProjection.v`
  Awkernel-facing thin wrapper over the common projection slice.

## Summary

The operational layer is the implementation-facing trace layer of the repository.

Its current scope is deliberately minimal: define operational state and traces, project them into schedule semantics, and recover schedule validity from explicit invariants. It should not be documented as a full OS semantics before the code actually reaches that scope.
