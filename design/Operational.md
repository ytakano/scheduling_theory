# Operational

## Scope

This document describes the current operational layer.

Its scope is:

- `theories/Operational/Common/*`

The current implementation is a minimal OS-neutral operational projection
slice: it records implementation-facing scheduler views and traces and explains
how they project back into schedule semantics.

The common operational layer now also exposes a delay-aware obligation
boundary: event-labeled executions, delay-source classification, and
cumulative delay budgets. This supports later refinement work without turning
`Operational/Common` into a full concrete OS semantics.

## Purpose of the Operational layer

The operational layer exists to model implementation-facing scheduler state without replacing the abstract schedule semantics.

Its role is to define:

- operational state and trace objects,
- small-step execution structure,
- trace projection into semantic schedules,
- the invariants needed to recover schedule validity from operational behavior,
- an OS-neutral projection boundary from concrete machine states into that
  common scheduler view.

This layer is intentionally modest. It is not yet a full OS semantics with the full range of timer, wakeup, migration, and interrupt behavior.

The new delay-aware surface only exposes the minimum common observables needed
for accounting:

- wakeup
- dispatch
- reschedule request / IPI-facing reschedule signal
- timer tick

Migration, concrete interrupt routing, and non-preemptive runtime details
remain outside the common event interface. Downstream adapters may enrich
delay-source classification without changing `OpEvent` or the semantic
definition of `Schedule`.

## Core concepts and guarantees

The core common operational objects are:

- `OpState`
- `OpTrace`
- `op_step`
- `execution`
- `labeled_execution`
- `op_delay_source`
- `cumulative_delay_budget`
- `OSProjection`
- `concrete_execution`

The key bridge back into the semantic core is:

- `project_schedule : OpTrace -> Schedule`

`OpState` is not a concrete OS state. It is the proof-relevant scheduler view
used by the common operational layer.

The projection layer and its lemmas show how operational traces recover schedule-level execution facts such as running and validity when suitable structural invariants hold.

`ProjectionLemmas.v` packages the current validity boundary:

- `projectable_trace`
- `execution_projection_sound`
- consequences such as `execution_projection_sound_implies_valid_schedule`

`ProjectionInvariants.v` and `ProjectionMulticoreValidity.v` extend that
boundary with the multicore-common bridge:

- operational range / placement invariants on `OpState`
- step-preservation lemmas for those invariants
- bundled execution-level soundness for multicore projection
- consequences such as projected `no_duplication`,
  `schedule_respects_admissibility`, and `multicore_semantic_validity`

Concrete OS adapters may then expose OS-specific states and traces outside
`Operational/Common`. The current `Operational/Awkernel/MinimalProjection.v`
module is the reusable Awkernel adapter boundary, while
`Operational/Awkernel/Minimal/MulticoreProjection.v` is a 2-CPU minimal
example entry point built on top of that boundary.

## Public entry points

The stable public entry points for this layer are:

- `theories/Operational/Common/OperationalEntryPoints.v`

Important supporting modules include:

- `theories/Operational/Common/State.v`
- `theories/Operational/Common/Trace.v`
- `theories/Operational/Common/Step.v`
- `theories/Operational/Common/Invariants.v`
- `theories/Operational/Common/Execution.v`
- `theories/Operational/Common/OSProjectionInterface.v`
- `theories/Operational/Common/ConcreteExecution.v`
- `theories/Operational/Common/Projection.v`
- `theories/Operational/Common/ProjectionLemmas.v`

## Design boundaries

This layer includes:

- implementation-facing scheduler views and traces,
- stepwise operational execution structure,
- OS-neutral projection from concrete states into `OpState`,
- projection from traces to abstract schedules,
- operational invariants used to recover semantic schedule validity.

This layer does not include:

- concrete OS state definitions,
- concrete OS adapters,
- the definition of schedule meaning itself,
- declarative or executable scheduler interfaces,
- interval schedulability analysis,
- full implementation-to-spec refinement theorems beyond the current projection soundness slice.

Those belong respectively to:

- `design/Semantics.md`
- `design/Abstractions.md`
- `design/Analysis.md`
- `design/Refinement.md`

The key split is that `Operational` records machine-facing behavior, while
`Semantics` continues to own the abstract schedule model that those traces
project into. Concrete OS adapters must therefore live outside
`Operational/Common`.

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
- `theories/Operational/Common/LabeledExecution.v`
  Packaged executions with per-step observable events.
- `theories/Operational/Common/DelayModel.v`
  Common delay-source vocabulary and default event classification.
- `theories/Operational/Common/DelayBudget.v`
  Cumulative delay-budget accounting lemmas over delay-source traces.
- `theories/Operational/Common/OSProjectionInterface.v`
  OS-neutral projection from concrete machine state to `OpState`.
- `theories/Operational/Common/ConcreteExecution.v`
  Wrapper that packages projected concrete traces as common operational executions.
- `theories/Operational/Common/Projection.v`
  Projection from operational traces to semantic schedules.
- `theories/Operational/Common/ProjectionLemmas.v`
  Projection soundness lemmas linking operational traces to schedule validity.
- `theories/Operational/Common/ProjectionInvariants.v`
  Operational range / placement invariants used by the multicore bridge.
- `theories/Operational/Common/ProjectionMulticoreValidity.v`
  Trace- and execution-level bridge lemmas from operational projection to
  `Multicore/Common`.
- `theories/Operational/Awkernel/MinimalProjection.v`
  Concrete adapter example built on top of the common projection slice.
- `theories/Operational/Awkernel/Minimal/MulticoreProjection.v`
  Thin 2-CPU Awkernel-facing entry point for the multicore projection bridge.
- `theories/Operational/Awkernel/Minimal/OperationalMulticoreProjectionExamples.v`
  Worked 2-CPU projection examples layered on top of the Awkernel minimal
  projection boundary.

## Summary

The operational layer is the implementation-facing trace layer of the
repository.

Its current scope is deliberately minimal: define an OS-neutral operational
scheduler view and traces, project them into schedule semantics, and recover
schedule validity, no-duplication, range-idleness, and placement facts from
explicit invariants. It should not be documented as a full OS semantics before
the code actually reaches that scope.
