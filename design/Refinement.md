# Refinement

## Scope

This document describes the current refinement layer of the repository.

Its present scope is:

- `theories/Refinement/SchedulingAlgorithmRefinement.v`
- `theories/Refinement/BoundedDelayRefinement.v`

The layer is intentionally narrow at the moment. It captures the bridge from executable local scheduling algorithms to abstract policy specifications and schedule-level admission facts.

It now also includes the first common bounded-delay refinement boundary for
operational multicore work. That boundary still stops short of any
OS-specific theorem and keeps ideal schedule semantics separate from delay
accounting.

## Purpose of the Refinement layer

The refinement layer explains how implementation-facing or executable scheduling objects relate to abstract semantic ones.

In the current codebase, that means making the distinction among:

- `SchedulingAlgorithm`: executable local choice
- `SchedulingAlgorithmSpec`: declarative policy condition
- `Scheduler`: schedule-level admission relation
- `Schedule`: semantic execution timeline

Refinement exists to state that an executable chooser implements an abstract
policy view, that schedules induced by that chooser therefore respect the
policy, and that selected cross-layer arrows preserve the intended service or
policy facts.

## Core concepts and guarantees

The central definition is:

- `algorithm_refines_spec`

It states that a concrete `GenericSchedulingAlgorithm` always produces an output permitted by a declarative `SchedulingAlgorithmSpec`.

The main theorems then show that if this refinement relation holds, schedules admitted by the standard single-CPU bridge inherit the declarative policy view:

- `single_cpu_algorithm_schedule_respects_algorithm_spec_at_with`
- `single_cpu_algorithm_schedule_respects_algorithm_spec_before`
- `single_cpu_algorithm_schedule_implies_single_cpu_algorithm_spec_schedule`

The current guarantee boundary is therefore:

- refinement connects executable local choice to declarative policy-respecting schedules
- the bridge is phrased at the schedule-admission level, not as a schedulability theorem
- bounded-delay refinement connects labeled operational execution to an ideal
  semantic schedule through cumulative delay budgets and service lag
- correctness-of-arrows reasoning is local to named refinement arrows: a
  chooser-to-policy arrow, a projected-schedule-to-ideal-service arrow, or a
  wrapper theorem that preserves a stated semantic property

## Public entry points

The stable entry point for this layer is:

- `theories/Refinement/SchedulingAlgorithmRefinement.v`
- `theories/Refinement/BoundedDelayRefinement.v`

Downstream users should treat this file as the current default import for:

- executable-to-declarative scheduling refinement,
- schedule-respects-spec bridge lemmas,
- bounded-delay/service-lag wrappers,
- the distinction among algorithm, scheduler, and semantic schedule.

## Design boundaries

This layer includes:

- executable-to-spec refinement statements,
- the inheritance of declarative policy properties by schedules induced from executable choosers,
- schedule-level bridge theorems that rely on abstraction-layer interfaces,
- service-lag-based bounded-delay interfaces between operational executions and
  ideal schedules,
- and correctness statements for explicit arrows between executable choosers,
  declarative policy specs, projected schedules, and ideal schedules.

This layer does not include:

- the meaning of schedules themselves,
- policy-specific optimality or local chooser proofs,
- busy-window, processor-demand, or fairness analysis,
- operational traces, state machines, or projection theorems.
- the operational projection theorem ladder or adapter contract ladder.

Those belong to the design layers that define the corresponding objects:

- `design/Semantics.md`
- `design/Uniprocessor.md` and `design/Multicore.md`
- `design/Analysis.md`
- `design/Operational.md`

Refinement is also not the same thing as schedulability analysis. A refinement theorem says an implementation-facing chooser matches an abstract policy boundary. It does not by itself prove that the resulting schedules meet deadlines.

## Extension points

The current refinement layer is ready to grow in these directions:

- richer executable-to-declarative results for additional algorithm interfaces, including multicore variants
- stronger bounded-delay/service-lag results relating projected schedules to
  ideal schedules
- additional correctness-of-arrows wrappers that preserve explicitly named
  policy or service facts

Such growth should preserve the current split:

- semantics defines the target meaning,
- abstractions define the interfaces,
- operational/common defines projection objects, projection theorems, and
  adapter contracts,
- refinement states that one executable, policy, schedule, or service relation
  arrow implements another.

## Operational/Common Boundary

Operational projection from concrete behavior to `OpState`, then to a semantic
`Schedule`, is owned by `design/Operational.md` and the
`Operational/Common` entry point. The projection theorem ladder and the adapter
contract ladder are operational/common responsibilities, even when individual
wrapper theorems live under `theories/Refinement/*` for historical or import
organization reasons.

That operational/common ladder is:

Concrete OS state
  -> `OSProjection`
  -> `OpTrace` / `labeled_execution`
  -> `project_schedule`
  -> semantic `Schedule`.

Operational/Common also owns the adapter contracts that justify the arrows
above:

- local concrete projection soundness,
- multicore projection soundness,
- scheduler-view and handoff contracts,
- candidate-source and admissibility-aware candidate-source contracts,
- scheduler-relation contracts,
- algorithm adapter contracts,
- and delay adapter contracts.

The refinement layer may consume the resulting projected schedule, labeled
execution, or delay budget when proving executable chooser-to-policy,
bounded-delay/service-lag, or correctness-of-arrows statements. It should not
redefine the operational projection boundary.

The bounded-delay path that belongs to Refinement starts after an operational
projection has already supplied the relevant schedule-facing objects:

Projected/labeled operational execution
  -> delay source trace
  -> cumulative delay budget
  -> actual semantic `Schedule`
  -> ideal semantic `Schedule`
  -> service-lag obligation.

The scheduler-policy path that belongs to Refinement is:

Executable chooser
  -> declarative policy spec
  -> induced schedule respects that policy
  -> scheduler-level policy statement.

When an operational adapter also proves that its projected schedule satisfies a
scheduler relation, that operational theorem can be an input to refinement
reasoning. The ownership boundary remains:

Emitted policy metadata in a concrete trace is not the refinement layer's
source of truth. Refinement consumes adapter-packaged evidence that a projected
schedule satisfies a declarative scheduler relation; it does not define raw
trace policy fields or unsupported-policy diagnostics.

The same ownership applies to the implemented minimal EDF/FIFO trace adapter
boundary. Runtime `RunnableDeadline` rows for non-DAG `GlobalEDF` releases are
adapter-local evidence used to reconstruct release/deadline facts before a
scheduler-relation witness is packaged. They do not add `OpState` fields,
`OpEvent` payloads, or common projection fields, and they are not refinement
entry points by themselves. The adapter accepts only the supported
`GlobalEDF`/`PrioritizedFIFO` set for this boundary, rejects `PrioritizedRR`,
`Panicked`, and unknown policies, gives visible `GlobalEDF` candidates priority
over FIFO candidates, and falls back to FIFO only when no EDF candidate is
visible. DAG GEDF and multi-CPU EDF remain outside this minimal refinement
composition. Diagnostics such as unsupported-policy, EDF deadline metadata,
and EDF/FIFO scheduler-rule rejection are concrete checker outputs, not
refinement-layer obligations.

- Operational/Common: projection theorem ladder and adapter contract ladder.
- Adapter layer: concrete witness construction from runtime observables.
- Refinement: executable chooser-to-policy, bounded-delay/service-lag, and
  correctness of explicit arrows.

An end-to-end concrete OS argument may compose all of these arrows:

Concrete OS state
  -> `OSProjection`
  -> `OpTrace` / `labeled_execution`
  -> `project_schedule`
  -> semantic `Schedule`
  -> `multicore_semantic_validity`
  -> placement / admissibility obligations
  -> optional scheduler-policy or service-lag refinement facts.

The first part of that chain is operational/common. The last optional
policy/service arrows are refinement.

## File map

- `theories/Refinement/SchedulingAlgorithmRefinement.v`
  The current refinement boundary: `algorithm_refines_spec` and the induced schedule-respects-spec theorems.
- `theories/Refinement/BoundedDelayRefinement.v`
  The common delay-aware refinement boundary: `service_lag_le` and the
  packaging record for labeled executions, delay budgets, and ideal schedules.

## Summary

The refinement layer is currently a small but important bridge layer.

It makes the relationship between executable local choice and abstract policy
specifications explicit, and it hosts bounded-delay/service-lag and
correctness-of-arrows reasoning. Operational projection theorems and adapter
contracts remain in the Operational/Common design boundary.
