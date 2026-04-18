# Refinement

## Scope

This document describes the current refinement layer of the repository.

Its present scope is:

- `theories/Refinement/SchedulingAlgorithmRefinement.v`

The layer is intentionally narrow at the moment. It captures the bridge from executable local scheduling algorithms to abstract policy specifications and schedule-level admission facts.

## Purpose of the Refinement layer

The refinement layer explains how implementation-facing or executable scheduling objects relate to abstract semantic ones.

In the current codebase, that means making the distinction among:

- `SchedulingAlgorithm`: executable local choice
- `SchedulingAlgorithmSpec`: declarative policy condition
- `Scheduler`: schedule-level admission relation
- `Schedule`: semantic execution timeline

Refinement exists to state that an executable chooser implements an abstract policy view, and that schedules induced by that chooser therefore respect the policy.

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

## Public entry points

The stable entry point for this layer is:

- `theories/Refinement/SchedulingAlgorithmRefinement.v`

Downstream users should treat this file as the current default import for:

- executable-to-declarative scheduling refinement,
- schedule-respects-spec bridge lemmas,
- the distinction among algorithm, scheduler, and semantic schedule.

## Design boundaries

This layer includes:

- executable-to-spec refinement statements,
- the inheritance of declarative policy properties by schedules induced from executable choosers,
- schedule-level bridge theorems that rely on the abstraction layer interfaces.

This layer does not include:

- the meaning of schedules themselves,
- policy-specific optimality or local chooser proofs,
- busy-window, processor-demand, or fairness analysis,
- operational traces, state machines, or projection theorems.

Those belong respectively to:

- `design/Semantics.md`
- `design/Uniprocessor.md` and `design/Multicore.md`
- `design/Analysis.md`
- `design/Operational.md`

Refinement is also not the same thing as schedulability analysis. A refinement theorem says an implementation-facing chooser matches an abstract policy boundary. It does not by itself prove that the resulting schedules meet deadlines.

## Extension points

The current refinement layer is ready to grow in two directions:

- richer executable-to-declarative results for additional algorithm interfaces, including multicore variants
- stronger implementation-facing bridges from operational scheduler models to semantic schedules

Such growth should preserve the current split:

- semantics defines the target meaning,
- abstractions define the interfaces,
- refinement states that one layer implements another.

## OS-neutral operational refinement boundary

Concrete multicore OS refinement should not depend on a concrete OS wrapper
inside the common layer. Instead, each OS should provide an adapter from its
concrete state to `OpState`.

The common refinement path is:

Concrete OS state
  -> `OSProjection`
  -> `OpTrace`
  -> `project_schedule`
  -> semantic `Schedule`

The refinement layer may then state that the projected schedule satisfies
validity, admissibility, placement, or scheduler-policy obligations.

This operational projection boundary is distinct from
`theories/Refinement/SchedulingAlgorithmRefinement.v`.
The latter connects executable chooser interfaces to declarative policy specs,
whereas the operational boundary connects concrete machine behavior to semantic
schedules.

Concrete OS-specific operational proofs should therefore live in
`Operational/<OS>` or `Refinement/<OS>`, not inside `Operational/Common`.

## File map

- `theories/Refinement/SchedulingAlgorithmRefinement.v`
  The current refinement boundary: `algorithm_refines_spec` and the induced schedule-respects-spec theorems.

## Summary

The refinement layer is currently a small but important bridge layer.

It makes the relationship between executable local choice and abstract policy specifications explicit, while leaving schedulability analysis and policy-specific theorem work to the higher layers that should own them.
