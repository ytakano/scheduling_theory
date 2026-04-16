# Abstractions

## Scope

This document describes the abstraction layer that sits above schedule semantics and below policy-specific theorem layers.

Its scope is:

- `theories/Abstractions/SchedulingAlgorithm/Interface.v`
- `theories/Abstractions/SchedulingAlgorithm/Lemmas.v`
- `theories/Abstractions/SchedulingAlgorithm/ClassicalLemmas.v`
- `theories/Abstractions/SchedulingAlgorithm/EnumCandidates.v`
- `theories/Abstractions/SchedulingAlgorithm/SchedulerBridge.v`
- `theories/Abstractions/SchedulingAlgorithm/TopMInterface.v`
- `theories/Abstractions/SchedulingAlgorithm/TopMSchedulerBridge.v`
- `theories/Abstractions/Scheduler/Interface.v`
- `theories/Abstractions/Scheduler/Validity.v`
- `theories/Uniprocessor/Generic/SchedulingAlgorithmCanonicalBridge.v`

This layer packages the reusable interfaces that keep schedule meaning, local choice, candidate provisioning, and global scheduler admission distinct.

## Purpose of the Abstractions layer

The abstraction layer exists to separate concerns that should not be conflated:

- semantic schedules,
- local executable choice,
- candidate visibility,
- global scheduler admission,
- declarative policy specifications,
- chooser-to-schedule bridge notions.

This separation lets the project share proof structure across many concrete policies and machine models without hard-coding EDF, LLF, FIFO, RR, or top-`m` behavior into the semantic core.

## Core concepts and guarantees

The main abstraction objects are:

- `GenericSchedulingAlgorithm` for local single-CPU choice
- `CandidateSource` and `CandidateSourceSpec` for candidate provisioning
- `Scheduler`, `schedulable_by`, and `schedulable_by_on` for global scheduler admission
- `SchedulingAlgorithmSpec` and the policy-respecting predicates in `Scheduler/Validity.v` for declarative policy views
- `GenericTopMSchedulingAlgorithm` and the top-`m` bridge for global multicore local choice

This layer also introduces the canonical bridge notions:

- `matches_choose_at_with`
- `matches_choose_before`

These are not primitive semantics. They are derived schedule-facing views that say a concrete schedule agrees with a chooser on one time step or a finite prefix.

The bridge files then lift local choice into scheduler-level objects:

- `single_cpu_algorithm_schedule`
- top-`m` schedule bridges for multicore

The result is a layered API in which:

- semantics says what a schedule means,
- abstractions say how local choice and scheduler admission are packaged,
- policy layers instantiate those abstractions.

## Public entry points

The default public entry points for this layer are:

- `theories/Abstractions/SchedulingAlgorithm/Interface.v`
- `theories/Abstractions/Scheduler/Interface.v`
- `theories/Abstractions/SchedulingAlgorithm/SchedulerBridge.v`
- `theories/Abstractions/Scheduler/Validity.v`
- `theories/Abstractions/SchedulingAlgorithm/TopMInterface.v`
- `theories/Abstractions/SchedulingAlgorithm/TopMSchedulerBridge.v`
- `theories/Uniprocessor/Generic/SchedulingAlgorithmCanonicalBridge.v`

Supporting modules:

- `Lemmas.v` is the constructive generic lemma layer
- `ClassicalLemmas.v` is the classical convenience layer
- `EnumCandidates.v` is the standard constant finite candidate source

Downstream clients should treat the canonical bridge module as the chooser-to-schedule interface, not as a replacement for the abstraction core.

## Design boundaries

This layer includes:

- reusable interfaces for local scheduling algorithms and schedulers,
- candidate-source contracts,
- declarative policy specifications,
- executable and declarative bridges from local choice to admitted schedules,
- chooser-matching notions used by normalization and witness arguments.

This layer does not include:

- the semantic meaning of schedules,
- concrete policy rules or policy-specific local proofs,
- finite-horizon normalization or optimality arguments in full detail,
- task-generation semantics,
- busy-window, processor-demand, or fairness analysis,
- operational traces or OS-level state machines.

Those belong respectively to:

- `design/Semantics.md`
- `design/Uniprocessor.md` and `design/Multicore.md`
- `design/GenericUniprocessorOptimality.md` as the detailed supplemental note
- `design/TaskModels.md`
- `design/Analysis.md`
- `design/Operational.md`

## Extension points

The current abstraction layer is intentionally prepared for:

- richer candidate sources, including partitioning, affinity, and prefix-dependent visibility,
- additional declarative-to-executable refinement statements,
- future multicore local-choice interfaces beyond the current top-`m` design,
- schedule-facing targets for later operational refinement work.

Extensions should preserve the separation between abstraction objects and the policy or analysis theories that consume them.

## File map

- `theories/Abstractions/SchedulingAlgorithm/Interface.v`
  Core single-CPU executable choice interface.
- `theories/Abstractions/SchedulingAlgorithm/Lemmas.v`
  Constructive generic consequences of the interface.
- `theories/Abstractions/SchedulingAlgorithm/ClassicalLemmas.v`
  Classical convenience lemmas kept separate from the constructive core.
- `theories/Abstractions/SchedulingAlgorithm/EnumCandidates.v`
  Standard finite constant candidate enumeration.
- `theories/Abstractions/SchedulingAlgorithm/SchedulerBridge.v`
  Standard bridge from a local single-CPU algorithm to a scheduler relation.
- `theories/Abstractions/SchedulingAlgorithm/TopMInterface.v`
  Generic top-`m` local-choice abstraction for multicore scheduling.
- `theories/Abstractions/SchedulingAlgorithm/TopMSchedulerBridge.v`
  Bridge from top-`m` local choice to multicore scheduler semantics.
- `theories/Abstractions/Scheduler/Interface.v`
  Scheduler relation and schedulability predicates.
- `theories/Abstractions/Scheduler/Validity.v`
  Declarative policy-respecting schedule predicates.
- `theories/Uniprocessor/Generic/SchedulingAlgorithmCanonicalBridge.v`
  Generic chooser-matching predicates for schedule canonicality on one step or a prefix.

## Summary

The abstraction layer defines the reusable interfaces that connect semantic schedules to local choice and scheduler admission.

Its core value is separation: schedules, local algorithms, candidate sources, declarative policies, and chooser-matching bridges remain distinct. That structure makes later policy, refinement, and analysis developments easier to state and reuse.
