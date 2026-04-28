# Architectural Layering

This document gives the global overview of the repository's intended
architecture.

Its purpose is to show dependency direction, semantic boundaries, and
placement rules for new developments. Layer-local detail belongs in the
dedicated design documents referenced below.

## Purpose of the architecture

The central design principle of the project is:

> define schedule semantics first, separate executable scheduling logic from
> semantic schedule admission, and connect implementation-facing executions to
> analysis-facing schedules through explicit semantic and reasoning boundaries.

This keeps proofs reusable across:

- scheduler policies,
- task models,
- machine models,
- refinement styles,
- analysis clients,
- executable checkers and trace-based validation tools.

## Scheduler semantic layers

The project distinguishes three scheduler semantic layers.

```text
OS-level scheduler operational semantics
        produces
          ↓
Trace semantics
        projects to / reconstructs
          ↓
Schedule semantics
        supports
          ↓
Analysis theory
````

The ordering above follows the execution-to-analysis flow. In the repository,
the proof dependency usually starts from schedule semantics and then adds trace
and operational connections on top.

### Schedule semantics

Schedule semantics is the mathematical model used by analysis and policy
specifications.

It provides objects such as:

```text
Time × CPU → option Job
```

and predicates for execution, service, completion, readiness, pending jobs,
deadline misses, validity, feasibility, restriction, truncation, and prefix
reasoning.

This is the semantic basis of schedulability analysis.

### Trace semantics

Trace semantics describes observable scheduling events.

It is the bridge between implementation-facing logs and schedule-level
reasoning. It hosts normalized events, trace well-formedness, trace-to-schedule
projection, and reconstruction correctness.

Typical trace events include:

* release,
* dispatch,
* preemption,
* completion,
* timer events,
* wakeup events,
* migration events,
* IPI-related events.

Trace semantics should remain independent of any one concrete OS log format.
Concrete OS adapters should normalize their logs into this layer.

### OS-level scheduler operational semantics

OS-level scheduler operational semantics describes scheduler execution as a
state-transition system.

It models implementation-facing mechanisms such as:

* run queues,
* dispatch,
* wakeup,
* timer handling,
* migration,
* IPI-triggered scheduling,
* delayed handoff,
* scheduler state updates.

This layer explains how traces are produced. Its current scope is a minimal
operational projection slice, not a full OS semantics.

## Reasoning theories

Analysis and refinement are not scheduler semantic layers in the same sense as
schedule, trace, and operational semantics. They are reasoning theories built
around the semantic stack.

```text
                       Analysis theory
        proves timing and schedulability properties
                              ↑
                        Schedule semantics
                              ↑
              projection / reconstruction correctness
                              |
                         Trace semantics
                              ↑
                  trace generation correctness
                              |
          OS-level scheduler operational semantics

        Refinement theory = correctness of the arrows
```

### Analysis theory

The analysis theory proves timing and schedulability properties over schedule
semantics.

It hosts interval-based reasoning such as:

* busy intervals,
* busy windows,
* busy prefixes,
* processor demand,
* processor supply,
* interference,
* workload absorption,
* no-deadline-miss theorems,
* bounded tardiness,
* fairness-facing packaged entry points.

For uniprocessor policy analysis, this theory may also expose:

* finite-horizon witness / bridge theorems,
* infinite-time wrappers that reuse finite-horizon bridge theorems prefix-wise,
* classical corollaries extracted from richer window-aware statements,
* policy-specific feasibility bridges such as EDF processor-demand and LLF
  laxity results,
* task-model-facing packaged entry points that expose bridge-first EDF
  classical corollaries, infinite EDF/LLF wrappers, and LLF schedulability
  wrappers on top of EDF feasibility bridges.

When a classical corollary depends on a stronger schedule-local bridge
(`no_carry_in`, backlog exclusion, or chosen busy-prefix properties), keep the
corollary bridge-first instead of weakening the API beyond what the current
proof layer justifies.

### Refinement theory

The refinement theory connects semantic layers and implementation-facing
objects.

It proves relationships such as:

* executable chooser behavior implies declarative policy compliance,
* generated schedules are admitted by schedule semantics,
* traces project to schedules correctly,
* operational executions produce well-formed traces,
* concrete or implementation-facing schedulers refine abstract scheduler
  specifications.

In short, refinement is the theory of the arrows between semantic objects, not
a separate semantic object by itself.

## Repository dependency direction

The intended logical dependency direction is:

```text
Foundation
  -> Semantics
  -> Abstractions
  -> Refinement
  -> Analysis
  -> { Uniprocessor, Multicore, Operational, TaskModels }
  -> Examples
```

This is an architectural rule, not a claim that every directory forms a perfect
chain.

In particular:

* `Semantics` contains the schedule-level semantic basis.
* `Operational` contains implementation-facing state, trace, and operational
  projection material.
* `Analysis` is a reasoning theory over schedules.
* `Refinement` is a reasoning theory connecting executable, trace-level, and
  schedule-level objects.

New developments should preserve the dependency direction unless there is a
clear structural reason not to.

## Repository guide

### Foundation

The foundation layer fixes the base scalar types, minimal task/job records, raw
schedule carrier type, and small task-model-independent arithmetic facts.

It should remain a small shared vocabulary.

Primary document:

* `design/Foundation.md`

### Semantics

The semantics layer defines schedule semantics.

It specifies what schedules mean: execution, service, completion, readiness,
validity, feasibility, and the semantic effects of prefix, restriction,
truncation, and local transformations.

This layer is the bottom semantic basis for analysis-facing reasoning.

Primary document:

* `design/Semantics.md`

### Abstractions

The abstraction layer packages scheduler and scheduling-algorithm interfaces,
candidate sources, declarative policy views, and chooser-to-schedule bridges.

It separates executable scheduling logic from semantic schedule admission.

Primary document:

* `design/Abstractions.md`

Supplemental note:

* `design/SchedulingArchitecture.md`

### Refinement

The refinement theory connects executable or implementation-facing scheduling
objects to abstract policy specifications and semantic schedule admission.

It should host correctness theorems for:

* chooser-to-policy connections,
* executable-to-semantic schedule admission,
* trace-to-schedule projection,
* operational-to-trace generation,
* implementation-facing scheduler refinement.

Primary document:

* `design/Refinement.md`

### Analysis

The analysis theory hosts interval-based schedulability reasoning over schedule
semantics.

It should not define the basic meaning of schedules. Instead, it consumes
schedule semantics to prove timing properties such as processor-demand,
busy-window, interference, no-deadline-miss, feasibility, schedulability, and
bounded-tardiness results.

Primary document:

* `design/Analysis.md`

### Uniprocessor

The uniprocessor development specializes the generic interfaces to single-CPU
scheduling and policy-specific theorem families such as EDF, LLF, FIFO, and RR.

It may instantiate semantic, abstraction, refinement, and analysis theories for
single-CPU policies.

Primary document:

* `design/Uniprocessor.md`

Supplemental note:

* `design/GenericUniprocessorOptimality.md`

### Multicore

The multicore development specializes the framework to common multicore
semantics plus partitioned and global scheduling theorem families.

This includes reusable multicore semantic bundles, placement/migration
invariants, and policy-generic top-`m` selection consequences when they remain
independent of analysis-facing workload arguments.

Primary document:

* `design/Multicore.md`

### Operational

The operational development introduces implementation-facing states, traces,
and projection back into schedule semantics.

It covers the upper part of the scheduler semantic stack:

```text
OS-level scheduler operational semantics
        ↓
Trace semantics
        ↓
Schedule semantics
```

Its current scope is a minimal operational projection slice, not a full OS
semantics.

Primary document:

* `design/Operational.md`

### TaskModels

The task-model development defines how periodic, sporadic, and jitter-aware task
families generate jobs and how those generated job sets are exposed to policy
and analysis theories.

It should define generated job sets and task-model-specific assumptions without
collapsing them into scheduler semantics.

Primary document:

* `design/TaskModels.md`

### Examples

Example files are proof clients and regression-style usages of the public
theorem inventory.

They should consume stable semantic and reasoning boundaries rather than act as
hidden implementation layers.

## Placement rules for new files

When adding a new file, place it at the lowest architectural component whose
responsibility matches the concept.

Use these rules:

* if the file defines base scalar types, minimal task/job records, raw schedule
  carriers, or task-model-independent arithmetic facts, place it in
  `Foundation`
* if the file defines the meaning of schedules or schedule-derived predicates,
  place it in `Semantics`
* if it defines reusable scheduler, scheduling-algorithm, chooser, candidate
  source, or declarative policy interfaces, place it in `Abstractions`
* if it proves executable-to-spec, trace-to-schedule, operational-to-trace, or
  implementation-to-semantics relationships, place it in `Refinement`
* if it proves interval reasoning, demand/supply reasoning, interference bounds,
  or schedulability-analysis facts, place it in `Analysis`
* if it is policy-specific single-CPU theory, place it in `Uniprocessor`
* if it is multicore structure, partitioning, placement/migration invariants, or
  global top-`m` theorem work, place it in `Multicore`
* if it defines implementation-facing state, observable scheduler events,
  trace semantics, OS-level operational transitions, or projection invariants,
  place it in `Operational`
* if it defines generated job sets from task parameters, place it in
  `TaskModels`
* if it is only a proof client or regression-style usage of public theorems,
  place it in `Examples`

When a proof feels awkward, the default fix should be a cleaner interface or
helper lemma at the correct boundary, not collapsing the semantic and reasoning
components together.

## Naming convention

Use the term `semantic layer` only for semantic objects such as:

* schedule semantics,
* trace semantics,
* OS-level scheduler operational semantics.

Use `theory`, `component`, or `development` for reasoning-oriented parts such
as:

* analysis theory,
* refinement theory,
* checker correctness theory,
* task-model development,
* uniprocessor development,
* multicore development.

This avoids confusing semantic objects with theorems about those objects.

## Summary

`ArchitecturalLayering.md` is the map of the repository, not the full
specification of each component.

The detailed design notes live in the dedicated documents under `design/`.

This overview should stay short, stable, and focused on:

* scheduler semantic boundaries,
* reasoning-theory boundaries,
* dependency direction,
* file placement.
