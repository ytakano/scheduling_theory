# Architectural Layering

This document gives the global overview of the repository's intended layering.

Its purpose is to show dependency direction and placement rules for new developments. Layer-local detail belongs in the dedicated layer documents referenced below.

## Purpose of layering

The central design principle of the project is:

> define schedule semantics first, separate executable scheduling logic from semantic schedule admission, and expose policy, analysis, task-model, multicore, and operational developments through explicit layer boundaries.

This keeps proofs reusable across:

- scheduler policies,
- task models,
- machine models,
- refinement styles,
- analysis clients.

## Dependency direction

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

This is an architectural rule, not a claim that every directory forms a perfect chain. New developments should preserve the direction unless there is a clear structural reason not to.

## Layer guide

### Foundation

The foundation layer fixes the base scalar types, minimal task/job records, and raw schedule carrier type. It should remain a small shared vocabulary.

Primary document:
- `design/Foundation.md`

### Semantics

The semantics layer defines what schedules mean: execution, service, completion, readiness, validity, feasibility, and the semantic effects of prefix, restriction, truncation, and local transformations.

Primary document:
- `design/Semantics.md`

### Abstractions

The abstraction layer packages scheduler and scheduling-algorithm interfaces, candidate sources, declarative policy views, and chooser-to-schedule bridges.

Primary document:
- `design/Abstractions.md`

Supplemental note:
- `design/SchedulingArchitecture.md`

### Refinement

The refinement layer connects executable or implementation-facing scheduling objects to abstract policy specifications and semantic schedule admission.

Primary document:
- `design/Refinement.md`

### Analysis

The analysis layer hosts interval-based schedulability reasoning such as busy intervals, busy windows, processor demand, processor supply, interference, workload absorption, and fairness-facing packaged entry points.

For uniprocessor policy analysis, this layer may also expose:

- finite-horizon witness / bridge theorems
- classical corollaries extracted from richer window-aware statements
- policy-specific feasibility bridges such as EDF processor-demand and LLF laxity results

When a classical corollary depends on a stronger schedule-local bridge
(`no_carry_in`, backlog exclusion, or chosen busy-prefix properties), keep the
corollary bridge-first instead of weakening the API beyond what the current
proof layer justifies.

Primary document:
- `design/Analysis.md`

### Uniprocessor

The uniprocessor layer specializes the generic interfaces to single-CPU scheduling and policy-specific theorem families such as EDF, LLF, FIFO, and RR.

Primary document:
- `design/Uniprocessor.md`

Supplemental note:
- `design/GenericUniprocessorOptimality.md`

### Multicore

The multicore layer specializes the framework to common multicore semantics plus partitioned and global scheduling theorem layers.

Primary document:
- `design/Multicore.md`

### Operational

The operational layer introduces implementation-facing state, traces, and projection back into schedule semantics. Its current scope is a minimal operational projection slice, not a full OS semantics.

Primary document:
- `design/Operational.md`

### TaskModels

The task-model layer defines how periodic, sporadic, and jitter-aware task families generate jobs and how those generated job sets are exposed to policy and analysis layers.

Primary document:
- `design/TaskModels.md`

### Examples

Example files are proof clients and regression-style usages of the public theorem inventory. They should consume stable layer boundaries rather than act as hidden implementation layers.

## Placement rules for new files

When adding a new file, place it at the lowest layer whose responsibility matches the concept.

Use these rules:

- if the file defines meaning of schedules or schedule-derived predicates, place it in `Semantics`
- if it defines reusable scheduler or chooser interfaces, place it in `Abstractions`
- if it proves executable-to-spec or implementation-to-semantics relationships, place it in `Refinement`
- if it proves interval reasoning or schedulability-analysis facts, place it in `Analysis`
- if it is policy-specific single-CPU theory, place it in `Uniprocessor`
- if it is multicore structure, partitioning, or global top-`m` theorem work, place it in `Multicore`
- if it defines implementation-facing states, traces, or projection invariants, place it in `Operational`
- if it defines generated job sets from task parameters, place it in `TaskModels`

When a proof feels awkward, the default fix should be a cleaner interface or helper lemma at the correct layer, not collapsing the layers together.

## Summary

`ArchitecturalLayering.md` is the map of the repository, not the full specification of each layer.

The detailed design notes now live in the dedicated layer documents under `design/`. This overview should stay short, stable, and focused on dependency direction and file placement.
