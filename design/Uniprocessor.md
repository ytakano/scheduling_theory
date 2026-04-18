# Uniprocessor

## Scope

This document describes the uniprocessor specialization layer.

Its scope is:

- `theories/Uniprocessor/Core/*`
- `theories/Uniprocessor/Generic/*`
- `theories/Uniprocessor/Policies/*`

This layer specializes the generic scheduler abstractions to single-CPU scheduling and organizes policy-specific theorem families on top of that specialization.

## Purpose of the Uniprocessor layer

The uniprocessor layer explains how single-CPU scheduling theory is structured in the repository.

Its responsibilities are:

- packaging single-CPU scheduler interfaces and facts,
- exposing generic finite-prefix and canonicalization infrastructure,
- organizing policy modules such as EDF, LLF, FIFO, and RR,
- proving uniprocessor policy-specific theorems without collapsing them into the abstraction layer.

## Core concepts and guarantees

The layer is organized into three parts.

`Uniprocessor/Core`
- basic single-CPU scheduler interfaces and local lemmas used by policy modules

`Uniprocessor/Generic`
- finite-prefix schedule witnesses
- chooser-matching canonicalization support
- normalization and finite-optimality skeletons shared across policies

`Uniprocessor/Policies`
- concrete policy modules and policy-facing theorem families
- EDF and LLF optimality pipelines
- FIFO and RR wrapper-style policy developments
- common metric-chooser utilities for reusable policy organization

The key architectural point is that the generic pipeline owns:

- canonicalization,
- local repair interfaces,
- normalization,
- finite-horizon scheduler-witness construction.

Policy modules then supply the policy-specific ingredients required by that pipeline.

For the detailed mechanics of horizon, canonicality, repair, and normalization, the primary supplemental note is:

- `design/GenericUniprocessorOptimality.md`

This document only summarizes that pipeline and does not duplicate its full explanation.

## Public entry points

The stable public entry points for this layer are:

- `theories/Uniprocessor/Core/UniSchedulerInterface.v`
- `theories/Uniprocessor/Generic/SchedulingAlgorithmCanonicalBridge.v`
- `theories/Uniprocessor/Generic/SchedulingAlgorithmNormalization.v`
- `theories/Uniprocessor/Generic/ScheduleTruncationPreservation.v`
- `theories/Uniprocessor/Generic/SchedulingAlgorithmOptimalitySkeleton.v`
- `theories/Uniprocessor/Policies/EDF.v`
- `theories/Uniprocessor/Policies/EDFOptimality.v`
- `theories/Uniprocessor/Policies/LLF.v`
- `theories/Uniprocessor/Policies/LLFOptimality.v`
- `theories/Uniprocessor/Policies/FIFO.v`
- `theories/Uniprocessor/Policies/RoundRobin.v`
- `theories/Uniprocessor/Policies/Common/MetricChooser.v`

In practice:

- downstream generic work should import the `Generic/*` modules
- downstream policy work should import the relevant policy module or optimality wrapper

## Design boundaries

This layer includes:

- single-CPU scheduler specialization,
- generic canonicalization and finite-optimality infrastructure for single-CPU policies,
- concrete policy modules and local policy theorems,
- horizon-bounded witness construction for uniprocessor policy results.

This layer does not include:

- the core meaning of schedules,
- reusable scheduler interfaces in their most general form,
- interval analysis as a primary concern,
- task-generation semantics,
- operational or implementation-facing scheduler traces.

Those belong respectively to:

- `design/Semantics.md`
- `design/Abstractions.md`
- `design/Analysis.md`
- `design/TaskModels.md`
- `design/Operational.md`

## Extension points

The current design is intended to support:

- new single-CPU policies that reuse the generic canonicalization and witness pipeline,
- richer metric-based chooser families,
- additional finite-optimality-ready policy instantiations,
- stronger public theorem inventories with stable naming across task-model lifts.

New policy work should prefer plugging into the generic pipeline rather than reproducing horizon and normalization arguments inside each policy file.

## File map

- `theories/Uniprocessor/Core/UniSchedulerInterface.v`
  Single-CPU scheduler interface layer.
- `theories/Uniprocessor/Core/UniSchedulerLemmas.v`
  Foundational single-CPU scheduler lemmas.
- `theories/Uniprocessor/Generic/FinitePrefixScheduleWitness.v`
  Finite-prefix witness infrastructure.
- `theories/Uniprocessor/Generic/SchedulingAlgorithmCanonicalBridge.v`
  Generic chooser-matching predicates for single-CPU canonicality.
- `theories/Uniprocessor/Generic/SchedulingAlgorithmNormalization.v`
  Reusable normalization interface and proof layer.
- `theories/Uniprocessor/Generic/ScheduleTruncationPreservation.v`
  Finite-horizon truncation preservation lemmas used by the generic optimality pipeline.
- `theories/Uniprocessor/Generic/SchedulingAlgorithmOptimalitySkeleton.v`
  Shared finite-optimality skeleton.
- `theories/Uniprocessor/Policies/Common/MetricChooser.v`
  Common metric-based chooser organization.
- `theories/Uniprocessor/Policies/Common/MetricChooserLemmas.v`
  Supporting metric-chooser lemmas.
- `theories/Uniprocessor/Policies/EDF*.v`
  EDF policy and finite-optimality theorem family.
- `theories/Uniprocessor/Policies/LLF*.v`
  LLF policy and finite-optimality theorem family.
- `theories/Uniprocessor/Policies/FIFO.v`
  FIFO policy wrapper layer.
- `theories/Uniprocessor/Policies/RoundRobin.v`
  Round-robin policy wrapper layer.

## Summary

The uniprocessor layer packages single-CPU specialization plus policy-specific theorem families.

Its main architectural rule is to keep shared canonicalization and finite-horizon structure in `Generic/*`, while policy modules contribute only policy-specific ingredients and wrappers. Detailed canonicalization mechanics remain documented in the supplemental uniprocessor optimality note.
