# Multicore

## Scope

This document describes the multicore specialization layer.

Its scope is:

- `theories/Multicore/Common/*`
- `theories/Multicore/Partitioned/*`
- `theories/Multicore/Global/*`

This layer packages multicore-specific structure and theorem layers for both partitioned and global scheduling.

## Purpose of the Multicore layer

The multicore layer explains how the repository specializes the general framework to multiple CPUs.

Its role is to separate:

- policy-independent multicore schedule facts,
- partitioned multicore scheduler construction,
- global top-`m` scheduling structure and policy wrappers.

This layer owns multicore structure. It does not own most fairness or tardiness analysis, even when those analyses consume multicore theorem layers.

## Core concepts and guarantees

The layer is organized into three parts.

`Multicore/Common`
- multicore base views such as per-CPU projection
- set-level running/full vocabulary for global schedules
- schedule-level placement invariants for admissible CPUs
- bundled semantic validity for common multicore clients
- service, completion, remaining-cost, and laxity facts specialized to multicore schedules
- machine supply semantic basics plus machine-full / idle wrappers for downstream clients
- admissibility and candidate-source infrastructure
- abstract migration facts that preserve admissibility under placement respect
- top-`m` metric, admissibility, placement-aware, selection-boundary, and interval full-supply bridges

`Multicore/Partitioned`
- static assignment of jobs to CPUs
- composition of local single-CPU schedulers into a multicore schedule
- partitioned validity, service localization, and schedulability bridges
- partitioned policy lifts and task-model lifts

`Multicore/Global`
- global top-`m` scheduler structure
- policy wrappers for global EDF and global LLF
- stable entry-point packaging for the reusable global theorem layer

The main multicore-specific abstraction boundary is top-`m` scheduling:

- global selection chooses up to `m` eligible jobs,
- admissibility, placement, and no-duplication properties ensure sound multicore scheduling structure,
- selected jobs may additionally be constrained by a CPU-position-aware placement boundary,
- the canonical public semantic boundary is a set-level statement that the
  running set is selected from a subset and any missing subset job implies a
  machine-full state,
- policy wrappers instantiate that shared theorem layer.

## Public entry points

The canonical public entry points for this layer are:

- `theories/Multicore/Common/MulticoreSemanticsEntryPoints.v`
- `theories/Multicore/Global/GlobalEntryPoints.v`
- `theories/Multicore/Partitioned/PartitionedEntryPoints.v`

Important supporting modules include:

- `theories/Multicore/Common/MultiCoreBase.v`
- `theories/Multicore/Common/MulticoreSemanticsEntryPoints.v`
- `theories/Multicore/Common/ServiceFacts.v`
- `theories/Multicore/Common/CompletionFacts.v`
- `theories/Multicore/Common/RemainingCostFacts.v`
- `theories/Multicore/Common/LaxityFacts.v`
- `theories/Multicore/Common/ValidityFacts.v`
- `theories/Multicore/Common/Admissibility.v`
- `theories/Multicore/Common/AdmissibleCandidateSource.v`
- `theories/Multicore/Common/TopMAdmissibilityBridge.v`
- `theories/Multicore/Common/TopMSelectionFacts.v`
- `theories/Multicore/Partitioned/Partitioned.v`
- `theories/Multicore/Partitioned/PartitionedCompose.v`
- `theories/Multicore/Global/GlobalEDF.v`
- `theories/Multicore/Global/GlobalLLF.v`

## Design boundaries

This layer includes:

- multicore semantic specializations and structural theorem layers,
- partitioned scheduling and composition infrastructure,
- global top-`m` scheduling structure,
- multicore policy wrappers and stable theorem-layer entry points.

This layer does not include:

- the core meaning of schedules,
- generic scheduler interfaces that are not multicore-specific,
- fairness, workload absorption, and tardiness analysis as the primary abstraction boundary,
- implementation-facing operational traces.

Those belong respectively to:

- `design/Semantics.md`
- `design/Abstractions.md`
- `design/Analysis.md`
- `design/Operational.md`

In particular, fairness and related contradiction-style interval arguments should primarily live in `Analysis`, even when they are built on top of the theorem layers exported from `Multicore`.

## Extension points

The current multicore layer is designed to support:

- additional partitioned wrappers and local-scheduler composition results,
- more global top-`m` policies,
- stronger migration-aware service and completion facts,
- clearer public theorem inventories for downstream multicore clients.

New multicore work should keep structural scheduling facts here and move interval-analysis consequences upward into `Analysis`.

## File map

- `theories/Multicore/Common/MultiCoreBase.v`
  Core multicore schedule views, projections, and set-level running/full vocabulary.
- `theories/Multicore/Common/MulticoreSemanticsEntryPoints.v`
  Canonical downstream import for the policy-independent multicore semantic
  theorem layer.
- `theories/Multicore/Common/ServiceFacts.v`
  Multicore service-accounting facts plus machine-supply semantic basics and
  machine-full to saturated-supply bridges.
- `theories/Multicore/Common/ValidityFacts.v`
  Bundled semantic-validity theorem layer for policy-independent multicore clients.
- `theories/Multicore/Common/CompletionFacts.v`
  Completion facts specialized to multicore schedules, including standard
  eligible/admissible non-running to machine-full consequences.
- `theories/Multicore/Common/RemainingCostFacts.v`
  Remaining-cost lemmas for multicore settings, including step-bound and
  monotonicity facts for interval clients.
- `theories/Multicore/Common/LaxityFacts.v`
  Multicore laxity infrastructure, including fairness-facing step bounds.
- `theories/Multicore/Common/Admissibility.v`
  Admissibility structure for multicore scheduling.
- `theories/Multicore/Common/PlacementFacts.v`
  Schedule-level placement invariants for admissible CPUs.
- `theories/Multicore/Common/MigrationFacts.v`
  Abstract migration facts layered over placement respect.
- `theories/Multicore/Common/AdmissibleCandidateSource.v`
  Candidate-source discipline and admissibility-spec layering for multicore settings.
- `theories/Multicore/Common/AffinityFacts.v`
  Affinity-facing supporting facts.
- `theories/Multicore/Common/RunningSetFacts.v`
  Public wrappers connecting running/full vocabulary to machine-supply equalities.
- `theories/Multicore/Common/TopMMetricChooser.v`
  Shared top-`m` metric-based chooser layer.
- `theories/Multicore/Common/TopMMetricFacts.v`
  Supporting top-`m` metric facts.
- `theories/Multicore/Common/TopMAdmissibilityBridge.v`
  Top-`m` admissibility-aware bridge layer plus the canonical set-level selection boundary.
- `theories/Multicore/Common/TopMPlacementFacts.v`
  Top-`m` CPU-position-aware placement boundary and schedule-respect bridge.
- `theories/Multicore/Common/TopMSelectionFacts.v`
  Generic top-`m` selection consequences, including interval full-supply theorems.
- `theories/Multicore/Partitioned/Partitioned.v`
  Core partitioned schedule definitions and theorems.
- `theories/Multicore/Partitioned/PartitionedCompose.v`
  Composition from per-CPU local schedulers to multicore schedules.
- `theories/Multicore/Partitioned/PartitionedEntryPoints.v`
  Canonical downstream import for the partitioned theorem layer.
- `theories/Multicore/Global/GlobalEDF.v`
  Global EDF wrapper layer over the top-`m` theorem infrastructure.
- `theories/Multicore/Global/GlobalLLF.v`
  Global LLF wrapper layer over the top-`m` theorem infrastructure.
- `theories/Multicore/Global/GlobalEntryPoints.v`
  Canonical downstream import for the global theorem layer, including set-level
  top-`m` selection theorems and their supporting vocabulary.

## Summary

The multicore layer is the structural multicore theorem layer of the project.

It packages common multicore facts plus partitioned and global scheduling developments, with top-`m` scheduling as the key global abstraction. Common now includes bundled validity, placement/migration invariants, machine-full wrappers, and interval full-supply consequences; analysis packages contradiction and fairness clients on top of that boundary rather than feeding dependencies back into it.
