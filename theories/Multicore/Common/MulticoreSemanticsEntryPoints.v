From RocqSched Require Export Multicore.Common.MultiCoreBase.
From RocqSched Require Export Multicore.Common.Admissibility.
From RocqSched Require Export Multicore.Common.AdmissibleCandidateSource.
From RocqSched Require Export Multicore.Common.PlacementFacts.
From RocqSched Require Export Multicore.Common.MigrationFacts.
From RocqSched Require Export Multicore.Common.TopMAdmissibilityBridge.
From RocqSched Require Export Multicore.Common.ValidityFacts.
From RocqSched Require Export Multicore.Common.TopMSelectionFacts.
From RocqSched Require Export Multicore.Common.ServiceFacts.
From RocqSched Require Export Multicore.Common.RunningSetFacts.
From RocqSched Require Export Multicore.Common.CompletionFacts.
From RocqSched Require Export Multicore.Common.RemainingCostFacts.
From RocqSched Require Export Multicore.Common.LaxityFacts.
From RocqSched Require Export Multicore.Common.TopMPlacementFacts.

(** * Stable public entry points for multicore common semantics

    This file is the canonical downstream import for the reusable
    policy-independent multicore semantic theorem layer.

    Public theorem families exposed here:
    - per-CPU schedule projection and multicore running/full vocabulary
    - bundled validity for multicore semantic clients
    - admissibility and admissibility-aware candidate-source structure
    - schedule-level placement and migration invariants
    - canonical set-level top-`m` semantic boundary theorems
    - placement-aware top-`m` boundary facts
    - generic top-`m` selection consequences up to interval full supply
    - running/full wrappers aligned with machine-supply equalities
    - migration-aware service, completion, remaining-cost, and laxity facts

    Not part of this layer:
    - global EDF / LLF policy wrappers
    - partitioned scheduler composition
    - interval analysis and fairness packaging *)
