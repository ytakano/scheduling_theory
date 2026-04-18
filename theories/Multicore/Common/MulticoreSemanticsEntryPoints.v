From RocqSched Require Export Multicore.Common.MultiCoreBase.
From RocqSched Require Export Multicore.Common.Admissibility.
From RocqSched Require Export Multicore.Common.AdmissibleCandidateSource.
From RocqSched Require Export Multicore.Common.TopMAdmissibilityBridge.
From RocqSched Require Export Multicore.Common.ServiceFacts.
From RocqSched Require Export Multicore.Common.CompletionFacts.
From RocqSched Require Export Multicore.Common.RemainingCostFacts.
From RocqSched Require Export Multicore.Common.LaxityFacts.

(** * Stable public entry points for multicore common semantics

    This file is the canonical downstream import for the reusable
    policy-independent multicore semantic theorem layer.

    Public theorem families exposed here:
    - per-CPU schedule projection and multicore running/full vocabulary
    - admissibility and admissibility-aware candidate-source structure
    - canonical set-level top-`m` semantic boundary theorems
    - migration-aware service, completion, remaining-cost, and laxity facts

    Not part of this layer:
    - global EDF / LLF policy wrappers
    - partitioned scheduler composition
    - interval analysis and fairness packaging *)
