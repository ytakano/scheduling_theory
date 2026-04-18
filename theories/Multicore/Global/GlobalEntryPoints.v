From RocqSched Require Export Multicore.Common.MultiCoreBase.
From RocqSched Require Export Multicore.Common.AdmissibleCandidateSource.
From RocqSched Require Export Abstractions.SchedulingAlgorithm.TopMInterface.
From RocqSched Require Export Abstractions.SchedulingAlgorithm.TopMSchedulerBridge.
From RocqSched Require Export Multicore.Common.TopMAdmissibilityBridge.
From RocqSched Require Export Multicore.Global.GlobalEDF.
From RocqSched Require Export Multicore.Global.GlobalLLF.

(** * Stable public entry points for the global theorem layer

    This file is the canonical downstream import for the reusable global
    multicore theorem layer.

    Public theorem families exposed here:
    - generic top-m scheduler bridge lemmas for validity, no-duplication,
      and idle-outside-range
    - admissibility-aware top-m bridge lemmas
    - set-level top-m semantic boundary theorems
    - EDF-specific thin wrappers
    - LLF-specific thin wrappers

    Not part of this layer:
    - analysis theorems
    - fairness / bounded-waiting theorems
    - OS-level operational semantics *)
