From RocqSched Require Export Analysis.Multicore.ProcessorSupply.
From RocqSched Require Export Analysis.Multicore.Interference.
From RocqSched Require Export Multicore.Global.GlobalEntryPoints.

(** * Stable public entry points for multicore global analysis

    This file is the canonical downstream import for the current
    multicore global-analysis theorem layer.

    Public theorem families exposed here:
    - machine-supply equalities and capacity bounds
    - interval full-supply consequences
    - covering-list interference lemmas
    - global EDF / LLF analysis-facing bridge facts

    Not part of this layer:
    - helper lemmas internal to processor-supply or interference proofs
    - future fairness / tardiness APIs
    - delay-aware or OS-operational refinements *)
