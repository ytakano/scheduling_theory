From RocqSched Require Export TaskModels.Periodic.PeriodicEDFAnalysisEntryPoints.
From RocqSched Require Export TaskModels.Periodic.PeriodicConcreteAnalysis.
From RocqSched Require Export TaskModels.Periodic.PeriodicLLFBridge.
From RocqSched Require Export TaskModels.Periodic.PeriodicLLFAnalysisBridge.
From RocqSched Require Export TaskModels.Periodic.PeriodicLLFPrefixCoherence.
From RocqSched Require Export TaskModels.Periodic.PeriodicLLFInfiniteBridge.

(** * Stable public entry points for idealized periodic LLF analysis

    This file is the canonical downstream import for the current
    periodic LLF schedulability-analysis wrapper layer.

    Public theorem families exposed here:
    - the packaged periodic EDF idealized-analysis inventory
    - periodic LLF finite-horizon optimality wrappers
    - `periodic_llf_schedulable_by_on` as the canonical infinite-time
      window-DBF schedulability API
    - `periodic_llf_schedulable_by_classical_dbf_on` as the explicit
      zero-offset classical-DBF convenience wrapper
    - `periodic_llf_schedulable_by_window_dbf_on` as the explicit
      window-DBF alias
    - bounded finite-horizon concrete DBF/window-DBF checkers
    - scalar cutoff helpers for infinite zero-offset classical DBF proofs
    - infinite-time periodic LLF candidate/coherence interfaces
    - infinite-time generated-LLF no-miss / feasible / schedulable wrappers
    - infinite-time zero-offset classical-DBF corollaries
    - explicit bridge-first APIs that keep
      `periodic_edf_busy_prefix_bridge` in the public assumptions

    Not part of this layer:
    - legacy compatibility wrappers
    - weakened APIs that auto-supply `no_carry_in`
    - future sporadic / jittered / delay-aware analysis wrappers *)
