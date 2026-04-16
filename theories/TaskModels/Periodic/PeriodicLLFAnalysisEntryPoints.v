From RocqSched Require Export TaskModels.Periodic.PeriodicEDFAnalysisEntryPoints.
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
    - periodic LLF schedulable-by-on wrappers derived from
      window-DBF and zero-offset classical DBF assumptions
    - infinite-time periodic LLF candidate/coherence interfaces
    - infinite-time generated-LLF no-miss / feasible / schedulable wrappers
    - explicit bridge-first APIs that keep
      `periodic_edf_busy_prefix_bridge` in the public assumptions

    Not part of this layer:
    - legacy compatibility wrappers
    - weakened APIs that auto-supply `no_carry_in`
    - future sporadic / jittered / delay-aware analysis wrappers *)
