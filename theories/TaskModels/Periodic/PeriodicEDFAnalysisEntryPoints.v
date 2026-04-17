From RocqSched Require Export Analysis.Uniprocessor.BusyWindowSearch.
From RocqSched Require Export Analysis.Uniprocessor.EDFProcessorDemand.
From RocqSched Require Export TaskModels.Periodic.PeriodicWindowDemandBound.
From RocqSched Require Export TaskModels.Periodic.PeriodicClassicDBF.
From RocqSched Require Export TaskModels.Periodic.PeriodicConcreteAnalysis.
From RocqSched Require Export TaskModels.Periodic.PeriodicEDFBridge.
From RocqSched Require Export TaskModels.Periodic.PeriodicEDFClassicalBridge.
From RocqSched Require Export TaskModels.Periodic.PeriodicEDFPrefixCoherence.
From RocqSched Require Export TaskModels.Periodic.PeriodicEDFInfiniteBridge.

(** * Stable public entry points for idealized periodic EDF analysis

    This file is the canonical downstream import for the current
    periodic EDF processor-demand / busy-prefix theorem layer.

    Public theorem families exposed here:
    - busy-prefix witness search facts
    - EDF processor-demand bridge facts
    - periodic window-DBF bridge facts
    - infinite-time periodic EDF candidate/coherence interfaces
    - infinite-time generated-EDF no-miss / feasible wrappers
      over the weaker no-carry-in bridge interface
    - `periodic_edf_schedulable_by_on` as the canonical infinite-time
      window-DBF schedulability API
    - `periodic_edf_schedulable_by_classical_dbf_on` as the explicit
      zero-offset classical-DBF convenience wrapper
    - `periodic_edf_schedulable_by_window_dbf_on` as the explicit
      window-DBF alias
    - bounded finite-horizon concrete DBF/window-DBF checkers
    - scalar cutoff helpers for infinite zero-offset classical DBF proofs
    - finite- and infinite-time zero-offset classical-DBF corollaries with
      explicit busy-prefix or no-carry-in bridges
    - periodic EDF no-miss / feasible-schedule / schedulable-by-on wrappers
    - finite generated-EDF wrappers that internalize
      `start_before_release` and keep only
      `periodic_edf_busy_prefix_no_carry_in_bridge` public,
      with downstream concrete proofs expected to use local idle-slot facts
      whenever they can avoid full busy-prefix case splits

    Not part of this layer:
    - legacy compatibility wrappers
    - unpackaged busy-prefix interfaces
    - generated-EDF auto-derivation of `no_carry_in`
    - future sporadic / jittered generalizations
    - delay-aware or OS-operational analysis *)
