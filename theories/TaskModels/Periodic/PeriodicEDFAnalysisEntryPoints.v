From RocqSched Require Export Analysis.Uniprocessor.BusyWindowSearch.
From RocqSched Require Export Analysis.Uniprocessor.EDFProcessorDemand.
From RocqSched Require Export TaskModels.Periodic.PeriodicWindowDemandBound.
From RocqSched Require Export TaskModels.Periodic.PeriodicEDFBridge.

(** * Stable public entry points for idealized periodic EDF analysis

    This file is the canonical downstream import for the current
    periodic EDF processor-demand / busy-prefix theorem layer.

    Public theorem families exposed here:
    - busy-prefix witness search facts
    - EDF processor-demand bridge facts
    - periodic window-DBF bridge facts
    - periodic EDF no-miss / feasible-schedule / schedulable-by-on wrappers

    Not part of this layer:
    - legacy compatibility wrappers
    - unpackaged busy-prefix interfaces
    - future sporadic / jittered generalizations
    - delay-aware or OS-operational analysis *)
