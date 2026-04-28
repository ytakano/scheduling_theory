From RocqSched Require Export TaskModels.Jitter.JitteredPeriodicWindowDemandBound.
From RocqSched Require Export TaskModels.Jitter.JitteredPeriodicEDFWindowBridge.
From RocqSched Require Export TaskModels.Jitter.JitteredPeriodicEDFInfiniteBridge.

(** * Stable public entry points for jittered-periodic EDF analysis

    This layer exposes the release-jitter window DBF definitions together with
    the generated EDF schedule interfaces.  Finite/infinite generated EDF
    prefix coherence is internalized for the current candidate source; the
    no-carry-in bridge remains an explicit analysis-side obligation.  Cutoff
    checkers and extraction-facing certificates are planned as later layers. *)
