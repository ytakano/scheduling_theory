From RocqSched Require Export TaskModels.Jitter.JitteredPeriodicWindowDemandBound.
From RocqSched Require Export TaskModels.Jitter.JitteredPeriodicEDFWindowBridge.
From RocqSched Require Export TaskModels.Jitter.JitteredPeriodicEDFInfiniteBridge.

(** * Stable public entry points for jittered-periodic EDF analysis

    This layer exposes the release-jitter window DBF definitions together with
    the generated EDF schedule interfaces.  The current infinite wrapper keeps
    finite-prefix feasibility / no-carry-in discharge explicit; cutoff checkers
    and extraction-facing certificates are planned as later layers. *)

