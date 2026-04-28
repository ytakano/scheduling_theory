From RocqSched Require Export TaskModels.Jitter.JitteredPeriodicEDFFinalCertificateChecker.

(** Soundness facade for the first jittered EDF certificate layer.

    The DBF-only certificate soundness theorem is proved in the final checker
    file because the proof is exactly the checker-field decomposition plus the
    existing cutoff DBF soundness theorem.  This module reserves the planned
    soundness import path for later richer jittered certificates. *)
