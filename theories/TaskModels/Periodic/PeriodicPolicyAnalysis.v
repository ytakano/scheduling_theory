From RocqSched Require Import Foundation.Base.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFCertificate.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFExtractionTypes.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFFinalCertificateChecker.

(** Policy-facing boolean entry point for periodic feasibility certificates.

    The checked certificate is currently an EDF-generated feasibility witness.
    The policy argument is intentionally proof-facing: it selects the soundness
    theorem a downstream caller applies, not a different boolean checker. *)

Inductive PeriodicPolicy :=
| PolicyEDF
| PolicyLLF.

Definition check_periodic_policy_feasibility
    (_p : PeriodicPolicy)
    (ts : list ExtractedPeriodicTask)
    (cert : EDFInfiniteCert JobId)
    (sidecar : PeriodicFeasibilityCheckedSidecarCert) : bool :=
  check_periodic_feasibility_checked_sidecar_extracted ts cert sidecar.
