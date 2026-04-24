From Stdlib Require Extraction.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFCertificate.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFExtractionDecision.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFExtractionTypes.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFFinalCertificateChecker.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFGeneratedPrefixChecker.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFWindowTransportChecker.

Extraction Language Haskell.

Extraction "extracted/haskell/PeriodicEDFSchedulability.hs"
  ExtractedPeriodicTask
  EDFPrefixCert
  EDFTransportClass
  EDFTransportCert
  EDFDBFCert
  EDFInfiniteCert
  EDFWindowTransportPairCert
  EDFWindowTransportTargetCert
  PeriodicEDFCheckedSidecarCert
  edf_schedulability_decide
  edf_schedulability_counterexample
  check_prefix_slots_match_generated_edf
  check_prefix_slots_match_generated_edf_fast
  check_periodic_edf_checked_sidecar_extracted.
