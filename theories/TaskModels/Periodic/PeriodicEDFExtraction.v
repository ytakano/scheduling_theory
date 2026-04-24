From Stdlib Require Extraction.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFExtractionDecision.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFExtractionTypes.

Extraction Language Haskell.

Extraction "extracted/haskell/PeriodicEDFSchedulability.hs"
  ExtractedPeriodicTask
  edf_schedulability_decide
  edf_schedulability_counterexample.
