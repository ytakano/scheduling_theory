From Stdlib Require Extraction.
From RocqSched Require Import Operational.Awkernel.Minimal.CapturedTraceSyntax.
From RocqSched Require Import Operational.Awkernel.Minimal.WorkloadAcceptance.
From RocqSched Require Import Operational.Awkernel.Minimal.WorkloadCandidateTable.

Extraction Language Haskell.

Extraction "/scheduling_theory/extracted/haskell/AwkernelWorkloadAcceptance.hs"
  TaskLifecycleKind
  TaskLifecycleRecord
  awk_workload_accepts_trace
  candidate_table_matches_rows.
