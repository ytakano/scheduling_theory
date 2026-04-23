From Stdlib Require Extraction.
From RocqSched Require Import Operational.Awkernel.CapturedTraceSyntax.
From RocqSched Require Import Operational.Awkernel.WorkloadAcceptance.

Extraction Language Haskell.

Extraction "/scheduling_theory/extracted/haskell/AwkernelWorkloadAcceptance.hs"
  TaskLifecycleKind
  TaskLifecycleRecord
  awk_workload_accepts_trace.
