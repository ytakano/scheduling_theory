From Stdlib Require Extraction.
From RocqSched Require Import Operational.Awkernel.Minimal.CapturedTraceSyntax.
From RocqSched Require Import Operational.Awkernel.Minimal.WorkloadAcceptance.

Extraction Language Haskell.

Extraction "/scheduling_theory/extracted/haskell/AwkernelWorkloadAcceptance.hs"
  AwkernelTaskTraceKind
  AwkernelTaskTraceEntry
  AwkernelSchedTraceEntry
  awk_workload_accepts_sched_trace.
