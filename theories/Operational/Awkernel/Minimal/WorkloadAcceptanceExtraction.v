From Stdlib Require Extraction.
From RocqSched Require Import Operational.Awkernel.Minimal.CapturedTraceSyntax.
From RocqSched Require Import Operational.Awkernel.Minimal.WorkloadAcceptance.
From RocqSched Require Import Operational.Awkernel.Minimal.WorkloadSchedulerFacing.

Extraction Language Haskell.

Extraction "/scheduling_theory/extracted/haskell/AwkernelWorkloadAcceptance.hs"
  AwkernelTaskTraceKind
  AwkernelTaskTraceEntry
  AwkernelSchedTraceEntry
  awk_workload_accepts_sched_trace
  first_non_fifo_sched_trace_index
  first_non_scheduler_relation_sched_trace_index
  awk_workload_accepts_global_fifo_sched_trace
  awk_workload_accepts_global_fifo_scheduler_relation_sched_trace.
