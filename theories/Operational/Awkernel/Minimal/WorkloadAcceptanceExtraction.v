From Stdlib Require Extraction.
From RocqSched Require Import Operational.Awkernel.Minimal.CapturedTraceSyntax.
From RocqSched Require Import Operational.Awkernel.Minimal.WorkloadAcceptance.
From RocqSched Require Import Operational.Awkernel.Minimal.WorkloadSchedulerFacing.

Extraction Language Haskell.

Extraction "extracted/haskell/AwkernelWorkloadAcceptance.hs"
  AwkernelTaskTraceKind
  AwkernelTaskPolicy
  AwkernelTaskTraceEntry
  AwkernelSchedTraceEntry
  awk_workload_accepts_sched_trace
  task_trace_all_global_fifo_policyb
  first_non_global_fifo_task_policy_index
  first_non_fifo_sched_trace_index
  first_non_scheduler_relation_sched_trace_index
  awk_workload_accepts_global_fifo_sched_trace
  awk_workload_accepts_global_fifo_scheduler_relation_sched_trace.
