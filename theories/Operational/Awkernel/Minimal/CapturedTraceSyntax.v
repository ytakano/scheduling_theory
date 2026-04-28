From Stdlib Require Import List Bool Arith Arith.PeanoNat.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Operational.Common.Step.
From RocqSched Require Import Operational.Awkernel.Minimal.MinimalProjection.
Import ListNotations.

Record AwkernelSchedTraceEntry : Type := mkAwkernelSchedTraceEntry {
  aste_event_id : nat;
  aste_cpu : CPU;
  aste_event : OpEvent;
  aste_current : option JobId;
  aste_runnable : list JobId;
  aste_need_resched : bool;
  aste_dispatch_target : option JobId;
  aste_worker_current : list (option JobId);
  aste_worker_need_resched : list bool;
  aste_worker_dispatch_target : list (option JobId);
}.

Definition sched_trace_primary_current
    (entry : AwkernelSchedTraceEntry) : option JobId :=
  aste_current entry.

Definition sched_trace_primary_need_resched
    (entry : AwkernelSchedTraceEntry) : bool :=
  aste_need_resched entry.

Definition sched_trace_primary_dispatch_target
    (entry : AwkernelSchedTraceEntry) : option JobId :=
  aste_dispatch_target entry.

Definition awk_sched_trace_entry_to_state
    (entry : AwkernelSchedTraceEntry) : AwkernelState :=
  mkAwkernelState
    (match aste_current entry with
     | Some j => fun c => if Nat.eqb c (aste_cpu entry) then Some j else None
     | None => fun _ => None
     end)
    (aste_runnable entry)
    (if aste_need_resched entry
     then fun c => if Nat.eqb c (aste_cpu entry) then true else false
     else fun _ => false)
    (match aste_dispatch_target entry with
     | Some j => fun c => if Nat.eqb c (aste_cpu entry) then Some j else None
     | None => fun _ => None
     end).
