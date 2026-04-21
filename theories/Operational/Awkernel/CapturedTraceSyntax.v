From Stdlib Require Import List Bool Arith Arith.PeanoNat.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Operational.Common.Step.
From RocqSched Require Import Operational.Awkernel.MinimalProjection.
Import ListNotations.

Record AwkernelCapturedRow : Type := mkAwkernelCapturedRow {
  acr_cpu : CPU;
  acr_event : OpEvent;
  acr_current : option JobId;
  acr_runnable : list JobId;
  acr_need_resched : bool;
  acr_dispatch_target : option JobId;
}.

Definition awk_row_to_state (row : AwkernelCapturedRow) : AwkernelState :=
  mkAwkernelState
    (match acr_current row with
     | Some j => fun c => if Nat.eqb c (acr_cpu row) then Some j else None
     | None => fun _ => None
     end)
    (acr_runnable row)
    (if acr_need_resched row
     then fun c => if Nat.eqb c (acr_cpu row) then true else false
     else fun _ => false)
    (match acr_dispatch_target row with
     | Some j => fun c => if Nat.eqb c (acr_cpu row) then Some j else None
     | None => fun _ => None
     end).
