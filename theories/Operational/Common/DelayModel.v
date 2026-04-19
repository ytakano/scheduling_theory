From Stdlib Require Import List Arith.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Operational.Common.Step.
Import ListNotations.

Inductive op_delay_source : Type :=
| DelayDispatch
| DelayWakeup
| DelayTimer
| DelayMigration
| DelayIPI
| DelayNonpreemptive.

Record op_delay_bounds : Type := mkOpDelayBounds {
  odb_dispatch : nat;
  odb_wakeup : nat;
  odb_timer : nat;
  odb_migration : nat;
  odb_ipi : nat;
  odb_nonpreemptive : nat;
}.

Definition delay_bound_of
    (B : op_delay_bounds) (src : op_delay_source) : nat :=
  match src with
  | DelayDispatch => odb_dispatch B
  | DelayWakeup => odb_wakeup B
  | DelayTimer => odb_timer B
  | DelayMigration => odb_migration B
  | DelayIPI => odb_ipi B
  | DelayNonpreemptive => odb_nonpreemptive B
  end.

Definition default_event_delay_sources (ev : OpEvent) : list op_delay_source :=
  match ev with
  | EvDispatch _ _ => [DelayDispatch]
  | EvPreempt _ _ _ => [DelayDispatch]
  | EvWakeup _ => [DelayWakeup]
  | EvRequestResched _ => []
  | EvHandleResched _ => [DelayIPI]
  | EvChoose _ _ => []
  | EvTick => [DelayTimer]
  | EvBlock _ => []
  | EvComplete _ => []
  end.
