From Stdlib Require Import Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.

(* CPU 0 is busy at time t iff some job is scheduled there. *)
Definition cpu_busy_at
    (sched : Schedule) (t : Time) : Prop :=
  exists j, sched t 0 = Some j.

(* Every slot in [t1, t2) is busy on CPU 0. *)
Definition interval_busy
    (sched : Schedule) (t1 t2 : Time) : Prop :=
  forall t, t1 <= t < t2 -> cpu_busy_at sched t.

(* A busy interval is a non-empty busy interval. *)
Definition busy_interval
    (sched : Schedule) (t1 t2 : Time) : Prop :=
  t1 < t2 /\
  interval_busy sched t1 t2.

(* A maximal busy interval cannot be extended one slot to the left or right. *)
Definition maximal_busy_interval_from
    (sched : Schedule) (t1 t2 : Time) : Prop :=
  busy_interval sched t1 t2 /\
  (t1 = 0 \/ ~ cpu_busy_at sched (pred t1)) /\
  ~ cpu_busy_at sched t2.

(* CPU-level service supplied at time t on the single processor. *)
Definition cpu_service_at
    (sched : Schedule) (t : Time) : nat :=
  match sched t 0 with
  | Some _ => 1
  | None => 0
  end.

(* Cumulative processor supply in [0, t). *)
Fixpoint cumulative_cpu_service
    (sched : Schedule) (t : Time) : nat :=
  match t with
  | 0 => 0
  | S t' => cpu_service_at sched t' + cumulative_cpu_service sched t'
  end.

(* Processor supply in [t1, t2). *)
Definition cpu_service_between
    (sched : Schedule) (t1 t2 : Time) : nat :=
  cumulative_cpu_service sched t2 - cumulative_cpu_service sched t1.
