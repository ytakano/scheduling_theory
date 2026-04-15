From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
Import ListNotations.

(* Minimal operational scheduler state for trace-to-schedule projection.
   This layer intentionally records only the proof-relevant scheduler view:
   per-CPU current jobs, a runnable-job view, and pending reschedule flags. *)
Record OpState : Type := mkOpState {
  op_current : CPU -> option JobId;
  op_runnable : list JobId;
  op_need_resched : CPU -> bool;
}.

Definition op_current_job (st : OpState) (c : CPU) : option JobId :=
  op_current st c.

Definition op_job_running (st : OpState) (j : JobId) : Prop :=
  exists c, op_current st c = Some j.

Definition op_runnable_set_like (st : OpState) : Prop :=
  NoDup (op_runnable st).

Definition op_no_duplication (m : nat) (st : OpState) : Prop :=
  forall j c1 c2,
    c1 < m -> c2 < m ->
    op_current st c1 = Some j ->
    op_current st c2 = Some j ->
    c1 = c2.
