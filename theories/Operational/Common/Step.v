From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Operational.Common.State.
Import ListNotations.

Inductive OpEvent : Type :=
| EvWakeup (j : JobId)
| EvBlock (j : JobId)
| EvComplete (j : JobId)
| EvRequestResched (c : CPU)
| EvRecvIPI (c : CPU)
| EvChoose (c : CPU) (j : JobId)
| EvDispatch (c : CPU) (j : JobId)
| EvTick.

Definition add_runnable (j : JobId) (st : OpState) : OpState :=
  mkOpState
    (op_current st)
    (j :: op_runnable st)
    (op_need_resched st)
    (op_dispatch_target st).

Fixpoint remove_job (j : JobId) (xs : list JobId) : list JobId :=
  match xs with
  | [] => []
  | x :: xs' => if Nat.eqb x j then remove_job j xs' else x :: remove_job j xs'
  end.

Definition remove_runnable (j : JobId) (st : OpState) : OpState :=
  mkOpState
    (op_current st)
    (remove_job j (op_runnable st))
    (op_need_resched st)
    (op_dispatch_target st).

Definition clear_current_job (j : JobId) (st : OpState) : OpState :=
  mkOpState
    (fun c =>
       match op_current st c with
       | Some j' => if Nat.eqb j' j then None else Some j'
       | None => None
       end)
    (op_runnable st)
    (op_need_resched st)
    (op_dispatch_target st).

Definition set_current (c : CPU) (oj : option JobId) (st : OpState) : OpState :=
  mkOpState
    (fun c' => if Nat.eqb c' c then oj else op_current st c')
    (op_runnable st)
    (op_need_resched st)
    (op_dispatch_target st).

Definition set_need_resched (c : CPU) (b : bool) (st : OpState) : OpState :=
  mkOpState
    (op_current st)
    (op_runnable st)
    (fun c' => if Nat.eqb c' c then b else op_need_resched st c')
    (op_dispatch_target st).

Definition clear_need_resched (c : CPU) (st : OpState) : OpState :=
  set_need_resched c false st.

Definition set_dispatch_target (c : CPU) (oj : option JobId) (st : OpState) : OpState :=
  mkOpState
    (op_current st)
    (op_runnable st)
    (op_need_resched st)
    (fun c' => if Nat.eqb c' c then oj else op_dispatch_target st c').

Definition clear_dispatch_target (c : CPU) (st : OpState) : OpState :=
  set_dispatch_target c None st.

Definition clear_current_and_request (j : JobId) (st : OpState) : OpState :=
  mkOpState
    (fun c =>
       match op_current st c with
       | Some j' => if Nat.eqb j' j then None else Some j'
       | None => None
       end)
    (remove_job j (op_runnable st))
    (fun c =>
       match op_current st c with
       | Some j' => if Nat.eqb j' j then true else op_need_resched st c
       | None => op_need_resched st c
       end)
    (op_dispatch_target st).

Inductive op_step : OpState -> OpEvent -> OpState -> Prop :=
| step_wakeup :
    forall st j,
      op_step st (EvWakeup j) (add_runnable j st)
| step_block :
    forall st j,
      op_job_running st j ->
      op_step st (EvBlock j) (clear_current_and_request j st)
| step_complete :
    forall st j,
      op_job_running st j ->
      op_step st (EvComplete j) (clear_current_and_request j st)
| step_request_resched :
    forall st c,
      op_step st (EvRequestResched c) (set_need_resched c true st)
| step_recv_ipi :
    forall st c,
      op_step st (EvRecvIPI c) (set_need_resched c true st)
| step_choose :
    forall st c j,
      In j (op_runnable st) ->
      op_dispatch_target st c = None ->
      ~ op_job_dispatch_pending st j ->
      op_step st (EvChoose c j) (set_dispatch_target c (Some j) st)
| step_dispatch :
    forall st c j,
      op_dispatch_target st c = Some j ->
      op_current st c = None ->
      op_step st (EvDispatch c j)
        (clear_need_resched c
           (clear_dispatch_target c
              (mkOpState
                 (fun c' => if Nat.eqb c' c then Some j else op_current st c')
                 (remove_job j (op_runnable st))
                 (op_need_resched st)
                 (op_dispatch_target st))))
| step_tick :
    forall st,
      op_step st EvTick st.
