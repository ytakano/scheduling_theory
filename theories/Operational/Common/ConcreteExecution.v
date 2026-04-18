From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Operational.Common.State.
From RocqSched Require Import Operational.Common.Trace.
From RocqSched Require Import Operational.Common.Step.
From RocqSched Require Import Operational.Common.Invariants.
From RocqSched Require Import Operational.Common.Execution.
From RocqSched Require Import Operational.Common.OSProjectionInterface.

(* Thin packaging layer turning a concrete OS trace into a common operational
   execution once stepwise progress and structural invariants are shown after
   projection. *)
Record concrete_execution
    {CState : Type}
    (P : OSProjection CState)
    (m : nat) : Type := mkConcreteExecution {
  ce_trace : concrete_trace CState;
  ce_init : Prop;
  ce_stepwise :
    trace_stepwise (os_to_op_trace P ce_trace);
  ce_struct_inv :
    forall t, op_struct_inv m (os_to_op_state P (ce_trace t));
}.

Arguments ce_trace {CState P m} _ _.
Arguments ce_init {CState P m} _.
Arguments ce_stepwise {CState P m} _ _.
Arguments ce_struct_inv {CState P m} _ _.

Definition concrete_to_execution
    {CState : Type}
    {P : OSProjection CState}
    {m : nat}
    (ex : concrete_execution P m) : execution m :=
  mkExecution
    m
    (os_to_op_trace P (ce_trace ex))
    (ce_init ex)
    (ce_stepwise ex)
    (ce_struct_inv ex).

Lemma concrete_to_execution_trace_eq :
  forall CState (P : OSProjection CState) m
         (ex : concrete_execution P m) t,
    ex_trace (concrete_to_execution ex) t =
    os_to_op_state P (ce_trace ex t).
Proof.
  intros CState P m ex t.
  reflexivity.
Qed.

Lemma concrete_execution_trace_step :
  forall CState (P : OSProjection CState) m
         (ex : concrete_execution P m) t,
    exists ev,
      op_step
        (os_to_op_state P (ce_trace ex t))
        ev
        (os_to_op_state P (ce_trace ex (S t))).
Proof.
  intros CState P m ex t.
  exact (ce_stepwise ex t).
Qed.
