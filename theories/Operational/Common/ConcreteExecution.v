From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Operational.Common.State.
From RocqSched Require Import Operational.Common.Trace.
From RocqSched Require Import Operational.Common.Step.
From RocqSched Require Import Operational.Common.Invariants.
From RocqSched Require Import Operational.Common.Execution.
From RocqSched Require Import Operational.Common.OSProjectionInterface.
From RocqSched Require Import Operational.Common.LabeledExecution.

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

(* Stronger packaging layer for adapters that can project each concrete step
   onto a specific common operational event. *)
Record labeled_concrete_execution
    {CState : Type}
    (P : OSLabeledProjection CState)
    (m : nat) : Type := mkLabeledConcreteExecution {
  lce_trace : concrete_trace CState;
  lce_init : Prop;
  lce_stepwise :
    forall t,
      op_step
        (os_to_op_state (osl_to_os_projection P) (lce_trace t))
        (os_step_label P (lce_trace t) (lce_trace (S t)))
        (os_to_op_state (osl_to_os_projection P) (lce_trace (S t)));
  lce_struct_inv :
    forall t, op_struct_inv m (os_to_op_state (osl_to_os_projection P) (lce_trace t));
}.

Arguments lce_trace {CState P m} _ _.
Arguments lce_init {CState P m} _.
Arguments lce_stepwise {CState P m} _ _.
Arguments lce_struct_inv {CState P m} _ _.

Definition concrete_to_labeled_execution
    {CState : Type}
    {P : OSLabeledProjection CState}
    {m : nat}
    (ex : labeled_concrete_execution P m) : labeled_execution m :=
  mkLabeledExecution
    m
    (osl_to_op_trace P (lce_trace ex))
    (osl_to_op_event_trace P (lce_trace ex))
    (lce_init ex)
    (lce_stepwise ex)
    (lce_struct_inv ex).

Definition labeled_concrete_to_execution
    {CState : Type}
    {P : OSLabeledProjection CState}
    {m : nat}
    (ex : labeled_concrete_execution P m) : execution m :=
  labeled_to_execution (concrete_to_labeled_execution ex).

Lemma concrete_to_labeled_execution_trace_eq :
  forall CState (P : OSLabeledProjection CState) m
         (ex : labeled_concrete_execution P m) t,
    lex_trace (concrete_to_labeled_execution ex) t =
    os_to_op_state (osl_to_os_projection P) (lce_trace ex t).
Proof.
  intros CState P m ex t.
  reflexivity.
Qed.

Lemma concrete_to_labeled_execution_event_eq :
  forall CState (P : OSLabeledProjection CState) m
         (ex : labeled_concrete_execution P m) t,
    lex_event (concrete_to_labeled_execution ex) t =
    os_step_label P (lce_trace ex t) (lce_trace ex (S t)).
Proof.
  intros CState P m ex t.
  reflexivity.
Qed.

Lemma labeled_concrete_execution_trace_step :
  forall CState (P : OSLabeledProjection CState) m
         (ex : labeled_concrete_execution P m) t,
    op_step
      (os_to_op_state (osl_to_os_projection P) (lce_trace ex t))
      (os_step_label P (lce_trace ex t) (lce_trace ex (S t)))
      (os_to_op_state (osl_to_os_projection P) (lce_trace ex (S t))).
Proof.
  intros CState P m ex t.
  exact (lce_stepwise ex t).
Qed.
