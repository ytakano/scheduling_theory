From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Operational.Common.State.
From RocqSched Require Import Operational.Common.Trace.
From RocqSched Require Import Operational.Common.Step.

(* OS-neutral projection boundary from concrete machine state into the
   proof-relevant operational scheduler view used by the common layer. *)
Record OSProjection (CState : Type) : Type := mkOSProjection {
  os_to_op_state : CState -> OpState;
}.

Arguments os_to_op_state {CState} _ _.

Definition concrete_trace (CState : Type) : Type :=
  Time -> CState.

Definition os_to_op_trace
    {CState : Type}
    (P : OSProjection CState)
    (tr : concrete_trace CState) : OpTrace :=
  fun t => os_to_op_state P (tr t).

Lemma os_to_op_trace_unfold :
  forall CState (P : OSProjection CState) (tr : concrete_trace CState) t,
    os_to_op_trace P tr t = os_to_op_state P (tr t).
Proof.
  intros CState P tr t.
  reflexivity.
Qed.

(* Adapter-facing labeled projection boundary. Concrete runtimes expose the
   same proof-facing state view as before, plus the abstract operational event
   associated with each concrete transition. *)
Record OSLabeledProjection (CState : Type) : Type := mkOSLabeledProjection {
  osl_state_projection : OSProjection CState;
  os_step_label : CState -> CState -> OpEvent;
}.

Arguments osl_state_projection {CState} _.
Arguments os_step_label {CState} _ _ _.

Definition osl_to_os_projection
    {CState : Type}
    (P : OSLabeledProjection CState) : OSProjection CState :=
  osl_state_projection P.

Definition osl_to_op_trace
    {CState : Type}
    (P : OSLabeledProjection CState)
    (tr : concrete_trace CState) : OpTrace :=
  os_to_op_trace (osl_to_os_projection P) tr.

Definition osl_to_op_event_trace
    {CState : Type}
    (P : OSLabeledProjection CState)
    (tr : concrete_trace CState) : Time -> OpEvent :=
  fun t => os_step_label P (tr t) (tr (S t)).

Lemma osl_to_op_trace_unfold :
  forall CState (P : OSLabeledProjection CState) (tr : concrete_trace CState) t,
    osl_to_op_trace P tr t =
    os_to_op_state (osl_to_os_projection P) (tr t).
Proof.
  intros CState P tr t.
  reflexivity.
Qed.

Lemma osl_to_op_event_trace_unfold :
  forall CState (P : OSLabeledProjection CState) (tr : concrete_trace CState) t,
    osl_to_op_event_trace P tr t =
    os_step_label P (tr t) (tr (S t)).
Proof.
  intros CState P tr t.
  reflexivity.
Qed.
