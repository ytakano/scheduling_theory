From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Operational.Common.State.
From RocqSched Require Import Operational.Common.Trace.

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
