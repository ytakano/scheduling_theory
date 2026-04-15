From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Operational.Common.State.
From RocqSched Require Import Operational.Common.Trace.
From RocqSched Require Import Operational.Common.Projection.
Import ListNotations.

Record AwkernelState : Type := mkAwkernelState {
  awk_current : CPU -> option JobId;
  awk_runnable : list JobId;
  awk_need_resched : CPU -> bool;
}.

Definition awk_to_op_state (st : AwkernelState) : OpState :=
  mkOpState (awk_current st) (awk_runnable st) (awk_need_resched st).

Definition AwkernelTrace : Type := Time -> AwkernelState.

Definition awk_to_op_trace (tr : AwkernelTrace) : OpTrace :=
  fun t => awk_to_op_state (tr t).

Definition awk_project_schedule (tr : AwkernelTrace) : Schedule :=
  project_schedule (awk_to_op_trace tr).

Definition awk_projected_running
    (m : nat) (tr : AwkernelTrace) (j : JobId) (t : Time) : Prop :=
  projected_running m (awk_to_op_trace tr) j t.

Lemma awk_project_schedule_eq :
  forall tr t c,
    awk_project_schedule tr t c = awk_current (tr t) c.
Proof.
  intros tr t c.
  reflexivity.
Qed.

Lemma awk_projected_running_iff :
  forall m tr j t,
    awk_projected_running m tr j t <->
    exists c, c < m /\ awk_current (tr t) c = Some j.
Proof.
  intros m tr j t.
  unfold awk_projected_running, awk_to_op_trace.
  rewrite projected_running_iff_current.
  tauto.
Qed.
