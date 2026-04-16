From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Operational.Common.State.
From RocqSched Require Import Operational.Common.Trace.
From RocqSched Require Import Operational.Common.Projection.
From RocqSched Require Import Operational.Common.Invariants.
From RocqSched Require Import Operational.Common.Execution.
From RocqSched Require Import Operational.Common.ProjectionLemmas.
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

Record awk_execution (m : nat) : Type := mkAwkExecution {
  awk_ex_trace : AwkernelTrace;
  awk_ex_init : Prop;
  awk_ex_stepwise : trace_stepwise (awk_to_op_trace awk_ex_trace);
  awk_ex_struct_inv : forall t, op_struct_inv m (awk_to_op_state (awk_ex_trace t));
}.

Arguments awk_ex_trace {m} _ _.
Arguments awk_ex_init {m} _.
Arguments awk_ex_stepwise {m} _ _.
Arguments awk_ex_struct_inv {m} _ _.

Definition awk_to_execution {m} (ex : awk_execution m) : execution m :=
  mkExecution
    m
    (awk_to_op_trace (awk_ex_trace ex))
    (awk_ex_init ex)
    (awk_ex_stepwise ex)
    (awk_ex_struct_inv ex).

Definition awk_trace_sound
    (jobs : JobId -> Job) (m : nat) (ex : awk_execution m) : Prop :=
  execution_projection_sound jobs m (awk_to_execution ex).

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

Lemma awk_trace_sound_implies_valid_schedule :
  forall jobs m ex,
    awk_trace_sound jobs m ex ->
    valid_schedule jobs m (awk_project_schedule (awk_ex_trace ex)).
Proof.
  intros jobs m ex Hsound.
  unfold awk_trace_sound in Hsound.
  change (valid_schedule jobs m
            (project_schedule (ex_trace (awk_to_execution ex)))).
  apply execution_projection_sound_implies_valid_schedule.
  exact Hsound.
Qed.
