From Stdlib Require Import Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Operational.Common.State.
From RocqSched Require Import Operational.Common.Trace.

Definition project_schedule (tr : OpTrace) : Schedule :=
  fun t c => op_current (tr t) c.

Definition projected_running (m : nat) (tr : OpTrace) (j : JobId) (t : Time) : Prop :=
  running m (project_schedule tr) j t.

Lemma project_schedule_eq_current :
  forall tr t c,
    project_schedule tr t c = op_current (tr t) c.
Proof.
  intros tr t c.
  reflexivity.
Qed.

Lemma project_schedule_cpu_eq :
  forall tr t c,
    project_schedule tr t c = op_current_job (tr t) c.
Proof.
  intros tr t c.
  reflexivity.
Qed.

Lemma projected_running_iff_current :
  forall m tr j t,
    projected_running m tr j t <->
    exists c, c < m /\ op_current (tr t) c = Some j.
Proof.
  intros m tr j t.
  unfold projected_running, running, project_schedule.
  tauto.
Qed.
