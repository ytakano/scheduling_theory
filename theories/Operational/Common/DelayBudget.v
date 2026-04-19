From Stdlib Require Import List Arith Arith.PeanoNat Lia ZArith.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Operational.Common.DelayModel.
Import ListNotations.

Definition DelayTrace : Type := Time -> list op_delay_source.

Definition step_delay_budget
    (B : op_delay_bounds) (srcs : list op_delay_source) : nat :=
  fold_right Nat.add 0 (map (delay_bound_of B) srcs).

Fixpoint cumulative_delay_budget
    (B : op_delay_bounds)
    (srcs : DelayTrace)
    (t : Time) : nat :=
  match t with
  | 0 => 0
  | S t' => cumulative_delay_budget B srcs t' + step_delay_budget B (srcs t')
  end.

Definition delay_budget_between
    (B : op_delay_bounds)
    (srcs : DelayTrace)
    (t1 t2 : Time) : nat :=
  cumulative_delay_budget B srcs t2 -
  cumulative_delay_budget B srcs t1.

Definition cumulative_delay
    (B : op_delay_bounds)
    (dt : DelayTrace)
    (t1 t2 : Time) : nat :=
  delay_budget_between B dt t1 t2.

Definition delay_budget_le
    (B : op_delay_bounds)
    (dt : DelayTrace)
    (t1 t2 delta : Time) : Prop :=
  cumulative_delay B dt t1 t2 <= delta.

Lemma cumulative_delay_budget_step :
  forall B srcs t,
    cumulative_delay_budget B srcs (S t) =
    cumulative_delay_budget B srcs t +
    step_delay_budget B (srcs t).
Proof.
  intros B srcs t.
  simpl.
  lia.
Qed.

Lemma cumulative_delay_budget_monotone :
  forall B srcs t1 t2,
    t1 <= t2 ->
    cumulative_delay_budget B srcs t1 <=
    cumulative_delay_budget B srcs t2.
Proof.
  intros B srcs t1 t2 Hle.
  induction Hle.
  - lia.
  - rewrite cumulative_delay_budget_step.
    lia.
Qed.

Lemma delay_budget_between_refl :
  forall B srcs t,
    delay_budget_between B srcs t t = 0.
Proof.
  intros B srcs t.
  unfold delay_budget_between.
  lia.
Qed.

Lemma cumulative_delay_zero_len :
  forall B dt t,
    cumulative_delay B dt t t = 0.
Proof.
  intros B dt t.
  unfold cumulative_delay.
  apply delay_budget_between_refl.
Qed.

Lemma delay_budget_between_split :
  forall B srcs t1 t2 t3,
    t1 <= t2 ->
    t2 <= t3 ->
    delay_budget_between B srcs t1 t3 =
    delay_budget_between B srcs t1 t2 +
    delay_budget_between B srcs t2 t3.
Proof.
  intros B srcs t1 t2 t3 H12 H23.
  unfold delay_budget_between.
  pose proof (cumulative_delay_budget_monotone B srcs t1 t2 H12) as Hmon12.
  pose proof (cumulative_delay_budget_monotone B srcs t2 t3 H23) as Hmon23.
  pose proof (cumulative_delay_budget_monotone B srcs t1 t3 ltac:(lia)) as Hmon13.
  repeat rewrite Nat2Z.inj_sub by assumption.
  lia.
Qed.

Lemma cumulative_delay_split :
  forall B dt t1 t2 t3,
    t1 <= t2 ->
    t2 <= t3 ->
    cumulative_delay B dt t1 t3 =
    cumulative_delay B dt t1 t2 +
    cumulative_delay B dt t2 t3.
Proof.
  intros B dt t1 t2 t3 H12 H23.
  unfold cumulative_delay.
  apply delay_budget_between_split; assumption.
Qed.

Lemma delay_budget_between_single_slot :
  forall B srcs t,
    delay_budget_between B srcs t (S t) =
    step_delay_budget B (srcs t).
Proof.
  intros B srcs t.
  unfold delay_budget_between.
  rewrite cumulative_delay_budget_step.
  lia.
Qed.

Lemma delay_budget_between_le_cumulative :
  forall B srcs t1 t2,
    t1 <= t2 ->
    delay_budget_between B srcs t1 t2 <= cumulative_delay_budget B srcs t2.
Proof.
  intros B srcs t1 t2 Hle.
  unfold delay_budget_between.
  pose proof (cumulative_delay_budget_monotone B srcs t1 t2 Hle) as Hmon.
  lia.
Qed.

Lemma delay_budget_monotone_delta :
  forall B dt t1 t2 d1 d2,
    delay_budget_le B dt t1 t2 d1 ->
    d1 <= d2 ->
    delay_budget_le B dt t1 t2 d2.
Proof.
  intros B dt t1 t2 d1 d2 Hbudget Hle.
  unfold delay_budget_le in *.
  lia.
Qed.
