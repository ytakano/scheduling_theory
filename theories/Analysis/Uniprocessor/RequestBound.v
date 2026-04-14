From Stdlib Require Import Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Analysis.Common.WorkloadAggregation.

(* ===== Request-Bound Function (RBF) ===== *)

(* The standard periodic RBF: the maximum cumulative demand of task τ
   in any window of length H is bounded by ⌈H / period⌉ × wcet. *)
Definition periodic_rbf
    (tasks : TaskId -> Task)
    (τ : TaskId)
    (H : Time) : nat :=
  ((H + task_period (tasks τ) - 1) / task_period (tasks τ))
  * task_cost (tasks τ).

(* Sporadic and jittered-periodic tasks satisfy the same upper bound
   as periodic tasks with the same period (since inter-arrival ≥ period). *)
Definition sporadic_rbf_bound
    (tasks : TaskId -> Task)
    (τ : TaskId)
    (H : Time) : nat :=
  ((H + task_period (tasks τ) - 1) / task_period (tasks τ))
  * task_cost (tasks τ).

(* ===== Basic properties ===== *)

(* periodic_rbf and sporadic_rbf_bound are definitionally equal. *)
Lemma sporadic_rbf_bound_eq_periodic_rbf :
  forall tasks τ H,
    sporadic_rbf_bound tasks τ H = periodic_rbf tasks τ H.
Proof. reflexivity. Qed.

(* Both are zero when H = 0 (regardless of period, since 0 + p - 1 = p - 1 < p). *)
Lemma periodic_rbf_zero :
  forall tasks τ,
    periodic_rbf tasks τ 0 = 0.
Proof.
  intros tasks τ.
  unfold periodic_rbf.
  simpl.
  (* goal: (task_period (tasks τ) - 1) / task_period (tasks τ) * task_cost (tasks τ) = 0 *)
  destruct (task_period (tasks τ)) as [| p'] eqn:Hp.
  - simpl. lia.
  - replace (S p' - 1) with p' by lia.
    assert (H0 : p' / S p' = 0) by (apply Nat.div_small; lia).
    rewrite H0. lia.
Qed.

(* ===== Monotonicity ===== *)

(* The ceiling count ⌈H / p⌉ is non-decreasing in H. *)
Lemma periodic_rbf_count_monotone :
  forall (tasks : TaskId -> Task) (τ : TaskId) (H1 H2 : Time),
    H1 <= H2 ->
    (H1 + task_period (tasks τ) - 1) / task_period (tasks τ) <=
    (H2 + task_period (tasks τ) - 1) / task_period (tasks τ).
Proof.
  intros tasks τ H1 H2 Hle.
  apply ceil_div_mono.
  lia.
Qed.

Lemma periodic_rbf_monotone :
  forall (tasks : TaskId -> Task) (τ : TaskId) (H1 H2 : Time),
    H1 <= H2 ->
    periodic_rbf tasks τ H1 <= periodic_rbf tasks τ H2.
Proof.
  intros tasks τ H1 H2 Hle.
  unfold periodic_rbf.
  apply Nat.mul_le_mono_r.
  exact (periodic_rbf_count_monotone tasks τ H1 H2 Hle).
Qed.

Lemma sporadic_rbf_bound_monotone :
  forall (tasks : TaskId -> Task) (τ : TaskId) (H1 H2 : Time),
    H1 <= H2 ->
    sporadic_rbf_bound tasks τ H1 <= sporadic_rbf_bound tasks τ H2.
Proof.
  intros tasks τ H1 H2 Hle.
  unfold sporadic_rbf_bound.
  apply Nat.mul_le_mono_r.
  exact (periodic_rbf_count_monotone tasks τ H1 H2 Hle).
Qed.

(* ===== Algebraic structure ===== *)

(* The count bound is at most H when period ≥ 1. *)
Lemma periodic_rbf_count_le_H :
  forall (tasks : TaskId -> Task) (τ : TaskId) (H : Time),
    0 < task_period (tasks τ) ->
    (H + task_period (tasks τ) - 1) / task_period (tasks τ) <= H.
Proof.
  intros tasks τ H Hp.
  destruct H as [| H'].
  - (* H = 0: (p - 1) / p = 0 <= 0 *)
    simpl.
    rewrite Nat.div_small; lia.
  - (* H = S H': S H' + p - 1 <= p * S H', so (S H' + p - 1)/p <= S H' *)
    apply Nat.Div0.div_le_upper_bound.
    nia.
Qed.

(* periodic_rbf tasks τ H ≤ H * task_cost (tasks τ) — the old coarse bound. *)
Lemma periodic_rbf_le_coarse_bound :
  forall (tasks : TaskId -> Task) (τ : TaskId) (H : Time),
    0 < task_period (tasks τ) ->
    periodic_rbf tasks τ H <= H * task_cost (tasks τ).
Proof.
  intros tasks τ H Hp.
  unfold periodic_rbf.
  apply Nat.mul_le_mono_r.
  exact (periodic_rbf_count_le_H tasks τ H Hp).
Qed.
