From Stdlib Require Import Arith Arith.PeanoNat Bool Lia List NArith.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import TaskModels.Periodic.PeriodicConcreteAnalysis.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicConcreteAnalysis.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicFastDBF.

Import ListNotations.

(** Checker-local N arithmetic for jittered-periodic DBF windows.

    The proof-facing semantics remain the existing nat-valued DBF functions.
    This module gives extracted checkers N-valued demand and capacity helpers,
    and proves that their boolean window checks coincide with the existing nat
    arithmetic checker. *)

Definition jittered_window_capacity_N (t1 t2 : Time) : N :=
  N.of_nat (t2 - t1).

Definition jittered_periodic_fast_release_count_N
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jitter : TaskId -> Time)
    (τ : TaskId)
    (t1 t2 : Time) : N :=
  N.of_nat
    (jittered_periodic_fast_release_count tasks offset jitter τ t1 t2).

Definition jittered_periodic_fast_dbf_window_N
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jitter : TaskId -> Time)
    (τ : TaskId)
    (t1 t2 : Time) : N :=
  jittered_periodic_fast_release_count_N tasks offset jitter τ t1 t2
  * N.of_nat (task_cost (tasks τ)).

Fixpoint taskset_jittered_periodic_fast_dbf_window_N
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jitter : TaskId -> Time)
    (enumT : list TaskId)
    (t1 t2 : Time) : N :=
  match enumT with
  | [] => 0
  | τ :: enumT' =>
      jittered_periodic_fast_dbf_window_N tasks offset jitter τ t1 t2
      + taskset_jittered_periodic_fast_dbf_window_N
          tasks offset jitter enumT' t1 t2
  end.

Definition jittered_periodic_fast_dbf_window_ok_N_b
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jitter : TaskId -> Time)
    (enumT : list TaskId)
    (t1 t2 : Time) : bool :=
  (taskset_jittered_periodic_fast_dbf_window_N
     tasks offset jitter enumT t1 t2
   <=? jittered_window_capacity_N t1 t2)%N.

Definition jittered_window_fast_ndbf_test_upto
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jitter : TaskId -> Time)
    (enumT : list TaskId)
    (H : Time) : bool :=
  forallb
    (fun w =>
       let '(t1, t2) := w in
       jittered_periodic_fast_dbf_window_ok_N_b
         tasks offset jitter enumT t1 t2)
    (critical_dbf_windows_upto tasks offset enumT H).

Lemma jittered_periodic_fast_release_count_N_to_nat :
  forall tasks offset jitter τ t1 t2,
    N.to_nat
      (jittered_periodic_fast_release_count_N tasks offset jitter τ t1 t2) =
    jittered_periodic_fast_release_count tasks offset jitter τ t1 t2.
Proof.
  intros.
  unfold jittered_periodic_fast_release_count_N.
  apply Nat2N.id.
Qed.

Lemma jittered_periodic_fast_dbf_window_N_to_nat :
  forall tasks offset jitter τ t1 t2,
    N.to_nat
      (jittered_periodic_fast_dbf_window_N tasks offset jitter τ t1 t2) =
    jittered_periodic_fast_dbf_window tasks offset jitter τ t1 t2.
Proof.
  intros.
  unfold jittered_periodic_fast_dbf_window_N,
         jittered_periodic_fast_dbf_window.
  rewrite N2Nat.inj_mul.
  rewrite jittered_periodic_fast_release_count_N_to_nat.
  rewrite Nat2N.id.
  reflexivity.
Qed.

Lemma taskset_jittered_periodic_fast_dbf_window_N_to_nat :
  forall tasks offset jitter enumT t1 t2,
    N.to_nat
      (taskset_jittered_periodic_fast_dbf_window_N
         tasks offset jitter enumT t1 t2) =
    taskset_jittered_periodic_fast_dbf_window
      tasks offset jitter enumT t1 t2.
Proof.
  intros tasks offset jitter enumT.
  induction enumT as [|τ enumT IH]; intros t1 t2; simpl.
  - reflexivity.
  - rewrite N2Nat.inj_add.
    rewrite jittered_periodic_fast_dbf_window_N_to_nat.
    rewrite IH.
    reflexivity.
Qed.

Lemma jittered_window_capacity_N_to_nat :
  forall t1 t2,
    N.to_nat (jittered_window_capacity_N t1 t2) = t2 - t1.
Proof.
  intros.
  unfold jittered_window_capacity_N.
  apply Nat2N.id.
Qed.

Lemma N_le_of_to_nat :
  forall a b,
    N.to_nat a <= N.to_nat b ->
    (a <= b)%N.
Proof.
  intros.
  lia.
Qed.

Lemma N_lt_of_to_nat :
  forall a b,
    N.to_nat a < N.to_nat b ->
    (a < b)%N.
Proof.
  intros.
  lia.
Qed.

Lemma jittered_periodic_fast_dbf_window_ok_N_b_eq_nat :
  forall tasks offset jitter enumT t1 t2,
    jittered_periodic_fast_dbf_window_ok_N_b
      tasks offset jitter enumT t1 t2 =
    (taskset_jittered_periodic_fast_dbf_window
       tasks offset jitter enumT t1 t2 <=? t2 - t1).
Proof.
  intros.
  unfold jittered_periodic_fast_dbf_window_ok_N_b.
  destruct
    (taskset_jittered_periodic_fast_dbf_window
       tasks offset jitter enumT t1 t2 <=? t2 - t1) eqn:Hnat.
  - apply Nat.leb_le in Hnat.
    assert
      ((taskset_jittered_periodic_fast_dbf_window_N
          tasks offset jitter enumT t1 t2
        <=? jittered_window_capacity_N t1 t2)%N = true).
    {
      apply N.leb_le.
      apply N_le_of_to_nat.
      rewrite taskset_jittered_periodic_fast_dbf_window_N_to_nat.
      rewrite jittered_window_capacity_N_to_nat.
      exact Hnat.
    }
    rewrite H.
    reflexivity.
  - apply Nat.leb_gt in Hnat.
    assert
      ((taskset_jittered_periodic_fast_dbf_window_N
          tasks offset jitter enumT t1 t2
        <=? jittered_window_capacity_N t1 t2)%N = false).
    {
      apply N.leb_gt.
      apply N_lt_of_to_nat.
      rewrite taskset_jittered_periodic_fast_dbf_window_N_to_nat.
      rewrite jittered_window_capacity_N_to_nat.
      exact Hnat.
    }
    rewrite H.
    reflexivity.
Qed.

Theorem jittered_window_fast_ndbf_test_upto_eq_nat :
  forall tasks offset jitter enumT H,
    jittered_window_fast_ndbf_test_upto tasks offset jitter enumT H =
    jittered_window_dbf_test_upto tasks offset jitter enumT H.
Proof.
  intros tasks offset jitter enumT H.
  unfold jittered_window_fast_ndbf_test_upto,
         jittered_window_dbf_test_upto.
  generalize (critical_dbf_windows_upto tasks offset enumT H).
  intros windows.
  induction windows as [|[t1 t2] windows IH]; simpl.
  - reflexivity.
  - rewrite jittered_periodic_fast_dbf_window_ok_N_b_eq_nat.
    rewrite taskset_jittered_periodic_fast_dbf_window_eq_enumerated.
    rewrite IH.
    reflexivity.
Qed.
