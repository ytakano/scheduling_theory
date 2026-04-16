From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Analysis.Uniprocessor.ProcessorDemand.
From RocqSched Require Import TaskModels.Periodic.PeriodicWindowDemandBound.

Import ListNotations.

(* A first bounded checker for concrete periodic DBF goals. The point set is a
   sound superset of all relevant times up to H: we simply enumerate every time
   in [0, H]. *)
Definition critical_dbf_points_upto
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (enumT : list TaskId)
    (H : Time) : list Time :=
  seq 0 (S H).

Definition dbf_test_upto
    (tasks : TaskId -> Task)
    (enumT : list TaskId)
    (H : Time) : bool :=
  forallb (fun t => taskset_periodic_dbf tasks enumT t <=? t)
          (critical_dbf_points_upto tasks (fun _ => 0) enumT H).

Definition window_dbf_test_upto
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (enumT : list TaskId)
    (H : Time) : bool :=
  forallb
    (fun t1 =>
       forallb
         (fun t2 =>
            taskset_periodic_dbf_window tasks offset enumT t1 t2 <=? t2 - t1)
         (seq t1 (S (H - t1))))
    (critical_dbf_points_upto tasks offset enumT H).

Lemma critical_dbf_points_upto_complete :
  forall tasks offset enumT H t,
    t <= H ->
    In t (critical_dbf_points_upto tasks offset enumT H).
Proof.
  intros tasks offset enumT H t Hle.
  unfold critical_dbf_points_upto.
  rewrite in_seq.
  lia.
Qed.

Lemma window_dbf_test_upto_inner_complete :
  forall H t1 t2,
    t1 <= t2 ->
    t2 <= H ->
    In t2 (seq t1 (S (H - t1))).
Proof.
  intros H t1 t2 Hle12 Hle2H.
  rewrite in_seq.
  lia.
Qed.

Lemma dbf_test_upto_sound :
  forall tasks enumT H t,
    dbf_test_upto tasks enumT H = true ->
    In t (critical_dbf_points_upto tasks (fun _ => 0) enumT H) ->
    taskset_periodic_dbf tasks enumT t <= t.
Proof.
  intros tasks enumT H t Htest Hin.
  unfold dbf_test_upto in Htest.
  apply forallb_forall with (x := t) in Htest; auto.
  now apply Nat.leb_le in Htest.
Qed.

Theorem dbf_test_upto_true_implies_bounded_dbf :
  forall tasks enumT H t,
    dbf_test_upto tasks enumT H = true ->
    t <= H ->
    taskset_periodic_dbf tasks enumT t <= t.
Proof.
  intros tasks enumT H t Htest Hle.
  eapply dbf_test_upto_sound; eauto.
  apply critical_dbf_points_upto_complete; exact Hle.
Qed.

Lemma window_dbf_test_upto_sound :
  forall tasks offset enumT H t1 t2,
    window_dbf_test_upto tasks offset enumT H = true ->
    In t1 (critical_dbf_points_upto tasks offset enumT H) ->
    In t2 (seq t1 (S (H - t1))) ->
    taskset_periodic_dbf_window tasks offset enumT t1 t2 <= t2 - t1.
Proof.
  intros tasks offset enumT H t1 t2 Htest Ht1 Ht2.
  unfold window_dbf_test_upto in Htest.
  apply forallb_forall with (x := t1) in Htest; auto.
  apply forallb_forall with (x := t2) in Htest; auto.
  now apply Nat.leb_le in Htest.
Qed.

Theorem window_dbf_test_upto_true_implies_bounded_window_dbf :
  forall tasks offset enumT H t1 t2,
    window_dbf_test_upto tasks offset enumT H = true ->
    t1 <= t2 ->
    t2 <= H ->
    taskset_periodic_dbf_window tasks offset enumT t1 t2 <= t2 - t1.
Proof.
  intros tasks offset enumT H t1 t2 Htest Hle12 Hle2H.
  eapply window_dbf_test_upto_sound; eauto.
  - apply critical_dbf_points_upto_complete. lia.
  - apply window_dbf_test_upto_inner_complete; assumption.
Qed.
