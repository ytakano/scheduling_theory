From Stdlib Require Import Arith Arith.PeanoNat Lia List Bool NArith.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Analysis.Uniprocessor.DemandBound.
From RocqSched Require Import Analysis.Uniprocessor.ProcessorDemand.
From RocqSched Require Import TaskModels.Periodic.PeriodicConcreteAnalysis.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Periodic.PeriodicWindowDemandBound.

Import ListNotations.

(** Checker-local N arithmetic for periodic DBF computations.

    The common semantics remains the existing nat-valued DBF/window DBF.  These
    helpers are executable arithmetic entrypoints for bounded checkers; the
    soundness lemmas below project every N result back to the nat definitions. *)

Definition n_expected_release
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (tau : TaskId)
    (k : nat) : N :=
  (N.of_nat (offset tau)
   + N.of_nat k * N.of_nat (task_period (tasks tau)))%N.

Definition n_expected_abs_deadline
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (tau : TaskId)
    (k : nat) : N :=
  (n_expected_release tasks offset tau k
   + N.of_nat (task_relative_deadline (tasks tau)))%N.

Definition n_periodic_dbf_count
    (tasks : TaskId -> Task)
    (tau : TaskId)
    (H : Time) : N :=
  if (N.of_nat H <? N.of_nat (task_relative_deadline (tasks tau)))%N then 0%N
  else
    N.succ
      (((N.of_nat H - N.of_nat (task_relative_deadline (tasks tau)))
        / N.of_nat (task_period (tasks tau)))%N).

Definition n_periodic_dbf
    (tasks : TaskId -> Task)
    (tau : TaskId)
    (H : Time) : N :=
  (n_periodic_dbf_count tasks tau H * N.of_nat (task_cost (tasks tau)))%N.

Fixpoint n_taskset_periodic_dbf
    (tasks : TaskId -> Task)
    (enumT : list TaskId)
    (H : Time) : N :=
  match enumT with
  | [] => 0%N
  | tau :: enumT' =>
      (n_periodic_dbf tasks tau H
       + n_taskset_periodic_dbf tasks enumT' H)%N
  end.

Definition n_periodic_index_in_window
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (tau : TaskId)
    (t1 t2 : Time)
    (k : nat) : bool :=
  (N.of_nat t1 <=? n_expected_release tasks offset tau k)%N
  &&
  (n_expected_abs_deadline tasks offset tau k <=? N.of_nat t2)%N.

Definition n_periodic_dbf_window
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (tau : TaskId)
    (t1 t2 : Time) : N :=
  (N.of_nat
     (length
        (filter
           (n_periodic_index_in_window tasks offset tau t1 t2)
           (seq 0 (S t2))))
   * N.of_nat (task_cost (tasks tau)))%N.

Fixpoint n_taskset_periodic_dbf_window
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (enumT : list TaskId)
    (t1 t2 : Time) : N :=
  match enumT with
  | [] => 0%N
  | tau :: enumT' =>
      (n_periodic_dbf_window tasks offset tau t1 t2
       + n_taskset_periodic_dbf_window tasks offset enumT' t1 t2)%N
  end.

Definition n_dbf_test_upto
    (tasks : TaskId -> Task)
    (enumT : list TaskId)
    (H : Time) : bool :=
  forallb
    (fun t => (n_taskset_periodic_dbf tasks enumT t <=? N.of_nat t)%N)
    (critical_dbf_points_upto tasks (fun _ => 0) enumT H).

Definition n_window_dbf_test_upto
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (enumT : list TaskId)
    (H : Time) : bool :=
  forallb
    (fun w =>
       let '(t1, t2) := w in
       (n_taskset_periodic_dbf_window tasks offset enumT t1 t2
        <=? N.of_nat (t2 - t1))%N)
    (critical_dbf_windows_upto tasks offset enumT H).

Definition n_dbf_test_by_cutoff
    (tasks : TaskId -> Task)
    (enumT : list TaskId) : bool :=
  n_dbf_test_upto tasks enumT (scalar_dbf_cutoff_bound tasks enumT).

Definition n_window_dbf_test_by_cutoff
    (tasks : TaskId -> Task)
    (enumT : list TaskId) : bool :=
  n_window_dbf_test_upto
    tasks
    (fun _ => 0)
    enumT
    (zero_offset_window_dbf_cutoff_bound tasks enumT)
  && n_dbf_test_by_cutoff tasks enumT.

Lemma n_ltb_of_nat_eq :
  forall a b,
    (N.of_nat a <? N.of_nat b)%N = (a <? b).
Proof.
  intros a b.
  destruct (N.ltb_spec (N.of_nat a) (N.of_nat b));
    destruct (Nat.ltb_spec a b); try reflexivity; lia.
Qed.

Lemma n_leb_of_nat_eq :
  forall a b,
    (N.of_nat a <=? N.of_nat b)%N = (a <=? b).
Proof.
  intros a b.
  destruct (N.leb_spec (N.of_nat a) (N.of_nat b));
    destruct (Nat.leb_spec a b); try reflexivity; lia.
Qed.

Lemma n_leb_to_nat_of_nat_eq :
  forall a b,
    (a <=? N.of_nat b)%N = (N.to_nat a <=? b).
Proof.
  intros a b.
  rewrite <- (N2Nat.id a) at 1.
  apply n_leb_of_nat_eq.
Qed.

Lemma n_expected_release_sound :
  forall tasks offset tau k,
    n_expected_release tasks offset tau k =
    N.of_nat (expected_release tasks offset tau k).
Proof.
  intros tasks offset tau k.
  unfold n_expected_release, expected_release.
  rewrite Nat2N.inj_add.
  rewrite Nat2N.inj_mul.
  reflexivity.
Qed.

Lemma n_expected_abs_deadline_sound :
  forall tasks offset tau k,
    n_expected_abs_deadline tasks offset tau k =
    N.of_nat (expected_abs_deadline tasks offset tau k).
Proof.
  intros tasks offset tau k.
  unfold n_expected_abs_deadline, expected_abs_deadline.
  rewrite n_expected_release_sound.
  rewrite Nat2N.inj_add.
  reflexivity.
Qed.

Lemma n_periodic_dbf_sound :
  forall tasks tau H,
    N.to_nat (n_periodic_dbf tasks tau H) =
    periodic_dbf tasks tau H.
Proof.
  intros tasks tau H.
  unfold n_periodic_dbf, n_periodic_dbf_count, periodic_dbf.
  rewrite n_ltb_of_nat_eq.
  destruct (H <? task_relative_deadline (tasks tau)); simpl.
  - reflexivity.
  - rewrite N2Nat.inj_mul.
    rewrite N2Nat.inj_succ.
    rewrite N2Nat.inj_div.
    rewrite N2Nat.inj_sub.
    rewrite !Nat2N.id.
    reflexivity.
Qed.

Lemma n_taskset_periodic_dbf_sound :
  forall tasks enumT H,
    N.to_nat (n_taskset_periodic_dbf tasks enumT H) =
    taskset_periodic_dbf tasks enumT H.
Proof.
  intros tasks enumT H.
  induction enumT as [|tau enumT IH]; simpl.
  - reflexivity.
  - rewrite N2Nat.inj_add.
    rewrite n_periodic_dbf_sound.
    rewrite IH.
    reflexivity.
Qed.

Lemma n_periodic_index_in_window_eq :
  forall tasks offset tau t1 t2 k,
    n_periodic_index_in_window tasks offset tau t1 t2 k =
    periodic_index_in_window tasks offset tau t1 t2 k.
Proof.
  intros tasks offset tau t1 t2 k.
  unfold n_periodic_index_in_window, periodic_index_in_window.
  rewrite n_expected_release_sound.
  rewrite n_expected_abs_deadline_sound.
  rewrite !n_leb_of_nat_eq.
  reflexivity.
Qed.

Lemma n_periodic_dbf_window_sound :
  forall tasks offset tau t1 t2,
    N.to_nat (n_periodic_dbf_window tasks offset tau t1 t2) =
    periodic_dbf_window tasks offset tau t1 t2.
Proof.
  intros tasks offset tau t1 t2.
  unfold n_periodic_dbf_window, periodic_dbf_window.
  rewrite N2Nat.inj_mul.
  rewrite !Nat2N.id.
  rewrite (filter_ext
             (n_periodic_index_in_window tasks offset tau t1 t2)
             (periodic_index_in_window tasks offset tau t1 t2)).
  - reflexivity.
  - intro k. apply n_periodic_index_in_window_eq.
Qed.

Lemma n_taskset_periodic_dbf_window_sound :
  forall tasks offset enumT t1 t2,
    N.to_nat (n_taskset_periodic_dbf_window tasks offset enumT t1 t2) =
    taskset_periodic_dbf_window tasks offset enumT t1 t2.
Proof.
  intros tasks offset enumT t1 t2.
  induction enumT as [|tau enumT IH]; simpl.
  - reflexivity.
  - rewrite N2Nat.inj_add.
    rewrite n_periodic_dbf_window_sound.
    rewrite IH.
    reflexivity.
Qed.

Lemma forallb_ext_simple :
  forall (A : Type) (f g : A -> bool) l,
    (forall x, f x = g x) ->
    forallb f l = forallb g l.
Proof.
  intros A f g l Heq.
  induction l as [|x xs IH]; simpl.
  - reflexivity.
  - rewrite Heq. rewrite IH. reflexivity.
Qed.

Lemma n_dbf_test_upto_eq :
  forall tasks enumT H,
    n_dbf_test_upto tasks enumT H =
    dbf_test_upto tasks enumT H.
Proof.
  intros tasks enumT H.
  unfold n_dbf_test_upto, dbf_test_upto.
  apply forallb_ext_simple.
  intro t.
  rewrite n_leb_to_nat_of_nat_eq.
  rewrite n_taskset_periodic_dbf_sound.
  reflexivity.
Qed.

Lemma n_window_dbf_test_upto_eq :
  forall tasks offset enumT H,
    n_window_dbf_test_upto tasks offset enumT H =
    window_dbf_test_upto tasks offset enumT H.
Proof.
  intros tasks offset enumT H.
  unfold n_window_dbf_test_upto, window_dbf_test_upto.
  apply forallb_ext_simple.
  intros [t1 t2].
  rewrite n_leb_to_nat_of_nat_eq.
  rewrite n_taskset_periodic_dbf_window_sound.
  reflexivity.
Qed.

Lemma n_dbf_test_by_cutoff_eq :
  forall tasks enumT,
    n_dbf_test_by_cutoff tasks enumT =
    dbf_test_by_cutoff tasks enumT.
Proof.
  intros tasks enumT.
  unfold n_dbf_test_by_cutoff, dbf_test_by_cutoff.
  apply n_dbf_test_upto_eq.
Qed.

Lemma n_window_dbf_test_by_cutoff_eq :
  forall tasks enumT,
    n_window_dbf_test_by_cutoff tasks enumT =
    window_dbf_test_by_cutoff tasks enumT.
Proof.
  intros tasks enumT.
  unfold n_window_dbf_test_by_cutoff, window_dbf_test_by_cutoff.
  rewrite n_window_dbf_test_upto_eq.
  rewrite n_dbf_test_by_cutoff_eq.
  reflexivity.
Qed.
