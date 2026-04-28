From Stdlib Require Import Arith Arith.PeanoNat Lia List Bool.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import TaskModels.Periodic.PeriodicConcreteAnalysis.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicWindowDemandBound.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicFastDBF.

Import ListNotations.

(** * Compact bounded DBF basis for jittered-periodic task sets

    The schema-v2 jittered certificate records every checked bounded window.
    This file introduces the proof-facing abstraction for schema-v3: a compact
    basis grouped by right endpoint.  The checker may validate only basis
    windows, provided the basis covers every bounded window by a demand-equal
    representative with a later left edge. *)

Definition JitteredCompactDbfBasis := list (Time * list Time).

Definition jittered_compact_basis_windows
    (basis : JitteredCompactDbfBasis) : list (Time * Time) :=
  flat_map
    (fun row =>
       let '(t2, left_edges) := row in
       map (fun t1 => (t1, t2)) left_edges)
    basis.

Definition jittered_left_edge_covers
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jitter : TaskId -> Time)
    (enumT : list TaskId)
    (t1 t2 l : Time) : Prop :=
  t1 <= l /\
  l <= t2 /\
  taskset_jittered_periodic_dbf_window tasks offset jitter enumT t1 t2 =
  taskset_jittered_periodic_dbf_window tasks offset jitter enumT l t2.

Definition jittered_compact_basis_covers_upto
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jitter : TaskId -> Time)
    (enumT : list TaskId)
    (H : Time)
    (basis : JitteredCompactDbfBasis) : Prop :=
  forall t1 t2,
    t1 <= t2 ->
    t2 <= H ->
    exists l,
      In (l, t2) (jittered_compact_basis_windows basis) /\
      jittered_left_edge_covers tasks offset jitter enumT t1 t2 l.

Definition jittered_compact_basis_dbf_test
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jitter : TaskId -> Time)
    (enumT : list TaskId)
    (basis : JitteredCompactDbfBasis) : bool :=
  forallb
    (fun w =>
       let '(t1, t2) := w in
       (t1 <=? t2)
       &&
       (taskset_jittered_periodic_dbf_window
          tasks offset jitter enumT t1 t2 <=? t2 - t1))
    (jittered_compact_basis_windows basis).

Definition jittered_fast_compact_basis_dbf_test
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jitter : TaskId -> Time)
    (enumT : list TaskId)
    (basis : JitteredCompactDbfBasis) : bool :=
  forallb
    (fun w =>
       let '(t1, t2) := w in
       (t1 <=? t2)
       &&
       (taskset_jittered_periodic_fast_dbf_window
          tasks offset jitter enumT t1 t2 <=? t2 - t1))
    (jittered_compact_basis_windows basis).

Definition jittered_identity_compact_basis_upto
    (H : Time) : JitteredCompactDbfBasis :=
  map (fun t2 => (t2, bounded_time_points t2)) (bounded_time_points H).

Lemma jittered_fast_compact_basis_dbf_test_eq :
  forall tasks offset jitter enumT basis,
    jittered_fast_compact_basis_dbf_test tasks offset jitter enumT basis =
    jittered_compact_basis_dbf_test tasks offset jitter enumT basis.
Proof.
  intros tasks offset jitter enumT basis.
  unfold jittered_fast_compact_basis_dbf_test,
         jittered_compact_basis_dbf_test.
  generalize (jittered_compact_basis_windows basis).
  intros windows.
  induction windows as [|[t1 t2] windows IH]; simpl.
  - reflexivity.
  - rewrite taskset_jittered_periodic_fast_dbf_window_eq_enumerated.
    rewrite IH.
    reflexivity.
Qed.

Lemma jittered_compact_basis_dbf_test_window_sound :
  forall tasks offset jitter enumT basis t1 t2,
    jittered_compact_basis_dbf_test tasks offset jitter enumT basis = true ->
    In (t1, t2) (jittered_compact_basis_windows basis) ->
    taskset_jittered_periodic_dbf_window tasks offset jitter enumT t1 t2
    <= t2 - t1.
Proof.
  intros tasks offset jitter enumT basis t1 t2 Htest Hin.
  unfold jittered_compact_basis_dbf_test in Htest.
  apply forallb_forall with (x := (t1, t2)) in Htest; auto.
  simpl in Htest.
  apply andb_true_iff in Htest as [_ Hdbf].
  now apply Nat.leb_le in Hdbf.
Qed.

Theorem jittered_compact_basis_dbf_test_sound :
  forall tasks offset jitter enumT H basis t1 t2,
    jittered_compact_basis_covers_upto
      tasks offset jitter enumT H basis ->
    jittered_compact_basis_dbf_test tasks offset jitter enumT basis = true ->
    t1 <= t2 ->
    t2 <= H ->
    taskset_jittered_periodic_dbf_window tasks offset jitter enumT t1 t2
    <= t2 - t1.
Proof.
  intros tasks offset jitter enumT H basis t1 t2 Hcovers Htest Hle12 Hle2H.
  destruct (Hcovers t1 t2 Hle12 Hle2H)
    as [l [Hin [Hle1l [Hlel2 Hdemand]]]].
  pose proof
    (jittered_compact_basis_dbf_test_window_sound
       tasks offset jitter enumT basis l t2 Htest Hin) as Hbasis.
  rewrite Hdemand.
  enough (t2 - l <= t2 - t1) by lia.
  lia.
Qed.

Theorem jittered_fast_compact_basis_dbf_test_sound :
  forall tasks offset jitter enumT H basis t1 t2,
    jittered_compact_basis_covers_upto
      tasks offset jitter enumT H basis ->
    jittered_fast_compact_basis_dbf_test tasks offset jitter enumT basis = true ->
    t1 <= t2 ->
    t2 <= H ->
    taskset_jittered_periodic_dbf_window tasks offset jitter enumT t1 t2
    <= t2 - t1.
Proof.
  intros tasks offset jitter enumT H basis t1 t2 Hcovers Htest Hle12 Hle2H.
  rewrite jittered_fast_compact_basis_dbf_test_eq in Htest.
  eapply jittered_compact_basis_dbf_test_sound; eauto.
Qed.

Lemma jittered_identity_compact_basis_covers_upto :
  forall tasks offset jitter enumT H,
    jittered_compact_basis_covers_upto
      tasks offset jitter enumT H (jittered_identity_compact_basis_upto H).
Proof.
  intros tasks offset jitter enumT H t1 t2 Hle12 Hle2H.
  exists t1.
  split.
  - unfold jittered_identity_compact_basis_upto,
           jittered_compact_basis_windows.
    apply in_flat_map.
    exists (t2, bounded_time_points t2).
    split.
    + apply in_map_iff.
      exists t2.
      split; [reflexivity|].
      unfold bounded_time_points.
      rewrite in_seq.
      lia.
    + apply in_map_iff.
      exists t1.
      split; [reflexivity|].
      unfold bounded_time_points.
      rewrite in_seq.
      lia.
  - unfold jittered_left_edge_covers.
    repeat split; try lia.
Qed.
