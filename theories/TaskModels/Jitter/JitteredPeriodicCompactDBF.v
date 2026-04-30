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

(** A [TimeRange] denotes the half-open interval
    [[time_range_start r, time_range_end r)). *)
Record TimeRange := mkTimeRange
  { time_range_start : Time;
    time_range_end : Time }.

Definition time_range_wf_b (r : TimeRange) : bool :=
  time_range_start r <? time_range_end r.

Definition time_range_contains (r : TimeRange) (t : Time) : Prop :=
  time_range_start r <= t < time_range_end r.

Fixpoint time_ranges_cover_from_b
    (expected_start : Time)
    (ranges : list TimeRange)
    (limit : Time) : bool :=
  match ranges with
  | [] => expected_start =? limit
  | r :: ranges' =>
      (expected_start =? time_range_start r)
      &&
      time_range_wf_b r
      &&
      time_ranges_cover_from_b (time_range_end r) ranges' limit
  end.

Definition time_ranges_cover_horizon_b
    (H : Time)
    (ranges : list TimeRange) : bool :=
  time_ranges_cover_from_b 0 ranges (S H).

Lemma time_ranges_cover_from_b_nil_true :
  forall expected_start limit,
    time_ranges_cover_from_b expected_start [] limit = true ->
    expected_start = limit.
Proof.
  intros expected_start limit Hcover.
  simpl in Hcover.
  now apply Nat.eqb_eq in Hcover.
Qed.

Lemma time_ranges_cover_from_b_cons_true :
  forall expected_start r ranges limit,
    time_ranges_cover_from_b expected_start (r :: ranges) limit = true ->
    expected_start = time_range_start r /\
    time_range_start r < time_range_end r /\
    time_ranges_cover_from_b (time_range_end r) ranges limit = true.
Proof.
  intros expected_start r ranges limit Hcover.
  simpl in Hcover.
  rewrite !andb_true_iff in Hcover.
  destruct Hcover as [[Hstart Hwf] Htail].
  apply Nat.eqb_eq in Hstart.
  apply Nat.ltb_lt in Hwf.
  repeat split; assumption.
Qed.

Lemma time_ranges_cover_from_b_contains :
  forall ranges expected_start limit t,
    time_ranges_cover_from_b expected_start ranges limit = true ->
    expected_start <= t < limit ->
    exists r,
      In r ranges /\ time_range_contains r t.
Proof.
  induction ranges as [|r ranges IH]; intros expected_start limit t Hcover Ht.
  - apply time_ranges_cover_from_b_nil_true in Hcover.
    lia.
  - destruct
      (time_ranges_cover_from_b_cons_true
         expected_start r ranges limit Hcover)
      as [Hstart [Hwf Htail]].
    destruct (t <? time_range_end r) eqn:Ht_end.
    + exists r.
      split; [left; reflexivity|].
      unfold time_range_contains.
      apply Nat.ltb_lt in Ht_end.
      lia.
    + apply Nat.ltb_ge in Ht_end.
      destruct (IH (time_range_end r) limit t Htail) as [r' [Hin Hcontains]].
      * lia.
      * exists r'.
        split; [right; exact Hin|exact Hcontains].
Qed.

Lemma time_ranges_cover_horizon_b_contains :
  forall H ranges t,
    time_ranges_cover_horizon_b H ranges = true ->
    t <= H ->
    exists r,
      In r ranges /\ time_range_contains r t.
Proof.
  intros H ranges t Hcover Ht.
  unfold time_ranges_cover_horizon_b in Hcover.
  eapply time_ranges_cover_from_b_contains; eauto.
  lia.
Qed.

Definition jittered_compact_basis_row_windows
    (row : Time * list Time) : list (Time * Time) :=
  let '(t2, left_edges) := row in
  map (fun t1 => (t1, t2)) left_edges.

Definition jittered_compact_basis_block_windows
    (block : JitteredCompactDbfBasis) : list (Time * Time) :=
  concat (map jittered_compact_basis_row_windows block).

Definition jittered_compact_basis_windows
    (basis : JitteredCompactDbfBasis) : list (Time * Time) :=
  flat_map
    (fun row =>
       let '(t2, left_edges) := row in
       map (fun t1 => (t1, t2)) left_edges)
    basis.

Lemma forallb_concat :
  forall (A : Type) (p : A -> bool) xss,
    forallb p (concat xss) = forallb (forallb p) xss.
Proof.
  intros A p xss.
  induction xss as [|xs xss IH]; simpl.
  - reflexivity.
  - rewrite forallb_app.
    rewrite IH.
    reflexivity.
Qed.

Lemma forallb_concat_map :
  forall (A B : Type) (p : B -> bool) (f : A -> list B) xs,
    forallb p (concat (map f xs)) =
    forallb (fun x => forallb p (f x)) xs.
Proof.
  intros A B p f xs.
  induction xs as [|x xs IH]; simpl.
  - reflexivity.
  - rewrite forallb_app.
    rewrite IH.
    reflexivity.
Qed.

Lemma jittered_compact_basis_windows_eq_concat_rows :
  forall basis,
    jittered_compact_basis_windows basis =
    concat (map jittered_compact_basis_row_windows basis).
Proof.
  intros basis.
  induction basis as [|[t2 left_edges] basis IH]; simpl.
  - reflexivity.
  - rewrite IH.
    reflexivity.
Qed.

Lemma jittered_compact_basis_windows_eq_block_windows :
  forall basis,
    jittered_compact_basis_windows basis =
    jittered_compact_basis_block_windows basis.
Proof.
  intros basis.
  unfold jittered_compact_basis_block_windows.
  apply jittered_compact_basis_windows_eq_concat_rows.
Qed.

Lemma jittered_compact_basis_block_windows_concat :
  forall blocks,
    jittered_compact_basis_block_windows (concat blocks) =
    concat (map jittered_compact_basis_block_windows blocks).
Proof.
  intros blocks.
  induction blocks as [|block blocks IH]; simpl.
  - reflexivity.
  - unfold jittered_compact_basis_block_windows in *.
    rewrite map_app.
    rewrite concat_app.
    rewrite IH.
    reflexivity.
Qed.

Lemma jittered_compact_basis_windows_concat_blocks :
  forall blocks,
    jittered_compact_basis_windows (concat blocks) =
    concat (map jittered_compact_basis_block_windows blocks).
Proof.
  intros blocks.
  rewrite jittered_compact_basis_windows_eq_block_windows.
  apply jittered_compact_basis_block_windows_concat.
Qed.

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

Definition jittered_fast_compact_basis_dbf_window_ok
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jitter : TaskId -> Time)
    (enumT : list TaskId)
    (w : Time * Time) : bool :=
  let '(t1, t2) := w in
  (t1 <=? t2)
  &&
  (taskset_jittered_periodic_fast_dbf_window
     tasks offset jitter enumT t1 t2 <=? t2 - t1).

Definition jittered_fast_compact_basis_dbf_test
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jitter : TaskId -> Time)
    (enumT : list TaskId)
    (basis : JitteredCompactDbfBasis) : bool :=
  forallb
    (jittered_fast_compact_basis_dbf_window_ok
       tasks offset jitter enumT)
    (jittered_compact_basis_windows basis).

Definition jittered_fast_compact_basis_dbf_row_test
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jitter : TaskId -> Time)
    (enumT : list TaskId)
    (row : Time * list Time) : bool :=
  forallb
    (jittered_fast_compact_basis_dbf_window_ok
       tasks offset jitter enumT)
    (jittered_compact_basis_row_windows row).

Definition jittered_fast_compact_basis_dbf_block_test
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jitter : TaskId -> Time)
    (enumT : list TaskId)
    (block : JitteredCompactDbfBasis) : bool :=
  forallb
    (jittered_fast_compact_basis_dbf_window_ok
       tasks offset jitter enumT)
    (jittered_compact_basis_block_windows block).

Definition jittered_fast_compact_basis_dbf_blocks_test
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jitter : TaskId -> Time)
    (enumT : list TaskId)
    (blocks : list JitteredCompactDbfBasis) : bool :=
  forallb
    (jittered_fast_compact_basis_dbf_block_test
       tasks offset jitter enumT)
    blocks.

Definition jittered_identity_compact_basis_upto
    (H : Time) : JitteredCompactDbfBasis :=
  map (fun t2 => (t2, bounded_time_points t2)) (bounded_time_points H).

Definition jittered_reduced_left_edge_b
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jitter : TaskId -> Time)
    (enumT : list TaskId)
    (t2 t1 : Time) : bool :=
  Nat.eqb t1 t2
  || negb
       (Nat.eqb
          (taskset_jittered_periodic_fast_dbf_window
             tasks offset jitter enumT t1 t2)
          (taskset_jittered_periodic_fast_dbf_window
             tasks offset jitter enumT (S t1) t2)).

Definition jittered_reduced_left_edges_for_t2
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jitter : TaskId -> Time)
    (enumT : list TaskId)
    (t2 : Time) : list Time :=
  filter
    (jittered_reduced_left_edge_b tasks offset jitter enumT t2)
    (bounded_time_points t2).

Definition jittered_reduced_compact_basis_upto
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jitter : TaskId -> Time)
    (enumT : list TaskId)
    (H : Time) : JitteredCompactDbfBasis :=
  map
    (fun t2 =>
       (t2, jittered_reduced_left_edges_for_t2 tasks offset jitter enumT t2))
    (bounded_time_points H).

Lemma jittered_reduced_left_edge_b_false_eq :
  forall tasks offset jitter enumT t1 t2,
    t1 < t2 ->
    jittered_reduced_left_edge_b tasks offset jitter enumT t2 t1 = false ->
    taskset_jittered_periodic_dbf_window tasks offset jitter enumT t1 t2 =
  taskset_jittered_periodic_dbf_window tasks offset jitter enumT (S t1) t2.
Proof.
  intros tasks offset jitter enumT t1 t2 Hlt Hselected.
  unfold jittered_reduced_left_edge_b in Hselected.
  assert (Hneq : (t1 =? t2) = false).
  { apply Nat.eqb_neq. lia. }
  rewrite Hneq in Hselected.
  simpl in Hselected.
  apply negb_false_iff in Hselected.
  apply Nat.eqb_eq in Hselected.
  repeat rewrite <- taskset_jittered_periodic_fast_dbf_window_eq_enumerated
    at 1.
  exact Hselected.
Qed.

Lemma jittered_reduced_left_edges_for_t2_covers :
  forall tasks offset jitter enumT t1 n,
    exists l,
      In l
        (jittered_reduced_left_edges_for_t2
           tasks offset jitter enumT (t1 + n)) /\
      t1 <= l /\
      l <= t1 + n /\
      taskset_jittered_periodic_dbf_window
        tasks offset jitter enumT t1 (t1 + n) =
      taskset_jittered_periodic_dbf_window
        tasks offset jitter enumT l (t1 + n).
Proof.
  intros tasks offset jitter enumT t1 n.
  revert t1.
  induction n as [|n IH]; intros t1.
  - exists t1.
    repeat split; try lia.
    unfold jittered_reduced_left_edges_for_t2.
    apply filter_In.
    split.
    + unfold bounded_time_points.
      rewrite in_seq.
      lia.
    + unfold jittered_reduced_left_edge_b.
      replace (t1 + 0) with t1 by lia.
      rewrite Nat.eqb_refl.
      reflexivity.
  - destruct
      (jittered_reduced_left_edge_b
         tasks offset jitter enumT (t1 + S n) t1) eqn:Hselected.
    + exists t1.
      repeat split; try lia.
      unfold jittered_reduced_left_edges_for_t2.
      apply filter_In.
      split.
      * unfold bounded_time_points.
        rewrite in_seq.
        lia.
      * exact Hselected.
    + destruct (IH (S t1)) as [l [Hin [Hle1 [Hle2 Hdemand]]]].
      exists l.
      pose proof
        (jittered_reduced_left_edge_b_false_eq
           tasks offset jitter enumT t1 (t1 + S n) ltac:(lia) Hselected)
        as Hstep.
      replace (t1 + S n) with (S t1 + n) in * by lia.
      split; [exact Hin|].
      repeat split; try lia.
Qed.

Lemma jittered_reduced_compact_basis_covers_upto :
  forall tasks offset jitter enumT H,
    jittered_compact_basis_covers_upto
      tasks offset jitter enumT H
      (jittered_reduced_compact_basis_upto tasks offset jitter enumT H).
Proof.
  intros tasks offset jitter enumT H t1 t2 Hle12 Hle2H.
  assert (Hn : exists n, t2 = t1 + n).
  { exists (t2 - t1). lia. }
  destruct Hn as [n Ht2].
  destruct
    (jittered_reduced_left_edges_for_t2_covers
       tasks offset jitter enumT t1 n)
    as [l [Hin [Hle1l [Hlel2 Hdemand]]]].
  exists l.
  split.
  - unfold jittered_reduced_compact_basis_upto,
           jittered_compact_basis_windows.
    apply in_flat_map.
    exists
      (t2, jittered_reduced_left_edges_for_t2 tasks offset jitter enumT t2).
    split.
    + apply in_map_iff.
      exists t2.
      split; [reflexivity|].
      unfold bounded_time_points.
      rewrite in_seq.
      lia.
    + apply in_map_iff.
      exists l.
      split; [reflexivity|].
      subst t2.
      exact Hin.
  - unfold jittered_left_edge_covers.
    subst t2.
    repeat split; try lia.
Qed.

Lemma jittered_fast_compact_basis_dbf_row_test_eq :
  forall tasks offset jitter enumT row,
    jittered_fast_compact_basis_dbf_row_test
      tasks offset jitter enumT row =
    jittered_fast_compact_basis_dbf_test
      tasks offset jitter enumT [row].
Proof.
  intros tasks offset jitter enumT [t2 left_edges].
  unfold jittered_fast_compact_basis_dbf_row_test,
         jittered_fast_compact_basis_dbf_test,
         jittered_compact_basis_row_windows,
         jittered_compact_basis_windows.
  simpl.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma jittered_fast_compact_basis_dbf_block_test_eq :
  forall tasks offset jitter enumT block,
    jittered_fast_compact_basis_dbf_block_test
      tasks offset jitter enumT block =
    jittered_fast_compact_basis_dbf_test
      tasks offset jitter enumT block.
Proof.
  intros tasks offset jitter enumT block.
  unfold jittered_fast_compact_basis_dbf_block_test,
         jittered_fast_compact_basis_dbf_test.
  now rewrite jittered_compact_basis_windows_eq_block_windows.
Qed.

Lemma jittered_fast_compact_basis_dbf_blocks_test_eq :
  forall tasks offset jitter enumT blocks,
    jittered_fast_compact_basis_dbf_blocks_test
      tasks offset jitter enumT blocks =
    jittered_fast_compact_basis_dbf_test
      tasks offset jitter enumT (concat blocks).
Proof.
  intros tasks offset jitter enumT blocks.
  unfold jittered_fast_compact_basis_dbf_blocks_test,
         jittered_fast_compact_basis_dbf_block_test,
         jittered_fast_compact_basis_dbf_test.
  rewrite jittered_compact_basis_windows_concat_blocks.
  symmetry.
  apply forallb_concat_map.
Qed.

Theorem jittered_fast_compact_basis_dbf_blocks_test_implies_concat :
  forall tasks offset jitter enumT blocks,
    jittered_fast_compact_basis_dbf_blocks_test
      tasks offset jitter enumT blocks = true ->
    jittered_fast_compact_basis_dbf_test
      tasks offset jitter enumT (concat blocks) = true.
Proof.
  intros tasks offset jitter enumT blocks Hblocks.
  now rewrite <- jittered_fast_compact_basis_dbf_blocks_test_eq.
Qed.

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
