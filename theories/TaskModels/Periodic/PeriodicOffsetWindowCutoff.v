From Stdlib Require Import Arith Arith.PeanoNat Lia List Bool Sorting.Permutation.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import TaskModels.Periodic.PeriodicConcreteAnalysis.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Periodic.PeriodicWindowDemandBound.

Import ListNotations.

(** Infrastructure for the future infinite offset-aware window-DBF cutoff.
    This file intentionally stops at arithmetic periodicity facts; the full
    window-DBF cutoff theorem is a later proof layer. *)

Fixpoint periodic_max_offset
    (offset : TaskId -> Time)
    (enumT : list TaskId) : Time :=
  match enumT with
  | [] => 0
  | τ :: enumT' =>
      Nat.max (offset τ) (periodic_max_offset offset enumT')
  end.

Definition offset_window_dbf_cutoff_bound
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (enumT : list TaskId) : Time :=
  let horizon_base :=
      periodic_max_offset offset enumT +
      periodic_max_relative_deadline tasks enumT in
  horizon_base + S horizon_base * periodic_hyperperiod tasks enumT.

Definition offset_window_dbf_test_by_cutoff
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (enumT : list TaskId) : bool :=
  window_dbf_test_upto
    tasks offset enumT
    (offset_window_dbf_cutoff_bound tasks offset enumT).

Lemma periodic_max_offset_ge :
  forall offset enumT τ,
    In τ enumT ->
    offset τ <= periodic_max_offset offset enumT.
Proof.
  intros offset enumT τ Hin.
  induction enumT as [|τ' enumT IH]; simpl in *.
  - contradiction.
  - destruct Hin as [-> | Hin].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans.
      * apply IH. exact Hin.
      * apply Nat.le_max_r.
Qed.

Lemma hyperperiod_as_task_period_multiple :
  forall tasks enumT τ,
    In τ enumT ->
    exists q,
      periodic_hyperperiod tasks enumT =
      q * task_period (tasks τ).
Proof.
  intros tasks enumT τ Hin.
  destruct (periodic_hyperperiod_divides tasks enumT τ Hin) as [q Hq].
  exists q.
  exact Hq.
Qed.

Lemma expected_release_shift_by_hyperperiod :
  forall tasks offset enumT τ k,
    In τ enumT ->
    exists q,
      forall n,
        expected_release tasks offset τ (k + n * q) =
        expected_release tasks offset τ k +
        n * periodic_hyperperiod tasks enumT.
Proof.
  intros tasks offset enumT τ k Hin.
  destruct (hyperperiod_as_task_period_multiple tasks enumT τ Hin) as [q Hhp].
  exists q.
  intros n.
  unfold expected_release.
  rewrite Hhp.
  lia.
Qed.

Lemma expected_deadline_shift_by_hyperperiod :
  forall tasks offset enumT τ k,
    In τ enumT ->
    exists q,
      forall n,
        expected_abs_deadline tasks offset τ (k + n * q) =
        expected_abs_deadline tasks offset τ k +
        n * periodic_hyperperiod tasks enumT.
Proof.
  intros tasks offset enumT τ k Hin.
  destruct (hyperperiod_as_task_period_multiple tasks enumT τ Hin) as [q Hhp].
  exists q.
  intros n.
  unfold expected_abs_deadline, expected_release.
  rewrite Hhp.
  lia.
Qed.

Lemma nodup_map_add_const :
  forall l c,
    NoDup l ->
    NoDup (map (fun x => x + c) l).
Proof.
  intros l c Hnodup.
  induction Hnodup as [|x l Hnotin Hnodup IH]; simpl.
  - constructor.
  - constructor.
    + intro Hin.
      apply in_map_iff in Hin.
      destruct Hin as [y [Hy Hin]].
      assert (x = y) by lia.
      subst y.
      apply Hnotin.
      exact Hin.
    + exact IH.
Qed.

Lemma periodic_index_in_window_shift_by_hyperperiod :
  forall tasks offset enumT τ t1 t2 k n q,
    In τ enumT ->
    periodic_hyperperiod tasks enumT = q * task_period (tasks τ) ->
    periodic_index_in_window tasks offset τ t1 t2 k = true ->
    periodic_index_in_window
      tasks offset τ
      (t1 + n * periodic_hyperperiod tasks enumT)
      (t2 + n * periodic_hyperperiod tasks enumT)
      (k + n * q) = true.
Proof.
  intros tasks offset enumT τ t1 t2 k n q _Hin Hhp Hwin.
  unfold periodic_index_in_window in *.
  rewrite !andb_true_iff in *.
  rewrite !Nat.leb_le in *.
  destruct Hwin as [Hrel Hdl].
  split.
  - unfold expected_release in *.
    rewrite Hhp.
    replace (offset τ + (k + n * q) * task_period (tasks τ))
      with (offset τ + k * task_period (tasks τ) +
            n * (q * task_period (tasks τ))) by nia.
    lia.
  - unfold expected_abs_deadline, expected_release in *.
    rewrite Hhp.
    replace
      (offset τ + (k + n * q) * task_period (tasks τ) +
       task_relative_deadline (tasks τ))
      with
      (offset τ + k * task_period (tasks τ) +
       task_relative_deadline (tasks τ) +
       n * (q * task_period (tasks τ))) by nia.
    lia.
Qed.

Lemma periodic_shifted_window_index_ge_shift :
  forall tasks offset enumT τ t1 t2 k n q,
    In τ enumT ->
    periodic_max_offset offset enumT <= t1 ->
    0 < task_period (tasks τ) ->
    periodic_hyperperiod tasks enumT = q * task_period (tasks τ) ->
    periodic_index_in_window
      tasks offset τ
      (t1 + n * periodic_hyperperiod tasks enumT)
      (t2 + n * periodic_hyperperiod tasks enumT)
      k = true ->
    n * q <= k.
Proof.
  intros tasks offset enumT τ t1 t2 k n q Hin Hmax Hp Hhp Hwin.
  unfold periodic_index_in_window in Hwin.
  rewrite andb_true_iff in Hwin.
  rewrite !Nat.leb_le in Hwin.
  destruct Hwin as [Hrel _].
  pose proof (periodic_max_offset_ge offset enumT τ Hin) as Hoff.
  unfold expected_release in Hrel.
  rewrite Hhp in Hrel.
  destruct (le_gt_dec (n * q) k) as [Hle | Hgt].
  - exact Hle.
  - assert (k * task_period (tasks τ) <
            (n * q) * task_period (tasks τ)).
    {
      apply Nat.mul_lt_mono_pos_r.
      - exact Hp.
      - exact Hgt.
    }
    lia.
Qed.

Lemma periodic_index_in_shifted_window_sub_hyperperiod :
  forall tasks offset enumT τ t1 t2 k n q,
    In τ enumT ->
    periodic_max_offset offset enumT <= t1 ->
    0 < task_period (tasks τ) ->
    periodic_hyperperiod tasks enumT = q * task_period (tasks τ) ->
    periodic_index_in_window
      tasks offset τ
      (t1 + n * periodic_hyperperiod tasks enumT)
      (t2 + n * periodic_hyperperiod tasks enumT)
      k = true ->
    periodic_index_in_window tasks offset τ t1 t2 (k - n * q) = true.
Proof.
  intros tasks offset enumT τ t1 t2 k n q Hin Hmax Hp Hhp Hwin.
  pose proof (periodic_shifted_window_index_ge_shift
                tasks offset enumT τ t1 t2 k n q
                Hin Hmax Hp Hhp Hwin) as Hge.
  unfold periodic_index_in_window in *.
  rewrite !andb_true_iff in *.
  rewrite !Nat.leb_le in *.
  destruct Hwin as [Hrel Hdl].
  split.
  - unfold expected_release in *.
    rewrite Hhp in Hrel.
    replace (k * task_period (tasks τ))
      with ((k - n * q) * task_period (tasks τ) +
            (n * q) * task_period (tasks τ)) in Hrel.
    2:{
      rewrite Nat.mul_sub_distr_r by exact Hge.
      assert ((n * q) * task_period (tasks τ) <=
              k * task_period (tasks τ)).
      { apply Nat.mul_le_mono_r. exact Hge. }
      lia.
    }
    lia.
  - unfold expected_abs_deadline, expected_release in *.
    rewrite Hhp in Hdl.
    replace (k * task_period (tasks τ))
      with ((k - n * q) * task_period (tasks τ) +
            (n * q) * task_period (tasks τ)) in Hdl.
    2:{
      rewrite Nat.mul_sub_distr_r by exact Hge.
      assert ((n * q) * task_period (tasks τ) <=
              k * task_period (tasks τ)).
      { apply Nat.mul_le_mono_r. exact Hge. }
      lia.
    }
    lia.
Qed.

Lemma periodic_dbf_window_shift_by_hyperperiod :
  forall tasks offset enumT τ t1 t2 n,
    In τ enumT ->
    periodic_max_offset offset enumT <= t1 ->
    0 < task_period (tasks τ) ->
    t1 <= t2 ->
    periodic_dbf_window
      tasks offset τ
      (t1 + n * periodic_hyperperiod tasks enumT)
      (t2 + n * periodic_hyperperiod tasks enumT) =
    periodic_dbf_window tasks offset τ t1 t2.
Proof.
  intros tasks offset enumT τ t1 t2 n Hin Hmax Hp Hle12.
  destruct (hyperperiod_as_task_period_multiple tasks enumT τ Hin) as [q Hhp].
  unfold periodic_dbf_window.
  set (hp := periodic_hyperperiod tasks enumT).
  set (m := n * q).
  set (time_shift := n * hp).
  set (old :=
    filter (periodic_index_in_window tasks offset τ t1 t2) (seq 0 (S t2))).
  set (shifted :=
    filter
      (periodic_index_in_window tasks offset τ (t1 + time_shift) (t2 + time_shift))
      (seq 0 (S (t2 + time_shift)))).
  replace (length shifted) with (length (map (fun k => k + m) old)).
  2: {
    apply Permutation_length.
    apply NoDup_Permutation.
    - apply nodup_map_add_const.
      subst old.
      apply NoDup_filter.
      apply seq_NoDup.
    - subst shifted.
      apply NoDup_filter.
      apply seq_NoDup.
    - intros k.
      split.
      + intro Hk.
        apply in_map_iff in Hk.
        destruct Hk as [k0 [Hk Hk0]].
        subst k.
        subst old shifted m time_shift hp.
        apply filter_In in Hk0.
        destruct Hk0 as [Hin0 Hwin0].
        apply filter_In.
        split.
        * rewrite in_seq in *.
          destruct Hin0 as [_ Hk0le].
          split; [lia|].
          rewrite Hhp.
          assert (q <= q * task_period (tasks τ)).
          { destruct q; simpl; nia. }
          nia.
        * eapply periodic_index_in_window_shift_by_hyperperiod; eauto.
      + intro Hk.
        subst old shifted m time_shift hp.
        apply filter_In in Hk.
        destruct Hk as [Hkin Hwin].
        pose proof (periodic_shifted_window_index_ge_shift
                      tasks offset enumT τ t1 t2 k n q
                      Hin Hmax Hp Hhp Hwin) as Hge.
        apply in_map_iff.
        exists (k - n * q).
        split.
        * lia.
        * apply filter_In.
          split.
          -- rewrite in_seq in *.
             split; [lia|].
             apply periodic_index_in_shifted_window_sub_hyperperiod
               with (enumT := enumT) (n := n) (q := q) in Hwin; eauto.
             unfold periodic_index_in_window in Hwin.
             rewrite andb_true_iff in Hwin.
             rewrite !Nat.leb_le in Hwin.
             destruct Hwin as [_ Hdl].
             unfold expected_abs_deadline, expected_release in Hdl.
             assert (k - n * q <=
                     (k - n * q) * task_period (tasks τ)).
             { destruct (k - n * q); simpl; nia. }
             lia.
          -- eapply periodic_index_in_shifted_window_sub_hyperperiod; eauto.
  }
  rewrite length_map.
  reflexivity.
Qed.

Lemma taskset_periodic_dbf_window_shift_by_hyperperiod :
  forall tasks offset enumT t1 t2 n,
    (forall τ, In τ enumT -> 0 < task_period (tasks τ)) ->
    periodic_max_offset offset enumT <= t1 ->
    t1 <= t2 ->
    taskset_periodic_dbf_window
      tasks offset enumT
      (t1 + n * periodic_hyperperiod tasks enumT)
      (t2 + n * periodic_hyperperiod tasks enumT) =
    taskset_periodic_dbf_window tasks offset enumT t1 t2.
Proof.
  intros tasks offset enumT t1 t2 n Hwf Hmax Hle12.
  assert (Hshift :
    forall enumT',
      (forall τ, In τ enumT' -> In τ enumT) ->
      taskset_periodic_dbf_window
        tasks offset enumT'
        (t1 + n * periodic_hyperperiod tasks enumT)
        (t2 + n * periodic_hyperperiod tasks enumT) =
      taskset_periodic_dbf_window tasks offset enumT' t1 t2).
  {
    induction enumT' as [|τ enumT' IH]; intros Hincl; simpl.
    - reflexivity.
    - assert (Hin_full : In τ enumT).
      { apply Hincl. now left. }
      assert (Hpτ : 0 < task_period (tasks τ)).
      { apply Hwf. exact Hin_full. }
      rewrite (periodic_dbf_window_shift_by_hyperperiod
                 tasks offset enumT τ t1 t2 n
                 Hin_full Hmax Hpτ Hle12).
      rewrite IH.
      + reflexivity.
      + intros τ' Hin.
        apply Hincl.
        now right.
  }
  apply Hshift.
  intros τ Hin.
  exact Hin.
Qed.

Theorem offset_window_dbf_check_by_cutoff_post_offset_shifted :
  forall tasks offset enumT t1 t2 n,
    (forall τ, In τ enumT -> 0 < task_period (tasks τ)) ->
    offset_window_dbf_test_by_cutoff tasks offset enumT = true ->
    let shift := n * periodic_hyperperiod tasks enumT in
    shift <= t1 ->
    shift <= t2 ->
    periodic_max_offset offset enumT <= t1 - shift ->
    t1 <= t2 ->
    t2 - shift <= offset_window_dbf_cutoff_bound tasks offset enumT ->
    taskset_periodic_dbf_window tasks offset enumT t1 t2 <= t2 - t1.
Proof.
  intros tasks offset enumT t1 t2 n Hwf Htest shift Hshift_le_t1
         Hshift_le_t2 Hpost_offset Hle12 Hcutoff.
  assert (Hle_shifted : t1 - shift <= t2 - shift) by lia.
  pose proof
    (taskset_periodic_dbf_window_shift_by_hyperperiod
       tasks offset enumT (t1 - shift) (t2 - shift) n
       Hwf Hpost_offset Hle_shifted) as Hshift_dbf.
  unfold shift in Hshift_dbf.
  replace (t1 - n * periodic_hyperperiod tasks enumT +
           n * periodic_hyperperiod tasks enumT) with t1 in Hshift_dbf by lia.
  replace (t2 - n * periodic_hyperperiod tasks enumT +
           n * periodic_hyperperiod tasks enumT) with t2 in Hshift_dbf by lia.
  rewrite Hshift_dbf.
  replace (t2 - t1) with ((t2 - shift) - (t1 - shift)) by lia.
  unfold offset_window_dbf_test_by_cutoff in Htest.
  eapply window_dbf_test_upto_true_implies_bounded_window_dbf; eauto.
Qed.
