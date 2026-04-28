From Stdlib Require Import Arith Arith.PeanoNat Lia List Bool Sorting.Permutation.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import TaskModels.Periodic.PeriodicConcreteAnalysis.
From RocqSched Require Import TaskModels.Periodic.PeriodicOffsetWindowCutoff.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicWindowDemandBound.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicConcreteAnalysis.

Import ListNotations.

(** * Conservative bounded cutoff surface for jittered-periodic window DBF

    The bound extends the existing offset-window cutoff by the maximum release
    jitter.  This batch proves soundness for windows bounded by the cutoff; the
    later hyperperiod-shift theorem will lift this to all windows. *)

Fixpoint jittered_max_release_jitter
    (jitter : TaskId -> Time)
    (enumT : list TaskId) : Time :=
  match enumT with
  | [] => 0
  | τ :: enumT' =>
      Nat.max (jitter τ) (jittered_max_release_jitter jitter enumT')
  end.

Definition jittered_offset_window_dbf_cutoff_bound
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jitter : TaskId -> Time)
    (enumT : list TaskId) : Time :=
  offset_window_dbf_cutoff_bound tasks offset enumT +
  jittered_max_release_jitter jitter enumT.

Definition jittered_offset_window_dbf_test_by_cutoff
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jitter : TaskId -> Time)
    (enumT : list TaskId) : bool :=
  jittered_window_dbf_test_upto
    tasks offset jitter enumT
    (jittered_offset_window_dbf_cutoff_bound tasks offset jitter enumT).

Lemma jittered_max_release_jitter_ge :
  forall jitter enumT τ,
    In τ enumT ->
    jitter τ <= jittered_max_release_jitter jitter enumT.
Proof.
  intros jitter enumT τ Hin.
  induction enumT as [|τ' enumT IH]; simpl in *.
  - contradiction.
  - destruct Hin as [-> | Hin].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans.
      * apply IH. exact Hin.
      * apply Nat.le_max_r.
Qed.

Theorem jittered_offset_window_dbf_test_by_cutoff_bounded_sound :
  forall tasks offset jitter enumT t1 t2,
    jittered_offset_window_dbf_test_by_cutoff tasks offset jitter enumT = true ->
    t1 <= t2 ->
    t2 <= jittered_offset_window_dbf_cutoff_bound tasks offset jitter enumT ->
    taskset_jittered_periodic_dbf_window
      tasks offset jitter enumT t1 t2 <= t2 - t1.
Proof.
  intros tasks offset jitter enumT t1 t2 Htest Hle12 Hle2.
  unfold jittered_offset_window_dbf_test_by_cutoff in Htest.
  eapply jittered_window_dbf_test_upto_true_implies_bounded_window_dbf; eauto.
Qed.

Lemma jittered_index_may_be_in_window_shift_by_hyperperiod :
  forall tasks offset jitter enumT τ t1 t2 k n q,
    In τ enumT ->
    periodic_hyperperiod tasks enumT = q * task_period (tasks τ) ->
    jittered_index_may_be_in_window_b tasks offset jitter τ t1 t2 k = true ->
    jittered_index_may_be_in_window_b
      tasks offset jitter τ
      (t1 + n * periodic_hyperperiod tasks enumT)
      (t2 + n * periodic_hyperperiod tasks enumT)
      (k + n * q) = true.
Proof.
  intros tasks offset jitter enumT τ t1 t2 k n q _Hin Hhp Hwin.
  apply jittered_index_may_be_in_window_b_spec.
  apply jittered_index_may_be_in_window_b_spec in Hwin.
  unfold jittered_index_may_be_in_window in *.
  destruct Hwin as [Hdl Hwin].
  split; [lia|].
  unfold expected_release in *.
  rewrite Hhp.
  replace (offset τ + (k + n * q) * task_period (tasks τ))
    with (offset τ + k * task_period (tasks τ) +
          n * (q * task_period (tasks τ))) by nia.
  apply Nat.min_glb.
  - apply Nat.max_lub.
    + pose proof (Nat.min_glb_l _ _ _ Hwin). lia.
    + pose proof (Nat.min_glb_l _ _ _ Hwin). lia.
  - apply Nat.max_lub.
    + pose proof (Nat.min_glb_r _ _ _ Hwin). lia.
    + pose proof (Nat.min_glb_r _ _ _ Hwin). lia.
Qed.

Lemma jittered_shifted_window_index_ge_shift :
  forall tasks offset jitter enumT τ t1 t2 k n q,
    In τ enumT ->
    periodic_max_offset offset enumT +
      jittered_max_release_jitter jitter enumT <= t1 ->
    0 < task_period (tasks τ) ->
    periodic_hyperperiod tasks enumT = q * task_period (tasks τ) ->
    jittered_index_may_be_in_window_b
      tasks offset jitter τ
      (t1 + n * periodic_hyperperiod tasks enumT)
      (t2 + n * periodic_hyperperiod tasks enumT)
      k = true ->
    n * q <= k.
Proof.
  intros tasks offset jitter enumT τ t1 t2 k n q Hin Hstart Hp Hhp Hwin.
  apply jittered_index_may_be_in_window_b_spec in Hwin.
  unfold jittered_index_may_be_in_window in Hwin.
  destruct Hwin as [_ Hwin].
  pose proof (periodic_max_offset_ge offset enumT τ Hin) as Hoff.
  pose proof (jittered_max_release_jitter_ge jitter enumT τ Hin) as Hj.
  pose proof (Nat.min_glb_r _ _ _ Hwin) as Hlatest.
  unfold expected_release in Hlatest.
  rewrite Hhp in Hlatest.
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

Lemma jittered_index_in_shifted_window_sub_hyperperiod :
  forall tasks offset jitter enumT τ t1 t2 k n q,
    In τ enumT ->
    periodic_max_offset offset enumT +
      jittered_max_release_jitter jitter enumT <= t1 ->
    0 < task_period (tasks τ) ->
    periodic_hyperperiod tasks enumT = q * task_period (tasks τ) ->
    jittered_index_may_be_in_window_b
      tasks offset jitter τ
      (t1 + n * periodic_hyperperiod tasks enumT)
      (t2 + n * periodic_hyperperiod tasks enumT)
      k = true ->
    jittered_index_may_be_in_window_b
      tasks offset jitter τ t1 t2 (k - n * q) = true.
Proof.
  intros tasks offset jitter enumT τ t1 t2 k n q Hin Hstart Hp Hhp Hwin.
  pose proof (jittered_shifted_window_index_ge_shift
                tasks offset jitter enumT τ t1 t2 k n q
                Hin Hstart Hp Hhp Hwin) as Hge.
  apply jittered_index_may_be_in_window_b_spec.
  apply jittered_index_may_be_in_window_b_spec in Hwin.
  unfold jittered_index_may_be_in_window in *.
  destruct Hwin as [Hdl Hwin].
  split; [lia|].
  unfold expected_release in *.
  rewrite Hhp in Hwin.
  replace (k * task_period (tasks τ))
    with ((k - n * q) * task_period (tasks τ) +
          (n * q) * task_period (tasks τ)) in Hwin.
  2:{
    rewrite Nat.mul_sub_distr_r by exact Hge.
    assert ((n * q) * task_period (tasks τ) <=
            k * task_period (tasks τ)).
    { apply Nat.mul_le_mono_r. exact Hge. }
    lia.
  }
  apply Nat.min_glb.
  - apply Nat.max_lub.
    + pose proof (Nat.min_glb_l _ _ _ Hwin). lia.
    + pose proof (Nat.min_glb_l _ _ _ Hwin). lia.
  - apply Nat.max_lub.
    + pose proof (Nat.min_glb_r _ _ _ Hwin). lia.
    + pose proof (Nat.min_glb_r _ _ _ Hwin). lia.
Qed.

Lemma jittered_periodic_dbf_window_shift_by_hyperperiod :
  forall tasks offset jitter enumT τ t1 t2 n,
    In τ enumT ->
    periodic_max_offset offset enumT +
      jittered_max_release_jitter jitter enumT <= t1 ->
    0 < task_period (tasks τ) ->
    t1 <= t2 ->
    jittered_periodic_dbf_window
      tasks offset jitter τ
      (t1 + n * periodic_hyperperiod tasks enumT)
      (t2 + n * periodic_hyperperiod tasks enumT) =
    jittered_periodic_dbf_window tasks offset jitter τ t1 t2.
Proof.
  intros tasks offset jitter enumT τ t1 t2 n Hin Hstart Hp Hle12.
  destruct (hyperperiod_as_task_period_multiple tasks enumT τ Hin) as [q Hhp].
  unfold jittered_periodic_dbf_window.
  set (hp := periodic_hyperperiod tasks enumT).
  set (m := n * q).
  set (time_shift := n * hp).
  set (old :=
    filter
      (jittered_index_may_be_in_window_b tasks offset jitter τ t1 t2)
      (seq 0 (S t2))).
  set (shifted :=
    filter
      (jittered_index_may_be_in_window_b
         tasks offset jitter τ (t1 + time_shift) (t2 + time_shift))
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
        * eapply jittered_index_may_be_in_window_shift_by_hyperperiod; eauto.
      + intro Hk.
        subst old shifted m time_shift hp.
        apply filter_In in Hk.
        destruct Hk as [Hkin Hwin].
        pose proof (jittered_shifted_window_index_ge_shift
                      tasks offset jitter enumT τ t1 t2 k n q
                      Hin Hstart Hp Hhp Hwin) as Hge.
        apply in_map_iff.
        exists (k - n * q).
        split.
        * lia.
        * apply filter_In.
          split.
          -- rewrite in_seq in *.
             split; [lia|].
             apply jittered_index_in_shifted_window_sub_hyperperiod
               with (enumT := enumT) (n := n) (q := q) in Hwin; eauto.
             apply jittered_index_may_be_in_window_b_spec in Hwin.
             unfold jittered_index_may_be_in_window in Hwin.
             destruct Hwin as [_ Hwin].
             pose proof (Nat.min_glb_l _ _ _ Hwin) as Hbound.
             unfold expected_release in Hbound.
             assert (k - n * q <=
                     offset τ + (k - n * q) * task_period (tasks τ)).
             { destruct (k - n * q); simpl; nia. }
             lia.
          -- eapply jittered_index_in_shifted_window_sub_hyperperiod; eauto.
  }
  rewrite length_map.
  reflexivity.
Qed.

Lemma taskset_jittered_periodic_dbf_window_shift_by_hyperperiod :
  forall tasks offset jitter enumT t1 t2 n,
    (forall τ, In τ enumT -> 0 < task_period (tasks τ)) ->
    periodic_max_offset offset enumT +
      jittered_max_release_jitter jitter enumT <= t1 ->
    t1 <= t2 ->
    taskset_jittered_periodic_dbf_window
      tasks offset jitter enumT
      (t1 + n * periodic_hyperperiod tasks enumT)
      (t2 + n * periodic_hyperperiod tasks enumT) =
    taskset_jittered_periodic_dbf_window tasks offset jitter enumT t1 t2.
Proof.
  intros tasks offset jitter enumT t1 t2 n Hwf Hstart Hle12.
  assert (Hshift :
    forall enumT',
      (forall τ, In τ enumT' -> In τ enumT) ->
      taskset_jittered_periodic_dbf_window
        tasks offset jitter enumT'
        (t1 + n * periodic_hyperperiod tasks enumT)
        (t2 + n * periodic_hyperperiod tasks enumT) =
      taskset_jittered_periodic_dbf_window tasks offset jitter enumT' t1 t2).
  {
    induction enumT' as [|τ enumT' IH]; intros Hincl; simpl.
    - reflexivity.
    - assert (Hin_full : In τ enumT).
      { apply Hincl. now left. }
      assert (Hpτ : 0 < task_period (tasks τ)).
      { apply Hwf. exact Hin_full. }
      rewrite (jittered_periodic_dbf_window_shift_by_hyperperiod
                 tasks offset jitter enumT τ t1 t2 n
                 Hin_full Hstart Hpτ Hle12).
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

Theorem jittered_offset_window_dbf_check_by_cutoff_post_jitter_shifted :
  forall tasks offset jitter enumT t1 t2 n,
    (forall τ, In τ enumT -> 0 < task_period (tasks τ)) ->
    jittered_offset_window_dbf_test_by_cutoff tasks offset jitter enumT = true ->
    let shift := n * periodic_hyperperiod tasks enumT in
    shift <= t1 ->
    shift <= t2 ->
    periodic_max_offset offset enumT +
      jittered_max_release_jitter jitter enumT <= t1 - shift ->
    t1 <= t2 ->
    t2 - shift <=
      jittered_offset_window_dbf_cutoff_bound tasks offset jitter enumT ->
    taskset_jittered_periodic_dbf_window
      tasks offset jitter enumT t1 t2 <= t2 - t1.
Proof.
  intros tasks offset jitter enumT t1 t2 n Hwf Htest shift Hshift_le_t1
         Hshift_le_t2 Hpost_start Hle12 Hcutoff.
  assert (Hle_shifted : t1 - shift <= t2 - shift) by lia.
  pose proof
    (taskset_jittered_periodic_dbf_window_shift_by_hyperperiod
       tasks offset jitter enumT (t1 - shift) (t2 - shift) n
       Hwf Hpost_start Hle_shifted) as Hshift_dbf.
  unfold shift in Hshift_dbf.
  replace (t1 - n * periodic_hyperperiod tasks enumT +
           n * periodic_hyperperiod tasks enumT) with t1 in Hshift_dbf by lia.
  replace (t2 - n * periodic_hyperperiod tasks enumT +
           n * periodic_hyperperiod tasks enumT) with t2 in Hshift_dbf by lia.
  rewrite Hshift_dbf.
  replace (t2 - t1) with ((t2 - shift) - (t1 - shift)) by lia.
  eapply jittered_offset_window_dbf_test_by_cutoff_bounded_sound; eauto.
Qed.
