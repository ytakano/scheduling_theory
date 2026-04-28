From Stdlib Require Import Arith Arith.PeanoNat Lia List Bool Sorting.Permutation.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import TaskModels.Periodic.PeriodicClassicDBF.
From RocqSched Require Import TaskModels.Periodic.PeriodicConcreteAnalysis.
From RocqSched Require Import TaskModels.Periodic.PeriodicOffsetWindowCutoff.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Periodic.PeriodicWindowDemandBound.
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

Lemma periodic_index_in_window_implies_jittered :
  forall tasks offset jitter τ t1 t2 k,
    periodic_index_in_window tasks offset τ t1 t2 k = true ->
    jittered_index_may_be_in_window_b tasks offset jitter τ t1 t2 k = true.
Proof.
  intros tasks offset jitter τ t1 t2 k Hwin.
  apply jittered_index_may_be_in_window_b_spec.
  unfold periodic_index_in_window in Hwin.
  rewrite andb_true_iff in Hwin.
  rewrite !Nat.leb_le in Hwin.
  destruct Hwin as [Hrel Hdl].
  unfold jittered_index_may_be_in_window.
  split.
  - unfold expected_abs_deadline in Hdl. lia.
  - unfold expected_abs_deadline in Hdl.
    apply Nat.min_glb.
    + apply Nat.max_lub; lia.
    + apply Nat.max_lub; lia.
Qed.

Lemma periodic_dbf_window_le_jittered_periodic_dbf_window :
  forall tasks offset jitter τ t1 t2,
    periodic_dbf_window tasks offset τ t1 t2 <=
    jittered_periodic_dbf_window tasks offset jitter τ t1 t2.
Proof.
  intros tasks offset jitter τ t1 t2.
  unfold periodic_dbf_window, jittered_periodic_dbf_window.
  apply Nat.mul_le_mono_r.
  eapply NoDup_incl_length.
  - apply NoDup_filter.
    apply seq_NoDup.
  - intros k Hk.
    apply filter_In in Hk.
    destruct Hk as [Hseq Hwin].
    apply filter_In.
    split; [exact Hseq|].
    eapply periodic_index_in_window_implies_jittered; eauto.
Qed.

Lemma taskset_periodic_dbf_window_le_jittered_periodic_dbf_window :
  forall tasks offset jitter enumT t1 t2,
    taskset_periodic_dbf_window tasks offset enumT t1 t2 <=
    taskset_jittered_periodic_dbf_window tasks offset jitter enumT t1 t2.
Proof.
  intros tasks offset jitter enumT t1 t2.
  induction enumT as [|τ enumT IH]; simpl.
  - lia.
  - pose proof
      (periodic_dbf_window_le_jittered_periodic_dbf_window
         tasks offset jitter τ t1 t2) as Hhead.
    lia.
Qed.

Lemma jittered_periodic_dbf_window_add_hyperperiod_upper_after_deadline :
  forall tasks offset jitter τ t1 t2 hp,
    t1 + task_relative_deadline (tasks τ) <= t2 ->
    0 < task_period (tasks τ) ->
    Nat.divide (task_period (tasks τ)) hp ->
    jittered_periodic_dbf_window tasks offset jitter τ t1 (t2 + hp) <=
    jittered_periodic_dbf_window tasks offset jitter τ t1 t2 +
      (hp / task_period (tasks τ)) * task_cost (tasks τ).
Proof.
  intros tasks offset jitter τ t1 t2 hp Hcovered Hp Hdiv.
  destruct Hdiv as [q Hhp0].
  assert (Hhp : hp = q * task_period (tasks τ)) by lia.
  set (p := task_period (tasks τ)).
  set (c := task_cost (tasks τ)).
  set (d := task_relative_deadline (tasks τ)).
  set (rel := fun k => expected_release tasks offset τ k).
  set (old :=
    filter
      (jittered_index_may_be_in_window_b tasks offset jitter τ t1 t2)
      (seq 0 (S t2))).
  set (extended :=
    filter
      (jittered_index_may_be_in_window_b tasks offset jitter τ t1 (t2 + hp))
      (seq 0 (S (t2 + hp)))).
  set (new :=
    filter (fun k => t2 - d <? rel k) extended).
  set (kbase := (S (t2 - d) - offset τ + p - 1) / p).
  assert (Hextended_incl : incl extended (old ++ new)).
  {
    intros k Hk.
    subst old new extended rel.
    apply filter_In in Hk.
    destruct Hk as [Hseq Hwin].
    apply jittered_index_may_be_in_window_b_spec in Hwin.
    unfold jittered_index_may_be_in_window in Hwin.
    destruct Hwin as [Hdl Hwin].
    apply in_app_iff.
    destruct (t2 - d <? expected_release tasks offset τ k) eqn:Hnew.
    - right.
      apply filter_In.
      split.
      + apply filter_In.
        split; [exact Hseq|].
        apply jittered_index_may_be_in_window_b_spec.
        unfold jittered_index_may_be_in_window.
        split; [exact Hdl|exact Hwin].
      + exact Hnew.
    - left.
      apply Nat.ltb_ge in Hnew.
      apply filter_In.
      split.
      + rewrite in_seq in *.
        destruct Hseq as [_ Hk_lt].
        split; [lia|].
        assert (k <= offset τ + k * task_period (tasks τ)).
        { destruct k; simpl; nia. }
        unfold expected_release in Hnew.
        lia.
      + apply jittered_index_may_be_in_window_b_spec.
        unfold jittered_index_may_be_in_window.
        split; [subst d; lia|].
        apply Nat.min_glb.
        * apply Nat.max_lub.
          -- pose proof (Nat.min_glb_l _ _ _ Hwin) as Hbound.
             subst d. lia.
          -- exact Hnew.
        * pose proof (Nat.min_glb_r _ _ _ Hwin) as Hlatest.
          exact Hlatest.
  }
  assert (Hnew_count : length new <= q).
  {
    assert (Hnew_incl : incl new (seq kbase q)).
    {
      intros k Hk.
      subst new extended rel.
      apply filter_In in Hk.
      destruct Hk as [Hk_ext Hnew].
      apply Nat.ltb_lt in Hnew.
      apply filter_In in Hk_ext.
      destruct Hk_ext as [_ Hwin].
      apply jittered_index_may_be_in_window_b_spec in Hwin.
      unfold jittered_index_may_be_in_window in Hwin.
      destruct Hwin as [_ Hwin].
      pose proof (Nat.min_glb_l _ _ _ Hwin) as Hrel_bound.
      unfold expected_release in *.
      rewrite in_seq.
      split.
      - eapply div_ceil_minus_one_le_factor.
        + exact Hp.
        + lia.
      - rewrite Hhp in Hrel_bound.
        destruct (le_gt_dec (kbase + q) k) as [Hge | Hlt].
        + assert (Hkbase_low :
            S (t2 - task_relative_deadline (tasks τ)) <=
            offset τ + kbase * p).
          {
            destruct (le_gt_dec
                        (S (t2 - task_relative_deadline (tasks τ)))
                        (offset τ)) as [Hbefore | Hafter].
            - subst p. lia.
            - subst kbase p.
              pose proof
                (div_ceil_minus_one_mul_ge
                   (S (t2 - task_relative_deadline (tasks τ)) - offset τ)
                   (task_period (tasks τ)) Hp) as Hceil.
              assert (Hsplit :
                S (t2 - task_relative_deadline (tasks τ)) =
                offset τ +
                (S (t2 - task_relative_deadline (tasks τ)) - offset τ))
                by lia.
              rewrite Hsplit.
              apply Nat.add_le_mono_l.
              exact Hceil.
          }
          assert ((kbase + q) * p <= k * p).
          { apply Nat.mul_le_mono_r. exact Hge. }
          lia.
        + lia.
    }
    eapply Nat.le_trans.
    - apply NoDup_incl_length with (l := new) (l' := seq kbase q).
      + subst new extended.
        apply NoDup_filter.
        apply NoDup_filter.
        apply seq_NoDup.
      + exact Hnew_incl.
    - rewrite length_seq.
      reflexivity.
  }
  unfold jittered_periodic_dbf_window.
  replace
    (length
       (filter
          (jittered_index_may_be_in_window_b tasks offset jitter τ t1 (t2 + hp))
          (seq 0 (S (t2 + hp)))))
    with (length extended) by reflexivity.
  replace
    (length
       (filter
          (jittered_index_may_be_in_window_b tasks offset jitter τ t1 t2)
          (seq 0 (S t2))))
    with (length old) by reflexivity.
  assert (Hlen_ext : length extended <= length (old ++ new)).
  {
    apply NoDup_incl_length.
    - unfold extended.
      apply NoDup_filter.
      apply seq_NoDup.
    - exact Hextended_incl.
  }
  rewrite length_app in Hlen_ext.
  subst p c.
  replace (hp / task_period (tasks τ)) with q by
    (rewrite Hhp; rewrite Nat.div_mul by lia; reflexivity).
  nia.
Qed.

Lemma taskset_jittered_periodic_dbf_window_add_hyperperiod_upper_after_deadline :
  forall tasks offset jitter enumT t1 t2 hp,
    t1 + periodic_max_relative_deadline tasks enumT <= t2 ->
    (forall τ, In τ enumT -> 0 < task_period (tasks τ)) ->
    (forall τ, In τ enumT -> Nat.divide (task_period (tasks τ)) hp) ->
    taskset_jittered_periodic_dbf_window tasks offset jitter enumT t1 (t2 + hp) <=
    taskset_jittered_periodic_dbf_window tasks offset jitter enumT t1 t2 +
      hyperperiod_load tasks enumT hp.
Proof.
  intros tasks offset jitter enumT t1 t2 hp Hcovered Hpos Hdiv.
  induction enumT as [|τ enumT IH]; simpl.
  - lia.
  - assert (Hhead_covered :
      t1 + task_relative_deadline (tasks τ) <= t2).
    {
      eapply Nat.le_trans.
      - apply Nat.add_le_mono_l.
        apply Nat.le_max_l.
      - exact Hcovered.
    }
    assert (Htail_covered :
      t1 + periodic_max_relative_deadline tasks enumT <= t2).
    {
      eapply Nat.le_trans.
      - apply Nat.add_le_mono_l.
        apply Nat.le_max_r.
      - exact Hcovered.
    }
    pose proof
      (jittered_periodic_dbf_window_add_hyperperiod_upper_after_deadline
         tasks offset jitter τ t1 t2 hp) as Hhead.
    specialize (Hhead Hhead_covered
      ltac:(apply Hpos; now left) ltac:(apply Hdiv; now left)).
    specialize (IH Htail_covered
      (fun τ' Hin => Hpos τ' (or_intror Hin))
      (fun τ' Hin => Hdiv τ' (or_intror Hin))).
    lia.
Qed.

Lemma jittered_offset_window_hyperperiod_load_le_hyperperiod :
  forall tasks offset jitter enumT,
    (forall τ, In τ enumT -> 0 < task_period (tasks τ)) ->
    jittered_offset_window_dbf_test_by_cutoff tasks offset jitter enumT = true ->
    hyperperiod_load tasks enumT (periodic_hyperperiod tasks enumT) <=
    periodic_hyperperiod tasks enumT.
Proof.
  intros tasks offset jitter enumT Hpos Htest.
  set (base_start := periodic_max_offset offset enumT).
  set (start :=
    periodic_max_offset offset enumT + jittered_max_release_jitter jitter enumT).
  set (m := periodic_max_relative_deadline tasks enumT).
  set (hp := periodic_hyperperiod tasks enumT).
  set (n := S (base_start + m + hp)).
  assert (Hbounded :
    taskset_jittered_periodic_dbf_window tasks offset jitter enumT start
      (start + m + n * hp) <= m + n * hp).
  {
    replace (m + n * hp) with ((start + m + n * hp) - start) by lia.
    eapply jittered_offset_window_dbf_test_by_cutoff_bounded_sound.
    - exact Htest.
    - lia.
    - unfold jittered_offset_window_dbf_cutoff_bound.
      subst start base_start m n hp.
      unfold offset_window_dbf_cutoff_bound.
      lia.
  }
  pose proof
    (taskset_periodic_dbf_window_hyperperiod_load_lower
       tasks offset enumT start m n hp) as Hlower.
  assert (Hoff_start : forall τ, In τ enumT -> offset τ <= start).
  {
    intros τ Hin.
    subst start.
    pose proof (periodic_max_offset_ge offset enumT τ Hin).
    lia.
  }
  specialize (Hlower
    Hoff_start
    (fun τ Hin => periodic_max_relative_deadline_ge tasks enumT τ Hin)
    Hpos
    (fun τ Hin => periodic_hyperperiod_divides tasks enumT τ Hin)
    ltac:(subst hp; apply periodic_hyperperiod_positive; exact Hpos)).
  pose proof
    (taskset_periodic_dbf_window_le_jittered_periodic_dbf_window
       tasks offset jitter enumT start (start + m + n * hp)) as Hperiodic_le.
  assert (Hn_big : m < n).
  { subst n base_start m. lia. }
  assert (Hchain :
    n * hyperperiod_load tasks enumT hp <= m + n * hp).
  {
    eapply Nat.le_trans.
    - exact Hlower.
    - eapply Nat.le_trans.
      + exact Hperiodic_le.
      + exact Hbounded.
  }
  subst hp.
  destruct (le_gt_dec
              (hyperperiod_load tasks enumT (periodic_hyperperiod tasks enumT))
              (periodic_hyperperiod tasks enumT)) as [Hle | Hgt].
  - exact Hle.
  - assert (periodic_hyperperiod tasks enumT <
            hyperperiod_load tasks enumT (periodic_hyperperiod tasks enumT))
      by exact Hgt.
    nia.
Qed.

Theorem jittered_offset_window_dbf_check_by_cutoff :
  forall tasks offset jitter enumT,
    (forall τ, In τ enumT -> 0 < task_period (tasks τ)) ->
    jittered_offset_window_dbf_test_by_cutoff tasks offset jitter enumT = true ->
    forall t1 t2,
      t1 <= t2 ->
      taskset_jittered_periodic_dbf_window
        tasks offset jitter enumT t1 t2 <= t2 - t1.
Proof.
  intros tasks offset jitter enumT Hpos Htest.
  set (hp := periodic_hyperperiod tasks enumT).
  set (cutoff := jittered_offset_window_dbf_cutoff_bound tasks offset jitter enumT).
  set (start :=
    periodic_max_offset offset enumT + jittered_max_release_jitter jitter enumT).
  set (m := periodic_max_relative_deadline tasks enumT).
  assert (Hhp_pos : 0 < hp).
  { subst hp. apply periodic_hyperperiod_positive. exact Hpos. }
  assert (Hload_le : hyperperiod_load tasks enumT hp <= hp).
  {
    subst hp.
    eapply jittered_offset_window_hyperperiod_load_le_hyperperiod; eauto.
  }
  assert (Hdiv : forall τ, In τ enumT -> Nat.divide (task_period (tasks τ)) hp).
  {
    intros τ Hin.
    subst hp.
    apply periodic_hyperperiod_divides.
    exact Hin.
  }
  intros t1 t2.
  revert t1.
  induction t2 as [t2 IH] using lt_wf_ind.
  intros t1 Hle12.
  destruct (le_gt_dec t2 cutoff) as [Ht2_cutoff | Ht2_after].
  - subst cutoff.
    eapply jittered_offset_window_dbf_test_by_cutoff_bounded_sound; eauto.
  - destruct (le_gt_dec (t1 + m) (t2 - hp)) as [Hlong | Hshort].
    + assert (Hprev_lt : t2 - hp < t2) by lia.
      assert (Hhp_le_t2 : hp <= t2).
      {
        unfold cutoff, jittered_offset_window_dbf_cutoff_bound,
               offset_window_dbf_cutoff_bound in Ht2_after.
        subst hp m.
        lia.
      }
      assert (Hprev_le : t1 <= t2 - hp) by lia.
      pose proof (IH (t2 - hp) Hprev_lt t1 Hprev_le) as Hprev.
      pose proof
        (taskset_jittered_periodic_dbf_window_add_hyperperiod_upper_after_deadline
           tasks offset jitter enumT t1 (t2 - hp) hp
           Hlong Hpos Hdiv) as Hstep.
      replace (t2 - hp + hp) with t2 in Hstep by lia.
      eapply Nat.le_trans.
      * exact Hstep.
      * lia.
    + assert (Hhp_le_t1 : hp <= t1).
      {
        unfold cutoff, jittered_offset_window_dbf_cutoff_bound,
               offset_window_dbf_cutoff_bound in Ht2_after.
        subst start m hp.
        lia.
      }
      assert (Hhp_le_t2 : hp <= t2) by lia.
      assert (Hprev_lt : t2 - hp < t2) by lia.
      assert (Hshift_start : start <= t1 - hp).
      {
        unfold cutoff, jittered_offset_window_dbf_cutoff_bound,
               offset_window_dbf_cutoff_bound in Ht2_after.
        subst start m hp.
        lia.
      }
      assert (Hprev_le : t1 - hp <= t2 - hp) by lia.
      pose proof (IH (t2 - hp) Hprev_lt (t1 - hp) Hprev_le) as Hprev.
      pose proof
        (taskset_jittered_periodic_dbf_window_shift_by_hyperperiod
           tasks offset jitter enumT (t1 - hp) (t2 - hp) 1
           Hpos Hshift_start Hprev_le) as Hshift.
      fold hp in Hshift.
      simpl in Hshift.
      replace (t1 - hp + (hp + 0)) with t1 in Hshift by lia.
      replace (t2 - hp + (hp + 0)) with t2 in Hshift by lia.
      rewrite Hshift.
      replace (t2 - t1) with ((t2 - hp) - (t1 - hp)) by lia.
      exact Hprev.
Qed.
