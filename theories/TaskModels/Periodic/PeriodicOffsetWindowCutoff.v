From Stdlib Require Import Arith Arith.PeanoNat Lia List Bool Sorting.Permutation.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import TaskModels.Periodic.PeriodicClassicDBF.
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
      periodic_max_relative_deadline tasks enumT +
      periodic_hyperperiod tasks enumT in
  horizon_base + S horizon_base * periodic_hyperperiod tasks enumT.

Definition offset_window_dbf_test_by_cutoff
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (enumT : list TaskId) : bool :=
  window_dbf_test_upto
    tasks offset enumT
    (offset_window_dbf_cutoff_bound tasks offset enumT).

Definition offset_window_dbf_test_by_cutoff_with_classical_guard
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (enumT : list TaskId) : bool :=
  offset_window_dbf_test_by_cutoff tasks offset enumT
  && dbf_test_by_cutoff tasks enumT.

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

Lemma periodic_dbf_window_hyperperiod_load_lower :
  forall tasks offset τ t1 m n hp q,
    offset τ <= t1 ->
    task_relative_deadline (tasks τ) <= m ->
    0 < task_period (tasks τ) ->
    0 < hp ->
    hp = q * task_period (tasks τ) ->
    n * ((hp / task_period (tasks τ)) *
         task_cost (tasks τ)) <=
    periodic_dbf_window tasks offset τ t1
      (t1 + m + n * hp).
Proof.
  intros tasks offset τ t1 m n hp q Hoff Hdl Hp Hhp_pos Hhp.
  set (p := task_period (tasks τ)).
  set (c := task_cost (tasks τ)).
  set (d := task_relative_deadline (tasks τ)).
  set (k0 := (t1 - offset τ + p - 1) / p).
  assert (Hq_pos : 0 < q).
  {
    rewrite Hhp in Hhp_pos.
    destruct q; simpl in *; lia.
  }
  assert (Hhp_eq : hp = q * p).
  { subst p. exact Hhp. }
  assert (Hceil_low : t1 <= offset τ + k0 * p).
  {
    subst k0 p.
    pose proof
      (div_ceil_minus_one_mul_ge
         (t1 - offset τ) (task_period (tasks τ)) Hp) as Hceil.
    lia.
  }
  assert (Hceil_high : offset τ + k0 * p <= t1 + p - 1).
  {
    subst k0 p.
    pose proof
      (Nat.div_mod
         (t1 - offset τ + task_period (tasks τ) - 1)
         (task_period (tasks τ)) ltac:(lia)) as Hdiv.
    pose proof
      (Nat.mod_upper_bound
         (t1 - offset τ + task_period (tasks τ) - 1)
         (task_period (tasks τ)) ltac:(lia)) as Hmod.
    lia.
  }
  unfold periodic_dbf_window.
  assert (Hincl :
    incl (seq k0 (n * q))
         (filter
            (periodic_index_in_window
               tasks offset τ t1 (t1 + m + n * hp))
            (seq 0 (S (t1 + m + n * hp))))).
  {
    intros k Hk.
    rewrite in_seq in Hk.
    destruct Hk as [Hk_ge Hk_lt].
    apply filter_In.
    split.
    - rewrite in_seq.
      split; [lia|].
      assert (Hkp :
        offset τ + k * p + d <= t1 + m + n * hp).
      {
        destruct n as [|n'].
        - simpl in Hk_lt. lia.
        - rewrite Hhp_eq.
          assert (k <= k0 + S n' * q - 1) by lia.
          assert (k * p <= (k0 + S n' * q - 1) * p).
          { apply Nat.mul_le_mono_r. exact H. }
          replace ((k0 + S n' * q - 1) * p)
            with (k0 * p + S n' * q * p - p) in H0 by nia.
          lia.
      }
      assert (k <= offset τ + k * p + d).
      { destruct k; simpl; nia. }
      lia.
    - unfold periodic_index_in_window.
      rewrite andb_true_iff.
      rewrite !Nat.leb_le.
      split.
      + unfold expected_release.
        assert (k0 * p <= k * p).
        { apply Nat.mul_le_mono_r. exact Hk_ge. }
        lia.
      + unfold expected_abs_deadline, expected_release.
        destruct n as [|n'].
        * simpl in Hk_lt. lia.
        * rewrite Hhp_eq.
          assert (k <= k0 + S n' * q - 1) by lia.
          assert (k * p <= (k0 + S n' * q - 1) * p).
          { apply Nat.mul_le_mono_r. exact H. }
          replace ((k0 + S n' * q - 1) * p)
            with (k0 * p + S n' * q * p - p) in H0 by nia.
          lia.
  }
  assert (Hcount :
    n * q <=
    length
      (filter
         (periodic_index_in_window
            tasks offset τ t1 (t1 + m + n * hp))
         (seq 0 (S (t1 + m + n * hp))))).
  {
    replace (n * q) with (length (seq k0 (n * q))) by
      (rewrite length_seq; lia).
    apply NoDup_incl_length with
      (l := seq k0 (n * q))
      (l' :=
        filter
          (periodic_index_in_window
             tasks offset τ t1 (t1 + m + n * hp))
          (seq 0 (S (t1 + m + n * hp)))).
    - apply seq_NoDup.
    - exact Hincl.
  }
  subst p c.
  replace (hp / task_period (tasks τ))
    with q by (rewrite Hhp; rewrite Nat.div_mul by lia; reflexivity).
  apply Nat.mul_le_mono_r with (p := task_cost (tasks τ)) in Hcount.
  replace (n * (q * task_cost (tasks τ)))
    with ((n * q) * task_cost (tasks τ)) by nia.
  exact Hcount.
Qed.

Lemma taskset_periodic_dbf_window_hyperperiod_load_lower :
  forall tasks offset enumT t1 m n hp,
    (forall τ, In τ enumT -> offset τ <= t1) ->
    (forall τ, In τ enumT -> task_relative_deadline (tasks τ) <= m) ->
    (forall τ, In τ enumT -> 0 < task_period (tasks τ)) ->
    (forall τ, In τ enumT ->
      exists q, hp = q * task_period (tasks τ)) ->
    0 < hp ->
    n * hyperperiod_load tasks enumT hp <=
    taskset_periodic_dbf_window tasks offset enumT t1
      (t1 + m + n * hp).
Proof.
  intros tasks offset enumT t1 m n hp Hoff Hdl Hpos Hdiv Hhp_pos.
  induction enumT as [|τ enumT IH]; simpl.
  - lia.
  - destruct (Hdiv τ ltac:(now left)) as [q Hhp].
    pose proof
      (periodic_dbf_window_hyperperiod_load_lower
         tasks offset τ t1 m n hp q
         ltac:(apply Hoff; now left)
         ltac:(apply Hdl; now left) ltac:(apply Hpos; now left)
         Hhp_pos
         Hhp) as Hhead.
    pose proof IH as Htail.
    specialize (Htail
      (fun τ' Hin => Hoff τ' (or_intror Hin))
      (fun τ' Hin => Hdl τ' (or_intror Hin))
      (fun τ' Hin => Hpos τ' (or_intror Hin))
      (fun τ' Hin => Hdiv τ' (or_intror Hin))).
    simpl in Htail.
    lia.
Qed.

Lemma offset_window_hyperperiod_load_le_hyperperiod :
  forall tasks offset enumT,
    (forall τ, In τ enumT -> 0 < task_period (tasks τ)) ->
    offset_window_dbf_test_by_cutoff tasks offset enumT = true ->
    hyperperiod_load tasks enumT (periodic_hyperperiod tasks enumT) <=
    periodic_hyperperiod tasks enumT.
Proof.
  intros tasks offset enumT Hpos Htest.
  set (start := periodic_max_offset offset enumT).
  set (m := periodic_max_relative_deadline tasks enumT).
  set (hp := periodic_hyperperiod tasks enumT).
  set (n := S (start + m + hp)).
  assert (Hbounded :
    taskset_periodic_dbf_window tasks offset enumT start
      (start + m + n * hp) <= m + n * hp).
  {
    unfold offset_window_dbf_test_by_cutoff in Htest.
    replace (m + n * hp) with ((start + m + n * hp) - start) by lia.
    eapply window_dbf_test_upto_true_implies_bounded_window_dbf.
    - exact Htest.
    - lia.
    - unfold offset_window_dbf_cutoff_bound.
      subst start m n hp.
      unfold offset_window_dbf_cutoff_bound.
      lia.
  }
  pose proof
    (taskset_periodic_dbf_window_hyperperiod_load_lower
       tasks offset enumT start m n hp) as Hlower.
  specialize (Hlower
    (fun τ Hin => periodic_max_offset_ge offset enumT τ Hin)
    (fun τ Hin => periodic_max_relative_deadline_ge tasks enumT τ Hin)
    Hpos
    (fun τ Hin => periodic_hyperperiod_divides tasks enumT τ Hin)
    ltac:(subst hp; apply periodic_hyperperiod_positive; exact Hpos)).
  assert (Hn_big : m < n).
  { subst n start m. lia. }
  assert (Hchain :
    n * hyperperiod_load tasks enumT hp <= m + n * hp).
  {
    eapply Nat.le_trans.
    - exact Hlower.
    - exact Hbounded.
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

Lemma periodic_dbf_window_add_hyperperiod_upper :
  forall tasks offset τ t1 t2 hp,
    0 < task_period (tasks τ) ->
    Nat.divide (task_period (tasks τ)) hp ->
    periodic_dbf_window tasks offset τ t1 (t2 + hp) <=
    periodic_dbf_window tasks offset τ t1 t2 +
      (hp / task_period (tasks τ)) * task_cost (tasks τ).
Proof.
  intros tasks offset τ t1 t2 hp Hp Hdiv.
  destruct Hdiv as [q Hhp0].
  assert (Hhp : hp = q * task_period (tasks τ)) by lia.
  set (p := task_period (tasks τ)).
  set (c := task_cost (tasks τ)).
  set (d := task_relative_deadline (tasks τ)).
  set (dl := fun k => expected_abs_deadline tasks offset τ k).
  set (old :=
    filter
      (periodic_index_in_window tasks offset τ t1 t2)
      (seq 0 (S t2))).
  set (extended :=
    filter
      (periodic_index_in_window tasks offset τ t1 (t2 + hp))
      (seq 0 (S (t2 + hp)))).
  set (new :=
    filter (fun k => t2 <? dl k) extended).
  set (kbase := (S t2 - offset τ - d + p - 1) / p).
  assert (Hextended_incl : incl extended (old ++ new)).
  {
    intros k Hk.
    subst old new extended dl.
    apply filter_In in Hk.
    destruct Hk as [Hseq Hwin].
    unfold periodic_index_in_window in Hwin.
    rewrite andb_true_iff in Hwin.
    rewrite !Nat.leb_le in Hwin.
    destruct Hwin as [Hrel Hdl].
    apply in_app_iff.
    destruct (t2 <? expected_abs_deadline tasks offset τ k) eqn:Hnew.
    - right.
      apply filter_In.
      split.
      + apply filter_In.
        split; [exact Hseq|].
        unfold periodic_index_in_window.
        rewrite andb_true_iff.
        rewrite !Nat.leb_le.
        split; assumption.
      + exact Hnew.
    - left.
      apply Nat.ltb_ge in Hnew.
      apply filter_In.
      split.
      + rewrite in_seq in *.
        destruct Hseq as [_ Hk_lt].
        split; [lia|].
        unfold expected_abs_deadline, expected_release in Hnew.
        assert (k <= offset τ + k * task_period (tasks τ) +
                    task_relative_deadline (tasks τ)).
        { destruct k; simpl; nia. }
        lia.
      + unfold periodic_index_in_window.
        rewrite andb_true_iff.
        rewrite !Nat.leb_le.
        split; assumption.
  }
  assert (Hnew_count : length new <= q).
  {
    assert (Hnew_incl : incl new (seq kbase q)).
    {
      intros k Hk.
      subst new extended dl.
      apply filter_In in Hk.
      destruct Hk as [Hk_ext Hnew].
      apply Nat.ltb_lt in Hnew.
      apply filter_In in Hk_ext.
      destruct Hk_ext as [_ Hwin].
      unfold periodic_index_in_window in Hwin.
      rewrite andb_true_iff in Hwin.
      rewrite !Nat.leb_le in Hwin.
      destruct Hwin as [_ Hdl].
      unfold expected_abs_deadline, expected_release in *.
      rewrite in_seq.
      split.
      - eapply div_ceil_minus_one_le_factor.
        + exact Hp.
        + lia.
      - assert (Hkbase_low :
          S t2 <=
          offset τ + kbase * p + d).
        {
          subst kbase p d.
          pose proof
            (div_ceil_minus_one_mul_ge
               (S t2 - offset τ - task_relative_deadline (tasks τ))
               (task_period (tasks τ)) Hp) as Hceil.
          lia.
        }
        rewrite Hhp in Hdl.
        destruct (le_gt_dec (kbase + q) k) as [Hge | Hlt].
        + assert ((kbase + q) * p <= k * p).
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
  unfold periodic_dbf_window.
  replace
    (length
       (filter
          (periodic_index_in_window tasks offset τ t1 (t2 + hp))
          (seq 0 (S (t2 + hp)))))
    with (length extended) by reflexivity.
  replace
    (length
       (filter
          (periodic_index_in_window tasks offset τ t1 t2)
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

Lemma taskset_periodic_dbf_window_add_hyperperiod_upper :
  forall tasks offset enumT t1 t2 hp,
    (forall τ, In τ enumT -> 0 < task_period (tasks τ)) ->
    (forall τ, In τ enumT -> Nat.divide (task_period (tasks τ)) hp) ->
    taskset_periodic_dbf_window tasks offset enumT t1 (t2 + hp) <=
    taskset_periodic_dbf_window tasks offset enumT t1 t2 +
      hyperperiod_load tasks enumT hp.
Proof.
  intros tasks offset enumT t1 t2 hp Hpos Hdiv.
  induction enumT as [|τ enumT IH]; simpl.
  - lia.
  - pose proof
      (periodic_dbf_window_add_hyperperiod_upper
         tasks offset τ t1 t2 hp
         ltac:(apply Hpos; now left)
         ltac:(apply Hdiv; now left)) as Hhead.
    specialize (IH
      (fun τ' Hin => Hpos τ' (or_intror Hin))
      (fun τ' Hin => Hdiv τ' (or_intror Hin))).
    lia.
Qed.

Lemma taskset_periodic_dbf_window_add_hyperperiod_upper_n :
  forall tasks offset enumT t1 t2 hp q,
    (forall τ, In τ enumT -> 0 < task_period (tasks τ)) ->
    (forall τ, In τ enumT -> Nat.divide (task_period (tasks τ)) hp) ->
    taskset_periodic_dbf_window tasks offset enumT t1 (t2 + q * hp) <=
    taskset_periodic_dbf_window tasks offset enumT t1 t2 +
      q * hyperperiod_load tasks enumT hp.
Proof.
  intros tasks offset enumT t1 t2 hp q Hpos Hdiv.
  induction q as [|q IH].
  - replace (t2 + 0 * hp) with t2 by lia.
    lia.
  - replace (t2 + S q * hp) with ((t2 + q * hp) + hp) by lia.
    pose proof
      (taskset_periodic_dbf_window_add_hyperperiod_upper
         tasks offset enumT t1 (t2 + q * hp) hp Hpos Hdiv) as Hstep.
    lia.
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

Theorem offset_window_dbf_check_by_cutoff :
  forall tasks offset enumT,
    (forall τ, In τ enumT -> 0 < task_period (tasks τ)) ->
    offset_window_dbf_test_by_cutoff tasks offset enumT = true ->
    forall t1 t2,
      t1 <= t2 ->
      taskset_periodic_dbf_window tasks offset enumT t1 t2 <= t2 - t1.
Proof.
  intros tasks offset enumT Hpos Htest.
  set (hp := periodic_hyperperiod tasks enumT).
  set (cutoff := offset_window_dbf_cutoff_bound tasks offset enumT).
  assert (Hhp_pos : 0 < hp).
  { subst hp. apply periodic_hyperperiod_positive. exact Hpos. }
  assert (Hload_le : hyperperiod_load tasks enumT hp <= hp).
  {
    subst hp.
    eapply offset_window_hyperperiod_load_le_hyperperiod; eauto.
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
    unfold offset_window_dbf_test_by_cutoff in Htest.
    eapply window_dbf_test_upto_true_implies_bounded_window_dbf; eauto.
  - destruct (le_gt_dec t1 (t2 - hp)) as [Hlong | Hshort].
    + assert (Hprev_lt : t2 - hp < t2) by lia.
      assert (Hhp_le_t2 : hp <= t2).
      {
        unfold cutoff, offset_window_dbf_cutoff_bound in Ht2_after.
        subst hp.
        lia.
      }
      pose proof (IH (t2 - hp) Hprev_lt t1 Hlong) as Hprev.
      pose proof
        (taskset_periodic_dbf_window_add_hyperperiod_upper
           tasks offset enumT t1 (t2 - hp) hp Hpos Hdiv) as Hstep.
      replace (t2 - hp + hp) with t2 in Hstep by lia.
      eapply Nat.le_trans.
      * exact Hstep.
      * lia.
    + assert (Htwo_hp_le_t2 : 2 * hp <= t2).
      {
        unfold cutoff, offset_window_dbf_cutoff_bound in Ht2_after.
        subst hp.
        lia.
      }
      assert (Hhp_le_t1 : hp <= t1) by lia.
      assert (Hhp_le_t2 : hp <= t2) by lia.
      assert (Hprev_lt : t2 - hp < t2) by lia.
      assert (Hshift_start :
        periodic_max_offset offset enumT <= t1 - hp).
      {
        unfold cutoff, offset_window_dbf_cutoff_bound in Ht2_after.
        subst hp.
        lia.
      }
      assert (Hprev_le : t1 - hp <= t2 - hp) by lia.
      pose proof (IH (t2 - hp) Hprev_lt (t1 - hp) Hprev_le) as Hprev.
      pose proof
        (taskset_periodic_dbf_window_shift_by_hyperperiod
           tasks offset enumT (t1 - hp) (t2 - hp) 1
           Hpos Hshift_start Hprev_le) as Hshift.
      fold hp in Hshift.
      simpl in Hshift.
      replace (t1 - hp + (hp + 0)) with t1 in Hshift by lia.
      replace (t2 - hp + (hp + 0)) with t2 in Hshift by lia.
      rewrite Hshift.
      replace (t2 - t1) with ((t2 - hp) - (t1 - hp)) by lia.
      exact Hprev.
Qed.

Theorem offset_window_dbf_check_by_cutoff_with_classical_guard :
  forall tasks offset enumT,
    NoDup enumT ->
    (forall τ, In τ enumT -> 0 < task_period (tasks τ)) ->
    offset_window_dbf_test_by_cutoff_with_classical_guard tasks offset enumT =
      true ->
    forall t1 t2,
      t1 <= t2 ->
      taskset_periodic_dbf_window tasks offset enumT t1 t2 <= t2 - t1.
Proof.
  intros tasks offset enumT Hnodup Hpos Htest t1 t2 _Hle12.
  unfold offset_window_dbf_test_by_cutoff_with_classical_guard in Htest.
  apply andb_true_iff in Htest.
  destruct Htest as [_Hoffset Hclassical].
  eapply Nat.le_trans.
  - eapply taskset_periodic_dbf_window_le_classical_dbf.
    exact Hpos.
  - eapply dbf_check_by_cutoff; eauto.
Qed.
