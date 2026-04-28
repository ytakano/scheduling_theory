From Stdlib Require Import Arith Arith.PeanoNat Lia List Bool.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Periodic.PeriodicClassicDBF.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicWindowDemandBound.

Import ListNotations.

(** * Arithmetic DBF counts for jittered-periodic windows

    The semantic DBF in [JitteredPeriodicWindowDemandBound] enumerates all
    indices up to the right endpoint.  This file keeps that definition as the
    proof-facing meaning, and adds a closed arithmetic counter suitable for
    extracted checkers. *)

Definition nat_interval_count (lo hi : nat) : nat :=
  if lo <=? hi then S (hi - lo) else 0.

Definition ceil_div_pos (n p : nat) : nat :=
  (n + p - 1) / p.

Definition ap_first_index_at_or_after
    (start period lo : nat) : nat :=
  if lo <=? start then 0 else ceil_div_pos (lo - start) period.

Definition ap_index_count
    (start period lo hi limit : nat) : nat :=
  if period =? 0 then
    if (lo <=? start) && (start <=? hi) then S limit else 0
  else if start <=? hi then
    let first := ap_first_index_at_or_after start period lo in
    let last := Nat.min limit ((hi - start) / period) in
    nat_interval_count first last
  else 0.

Definition ap_index_count_witnesses
    (start period lo hi limit : nat) : list nat :=
  if period =? 0 then
    if (lo <=? start) && (start <=? hi) then seq 0 (S limit) else []
  else if start <=? hi then
    let first := ap_first_index_at_or_after start period lo in
    let last := Nat.min limit ((hi - start) / period) in
    seq first (nat_interval_count first last)
  else [].

Definition ap_release_in_window_b
    (start period lo hi k : nat) : bool :=
  (lo <=? start + k * period) && (start + k * period <=? hi).

Lemma nat_interval_count_length :
  forall lo hi,
    length (seq lo (nat_interval_count lo hi)) =
    nat_interval_count lo hi.
Proof.
  intros lo hi.
  unfold nat_interval_count.
  destruct (lo <=? hi); apply length_seq.
Qed.

Lemma ap_index_count_witnesses_length :
  forall start period lo hi limit,
    length (ap_index_count_witnesses start period lo hi limit) =
    ap_index_count start period lo hi limit.
Proof.
  intros start period lo hi limit.
  unfold ap_index_count_witnesses, ap_index_count.
  destruct (period =? 0).
  - destruct ((lo <=? start) && (start <=? hi)).
    + rewrite length_seq.
      reflexivity.
    + reflexivity.
  - destruct (start <=? hi).
    + apply nat_interval_count_length.
    + reflexivity.
Qed.

Lemma ap_release_in_window_b_spec :
  forall start period lo hi k,
    ap_release_in_window_b start period lo hi k = true <->
    lo <= start + k * period <= hi.
Proof.
  intros start period lo hi k.
  unfold ap_release_in_window_b.
  rewrite andb_true_iff, !Nat.leb_le.
  tauto.
Qed.

Lemma ap_index_count_witnesses_incl_filter :
  forall start period lo hi limit,
    incl
      (ap_index_count_witnesses start period lo hi limit)
      (filter
         (ap_release_in_window_b start period lo hi)
         (seq 0 (S limit))).
Proof.
  intros start period lo hi limit k Hin.
  unfold ap_index_count_witnesses in Hin.
  destruct (period =? 0) eqn:Hperiod0.
  - apply Nat.eqb_eq in Hperiod0.
    subst period.
    destruct ((lo <=? start) && (start <=? hi)) eqn:Hbounds;
      [|contradiction].
    apply filter_In.
    split.
    + exact Hin.
    + apply andb_true_iff in Hbounds as [Hlo Hhi].
      apply Nat.leb_le in Hlo.
      apply Nat.leb_le in Hhi.
      apply ap_release_in_window_b_spec.
      lia.
  - apply Nat.eqb_neq in Hperiod0.
    destruct (start <=? hi) eqn:Hstart_hi; [|contradiction].
    apply Nat.leb_le in Hstart_hi.
    set (first := ap_first_index_at_or_after start period lo) in *.
    set (last := Nat.min limit ((hi - start) / period)) in *.
    unfold nat_interval_count in Hin.
    destruct (first <=? last) eqn:Hfirst_last; [|contradiction].
    apply Nat.leb_le in Hfirst_last.
    rewrite in_seq in Hin.
    destruct Hin as [Hfirst_le_k Hk_lt].
    apply filter_In.
    split.
    + rewrite in_seq.
      split.
      * lia.
      * subst last.
        pose proof (Nat.le_min_l limit ((hi - start) / period)) as Hlast_limit.
        lia.
    + apply ap_release_in_window_b_spec.
      split.
      * subst first.
        unfold ap_first_index_at_or_after.
        destruct (lo <=? start) eqn:Hlo_start.
        -- apply Nat.leb_le in Hlo_start.
           lia.
        -- assert (Hfirst_eq :
             ap_first_index_at_or_after start period lo =
             ceil_div_pos (lo - start) period).
           {
             unfold ap_first_index_at_or_after.
             rewrite Hlo_start.
             reflexivity.
           }
           apply Nat.leb_gt in Hlo_start.
           pose proof
             (div_ceil_minus_one_mul_ge (lo - start) period ltac:(lia))
             as Hceil.
           assert (ceil_div_pos (lo - start) period <= k).
           {
             rewrite <- Hfirst_eq.
             exact Hfirst_le_k.
           }
           unfold ceil_div_pos in H.
           assert ((lo - start) <= k * period).
           {
             eapply Nat.le_trans; [exact Hceil|].
             apply Nat.mul_le_mono_r.
             exact H.
           }
           lia.
      * subst last.
        assert (k <= (hi - start) / period) by lia.
        assert (k * period <= ((hi - start) / period) * period).
        { apply Nat.mul_le_mono_r. exact H. }
        pose proof (Nat.div_mod (hi - start) period Hperiod0) as Hdiv.
        pose proof (Nat.mod_upper_bound (hi - start) period Hperiod0) as Hmod.
        lia.
Qed.

Lemma ap_index_filter_incl_witnesses :
  forall start period lo hi limit,
    incl
      (filter
         (ap_release_in_window_b start period lo hi)
         (seq 0 (S limit)))
      (ap_index_count_witnesses start period lo hi limit).
Proof.
  intros start period lo hi limit k Hin.
  apply filter_In in Hin.
  destruct Hin as [Hk Hwin].
  apply ap_release_in_window_b_spec in Hwin.
  destruct Hwin as [Hlo Hhi].
  rewrite in_seq in Hk.
  destruct Hk as [_ Hk_limit].
  unfold ap_index_count_witnesses.
  destruct (period =? 0) eqn:Hperiod0.
  - apply Nat.eqb_eq in Hperiod0.
    subst period.
    assert (((lo <=? start) && (start <=? hi)) = true).
    {
      apply andb_true_iff.
      split; apply Nat.leb_le; lia.
    }
    rewrite H.
    rewrite in_seq.
    lia.
  - apply Nat.eqb_neq in Hperiod0.
    assert ((start <=? hi) = true).
    {
      apply Nat.leb_le.
      lia.
    }
    rewrite H.
    set (first := ap_first_index_at_or_after start period lo).
    set (last := Nat.min limit ((hi - start) / period)).
    unfold nat_interval_count.
    assert (Hfirst_le_k : first <= k).
    {
      subst first.
      unfold ap_first_index_at_or_after.
      destruct (lo <=? start) eqn:Hlo_start.
      - lia.
      - apply Nat.leb_gt in Hlo_start.
        unfold ceil_div_pos.
        eapply div_ceil_minus_one_le_factor.
        + lia.
        + lia.
    }
    assert (Hk_le_last : k <= last).
    {
      subst last.
      apply Nat.min_glb.
      - lia.
      - apply Nat.div_le_lower_bound; [lia|].
        lia.
    }
    assert ((first <=? last) = true).
    {
      apply Nat.leb_le.
      lia.
    }
    rewrite H0.
    rewrite in_seq.
    lia.
Qed.

Theorem ap_index_count_eq_filter_length :
  forall start period lo hi limit,
    ap_index_count start period lo hi limit =
    length
      (filter
         (ap_release_in_window_b start period lo hi)
         (seq 0 (S limit))).
Proof.
  intros start period lo hi limit.
  pose proof
    (ap_index_count_witnesses_length start period lo hi limit) as Hlen.
  apply Nat.le_antisymm.
  - rewrite <- Hlen.
    eapply NoDup_incl_length.
    + unfold ap_index_count_witnesses.
      destruct (period =? 0).
      * destruct ((lo <=? start) && (start <=? hi));
          [apply seq_NoDup|constructor].
      * destruct (start <=? hi); [apply seq_NoDup|constructor].
    + apply ap_index_count_witnesses_incl_filter.
  - rewrite <- Hlen.
    eapply NoDup_incl_length.
    + apply NoDup_filter.
      apply seq_NoDup.
    + apply ap_index_filter_incl_witnesses.
Qed.

Definition jittered_periodic_fast_release_count
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jitter : TaskId -> Time)
    (τ : TaskId)
    (t1 t2 : Time) : nat :=
  let d := task_relative_deadline (tasks τ) in
  if (d <=? t2) && (t1 <=? t2 - d) then
    ap_index_count
      (offset τ)
      (task_period (tasks τ))
      (t1 - jitter τ)
      (t2 - d)
      t2
  else 0.

Definition jittered_periodic_fast_dbf_window
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jitter : TaskId -> Time)
    (τ : TaskId)
    (t1 t2 : Time) : nat :=
  jittered_periodic_fast_release_count tasks offset jitter τ t1 t2 *
  task_cost (tasks τ).

Fixpoint taskset_jittered_periodic_fast_dbf_window
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jitter : TaskId -> Time)
    (enumT : list TaskId)
    (t1 t2 : Time) : nat :=
  match enumT with
  | [] => 0
  | τ :: enumT' =>
      jittered_periodic_fast_dbf_window tasks offset jitter τ t1 t2 +
      taskset_jittered_periodic_fast_dbf_window tasks offset jitter enumT' t1 t2
  end.

Lemma jittered_index_may_be_in_window_b_fast_iff :
  forall tasks offset jitter τ t1 t2 k,
    task_relative_deadline (tasks τ) <= t2 ->
    t1 <= t2 - task_relative_deadline (tasks τ) ->
    jittered_index_may_be_in_window_b tasks offset jitter τ t1 t2 k = true <->
    ap_release_in_window_b
      (offset τ)
      (task_period (tasks τ))
      (t1 - jitter τ)
      (t2 - task_relative_deadline (tasks τ))
      k = true.
Proof.
  intros tasks offset jitter τ t1 t2 k Hdeadline Hwindow.
  unfold jittered_index_may_be_in_window_b,
         ap_release_in_window_b,
         expected_release.
  rewrite !andb_true_iff, !Nat.leb_le.
  split.
  - intros [_ Hwin].
    split; lia.
  - intros [Hlo Hhi].
    split; [lia|].
    apply Nat.max_lub; apply Nat.min_glb; lia.
Qed.

Lemma jittered_index_may_be_in_window_b_false_after_deadline :
  forall tasks offset jitter τ t1 t2 k,
    t2 < task_relative_deadline (tasks τ) ->
    jittered_index_may_be_in_window_b tasks offset jitter τ t1 t2 k = false.
Proof.
  intros tasks offset jitter τ t1 t2 k Hlt.
  unfold jittered_index_may_be_in_window_b.
  apply Bool.andb_false_intro1.
  apply Nat.leb_gt.
  exact Hlt.
Qed.

Lemma jittered_index_may_be_in_window_b_false_empty_window :
  forall tasks offset jitter τ t1 t2 k,
    task_relative_deadline (tasks τ) <= t2 ->
    t2 - task_relative_deadline (tasks τ) < t1 ->
    jittered_index_may_be_in_window_b tasks offset jitter τ t1 t2 k = false.
Proof.
  intros tasks offset jitter τ t1 t2 k Hdeadline Hempty.
  unfold jittered_index_may_be_in_window_b.
  apply Bool.andb_false_intro2.
  apply Nat.leb_gt.
  enough (Nat.min
            (t2 - task_relative_deadline (tasks τ))
            (expected_release tasks offset τ k + jitter τ) <
          Nat.max t1 (expected_release tasks offset τ k)) by exact H.
  pose proof
    (Nat.le_min_l
       (t2 - task_relative_deadline (tasks τ))
       (expected_release tasks offset τ k + jitter τ)) as Hmin.
  pose proof
    (Nat.le_max_l t1 (expected_release tasks offset τ k)) as Hmax.
  lia.
Qed.

Theorem jittered_periodic_fast_release_count_eq_enumerated :
  forall tasks offset jitter τ t1 t2,
    jittered_periodic_fast_release_count tasks offset jitter τ t1 t2 =
    length
      (filter
         (jittered_index_may_be_in_window_b tasks offset jitter τ t1 t2)
         (seq 0 (S t2))).
Proof.
  intros tasks offset jitter τ t1 t2.
  unfold jittered_periodic_fast_release_count.
  destruct ((task_relative_deadline (tasks τ) <=? t2) &&
            (t1 <=? t2 - task_relative_deadline (tasks τ))) eqn:Hwindow.
  - apply andb_true_iff in Hwindow as [Hdeadline Hnonempty].
    apply Nat.leb_le in Hdeadline.
    apply Nat.leb_le in Hnonempty.
    rewrite ap_index_count_eq_filter_length.
    apply f_equal.
    apply filter_ext.
    intro k.
    apply Bool.eq_iff_eq_true.
    apply iff_sym.
    apply jittered_index_may_be_in_window_b_fast_iff.
    + exact Hdeadline.
    + exact Hnonempty.
  - apply andb_false_iff in Hwindow as [Hdeadline | Hempty].
    all: replace
      (filter
         (jittered_index_may_be_in_window_b tasks offset jitter τ t1 t2)
         (seq 0 (S t2)))
      with (filter (fun _ : nat => false) (seq 0 (S t2)));
      [rewrite filter_false; reflexivity|].
    + apply filter_ext.
      intros k.
      apply Nat.leb_gt in Hdeadline.
      symmetry.
      apply jittered_index_may_be_in_window_b_false_after_deadline.
      exact Hdeadline.
    + apply Nat.leb_gt in Hempty.
      apply filter_ext.
      intros k.
      destruct (task_relative_deadline (tasks τ) <=? t2) eqn:Hdeadline.
      * apply Nat.leb_le in Hdeadline.
        symmetry.
        apply jittered_index_may_be_in_window_b_false_empty_window; assumption.
      * apply Nat.leb_gt in Hdeadline.
        symmetry.
        apply jittered_index_may_be_in_window_b_false_after_deadline.
        exact Hdeadline.
Qed.

Theorem jittered_periodic_fast_dbf_window_eq_enumerated :
  forall tasks offset jitter τ t1 t2,
    jittered_periodic_fast_dbf_window tasks offset jitter τ t1 t2 =
    jittered_periodic_dbf_window tasks offset jitter τ t1 t2.
Proof.
  intros tasks offset jitter τ t1 t2.
  unfold jittered_periodic_fast_dbf_window,
         jittered_periodic_dbf_window.
  rewrite jittered_periodic_fast_release_count_eq_enumerated.
  reflexivity.
Qed.

Theorem taskset_jittered_periodic_fast_dbf_window_eq_enumerated :
  forall tasks offset jitter enumT t1 t2,
    taskset_jittered_periodic_fast_dbf_window tasks offset jitter enumT t1 t2 =
    taskset_jittered_periodic_dbf_window tasks offset jitter enumT t1 t2.
Proof.
  intros tasks offset jitter enumT.
  induction enumT as [|τ enumT IH]; intros t1 t2; simpl.
  - reflexivity.
  - rewrite jittered_periodic_fast_dbf_window_eq_enumerated.
    rewrite IH.
    reflexivity.
Qed.
