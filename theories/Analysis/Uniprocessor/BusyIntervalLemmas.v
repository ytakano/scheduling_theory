From Stdlib Require Import Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Semantics.ScheduleLemmas.ScheduleFacts.
From RocqSched Require Import Analysis.Uniprocessor.BusyInterval.

Lemma cpu_busy_at_iff_scheduled :
  forall sched t,
    cpu_busy_at sched t <-> exists j, sched t 0 = Some j.
Proof.
  intros sched t.
  unfold cpu_busy_at.
  tauto.
Qed.

Lemma cpu_busy_at_implies_running :
  forall sched t,
    cpu_busy_at sched t ->
    exists j, running 1 sched j t.
Proof.
  intros sched t [j Hrun].
  exists j.
  unfold running.
  exists 0.
  split; [lia | exact Hrun].
Qed.

Lemma running_implies_cpu_busy_at :
  forall sched j t,
    running 1 sched j t ->
    cpu_busy_at sched t.
Proof.
  intros sched j t [c [Hlt Hrun]].
  assert (c = 0) by lia.
  subst c.
  exists j.
  exact Hrun.
Qed.

Lemma cpu_busy_at_has_cpu_count :
  forall sched t,
    cpu_busy_at sched t ->
    exists j, cpu_count 1 sched j t = 1.
Proof.
  intros sched t [j Hrun].
  exists j.
  unfold cpu_count, runs_on.
  rewrite Hrun.
  simpl.
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

Lemma cpu_not_busy_at_cpu_service_zero :
  forall sched t,
    ~ cpu_busy_at sched t ->
    cpu_service_at sched t = 0.
Proof.
  intros sched t Hidle.
  unfold cpu_service_at, cpu_busy_at.
  destruct (sched t 0) as [j|] eqn:Hsched.
  - exfalso.
    apply Hidle.
    exists j.
    exact Hsched.
  - reflexivity.
Qed.

Lemma cpu_busy_at_cpu_service_one :
  forall sched t,
    cpu_busy_at sched t ->
    cpu_service_at sched t = 1.
Proof.
  intros sched t [j Hrun].
  unfold cpu_service_at.
  rewrite Hrun.
  reflexivity.
Qed.

Lemma cumulative_cpu_service_step :
  forall sched t,
    cumulative_cpu_service sched (S t) =
    cumulative_cpu_service sched t + cpu_service_at sched t.
Proof.
  intros sched t.
  simpl.
  lia.
Qed.

Lemma cumulative_cpu_service_monotone :
  forall sched t1 t2,
    t1 <= t2 ->
    cumulative_cpu_service sched t1 <= cumulative_cpu_service sched t2.
Proof.
  intros sched t1 t2 Hle.
  induction t2 as [| t2' IH].
  - assert (t1 = 0) by lia.
    subst t1.
    lia.
  - apply Nat.le_succ_r in Hle.
    destruct Hle as [Hlt | ->].
    + eapply Nat.le_trans; [apply IH; exact Hlt |].
      rewrite cumulative_cpu_service_step.
      lia.
    + lia.
Qed.

Lemma cpu_service_between_eq :
  forall sched t1 t2,
    t1 <= t2 ->
    cpu_service_between sched t1 t2 =
    cumulative_cpu_service sched t2 - cumulative_cpu_service sched t1.
Proof.
  intros sched t1 t2 _.
  unfold cpu_service_between.
  reflexivity.
Qed.

Lemma cpu_service_between_refl :
  forall sched t,
    cpu_service_between sched t t = 0.
Proof.
  intros sched t.
  unfold cpu_service_between.
  lia.
Qed.

Lemma cpu_service_between_split :
  forall sched t1 t2 t3,
    t1 <= t2 ->
    t2 <= t3 ->
    cpu_service_between sched t1 t3 =
    cpu_service_between sched t1 t2 +
    cpu_service_between sched t2 t3.
Proof.
  intros sched t1 t2 t3 H12 H23.
  unfold cpu_service_between.
  pose proof (cumulative_cpu_service_monotone sched t1 t2 H12) as Hle12.
  pose proof (cumulative_cpu_service_monotone sched t2 t3 H23) as Hle23.
  lia.
Qed.

Lemma cpu_service_between_0_r :
  forall sched t,
    cpu_service_between sched 0 t = cumulative_cpu_service sched t.
Proof.
  intros sched t.
  unfold cpu_service_between.
  simpl.
  lia.
Qed.

Lemma cpu_service_between_nonneg :
  forall sched t1 t2,
    t1 <= t2 ->
    cumulative_cpu_service sched t1 <= cumulative_cpu_service sched t2.
Proof.
  intros sched t1 t2 Hle.
  exact (cumulative_cpu_service_monotone sched t1 t2 Hle).
Qed.

Lemma busy_interval_implies_busy_at :
  forall sched t1 t2 t,
    busy_interval sched t1 t2 ->
    t1 <= t < t2 ->
    cpu_busy_at sched t.
Proof.
  intros sched t1 t2 t [_ Hbusy] Ht.
  exact (Hbusy t Ht).
Qed.

Lemma busy_interval_has_no_idle_slot :
  forall sched t1 t2 t,
    busy_interval sched t1 t2 ->
    t1 <= t < t2 ->
    exists j, sched t 0 = Some j.
Proof.
  intros sched t1 t2 t Hbusy Ht.
  apply busy_interval_implies_busy_at with (t1 := t1) (t2 := t2); assumption.
Qed.

Lemma busy_interval_prefix :
  forall sched t1 t2 t2',
    busy_interval sched t1 t2 ->
    t1 < t2' ->
    t2' <= t2 ->
    busy_interval sched t1 t2'.
Proof.
  intros sched t1 t2 t2' [Hlt Hbusy] Hlt' Hle'.
  split.
  - exact Hlt'.
  - intros t Ht.
    apply Hbusy.
    lia.
Qed.

Lemma busy_interval_suffix :
  forall sched t1 t2 t1',
    busy_interval sched t1 t2 ->
    t1 <= t1' ->
    t1' < t2 ->
    busy_interval sched t1' t2.
Proof.
  intros sched t1 t2 t1' [Hlt Hbusy] Hle' Hlt'.
  split.
  - exact Hlt'.
  - intros t Ht.
    apply Hbusy.
    lia.
Qed.

Lemma idle_slot_not_interval_busy :
  forall sched t1 t2 t,
    t1 <= t < t2 ->
    ~ cpu_busy_at sched t ->
    ~ interval_busy sched t1 t2.
Proof.
  intros sched t1 t2 t Ht Hidle Hbusy.
  apply Hidle.
  exact (Hbusy t Ht).
Qed.

Lemma idle_slot_not_busy_interval :
  forall sched t1 t2 t,
    t1 <= t < t2 ->
    ~ cpu_busy_at sched t ->
    ~ busy_interval sched t1 t2.
Proof.
  intros sched t1 t2 t Ht Hidle [_ Hbusy].
  apply Hidle.
  exact (Hbusy t Ht).
Qed.

Lemma maximal_busy_interval_from_decompose :
  forall sched t1 t2,
    maximal_busy_interval_from sched t1 t2 ->
    busy_interval sched t1 t2 /\
    (t1 = 0 \/ ~ cpu_busy_at sched (pred t1)) /\
    ~ cpu_busy_at sched t2.
Proof.
  intros sched t1 t2 Hmax.
  exact Hmax.
Qed.

Lemma maximal_busy_interval_from_left_boundary :
  forall sched t1 t2,
    maximal_busy_interval_from sched t1 t2 ->
    t1 = 0 \/ ~ cpu_busy_at sched (pred t1).
Proof.
  intros sched t1 t2 [_ [Hleft _]].
  exact Hleft.
Qed.

Lemma maximal_busy_interval_from_right_boundary :
  forall sched t1 t2,
    maximal_busy_interval_from sched t1 t2 ->
    ~ cpu_busy_at sched t2.
Proof.
  intros sched t1 t2 [_ [_ Hright]].
  exact Hright.
Qed.

Lemma cumulative_cpu_service_full_busy_prefix :
  forall sched t,
    interval_busy sched 0 t ->
    cumulative_cpu_service sched t = t.
Proof.
  intros sched t Hbusy.
  induction t as [| t' IH].
  - reflexivity.
  - rewrite cumulative_cpu_service_step.
    assert (Hslot : cpu_busy_at sched t').
    { apply Hbusy.
      lia. }
    rewrite cpu_busy_at_cpu_service_one by exact Hslot.
    rewrite IH.
    + lia.
    + intros k Hk.
      apply Hbusy.
      lia.
Qed.

Lemma cpu_service_between_busy_interval_eq_length :
  forall sched t1 t2,
    busy_interval sched t1 t2 ->
    cpu_service_between sched t1 t2 = t2 - t1.
Proof.
  intros sched t1 t2 [Hlt Hbusy].
  remember (t2 - t1) as len eqn:Hlen.
  revert t1 t2 Hlt Hbusy Hlen.
  induction len as [| len IH]; intros t1 t2 Hlt Hbusy Hlen.
  - lia.
  - destruct (Nat.eq_dec t2 (S t1)) as [-> | Hneq].
    + unfold cpu_service_between.
      rewrite cumulative_cpu_service_step.
      rewrite cpu_busy_at_cpu_service_one.
      * lia.
      * apply Hbusy. lia.
    + assert (Hlt' : S t1 < t2) by lia.
      assert (Hsuffix : busy_interval sched (S t1) t2).
      { apply busy_interval_suffix with (t1 := t1).
        - split; assumption.
        - lia.
        - exact Hlt'. }
      rewrite (cpu_service_between_split sched t1 (S t1) t2) by lia.
      unfold cpu_service_between at 1.
      rewrite cumulative_cpu_service_step.
      rewrite cpu_busy_at_cpu_service_one.
      * assert (Hlen' : len = t2 - S t1) by lia.
        rewrite (IH (S t1) t2 Hlt' (proj2 Hsuffix) Hlen').
        lia.
      * apply Hbusy. lia.
Qed.

Lemma cpu_service_between_le_length :
  forall sched t1 t2,
    t1 <= t2 ->
    cpu_service_between sched t1 t2 <= t2 - t1.
Proof.
  intros sched t1 t2 Hle.
  remember (t2 - t1) as len eqn:Hlen.
  revert t1 t2 Hle Hlen.
  induction len as [| len IH]; intros t1 t2 Hle Hlen.
  - assert (t1 = t2) by lia.
    subst t2.
    rewrite cpu_service_between_refl.
    lia.
  - destruct (Nat.eq_dec t2 t1) as [-> | Hneq].
    + lia.
    + assert (Hlt : t1 < t2) by lia.
      destruct (Nat.eq_dec t2 (S t1)) as [-> | Hneq'].
      * assert (Hstep :
            cpu_service_between sched t1 (S t1) = cpu_service_at sched t1).
        { unfold cpu_service_between.
          rewrite cumulative_cpu_service_step.
          destruct (cpu_service_at sched t1); lia. }
        rewrite Hstep.
        replace (S t1 - t1) with 1 in Hlen by lia.
        assert (len = 0) by lia.
        subst len.
        assert (Hslot : cpu_service_at sched t1 <= 1).
        { unfold cpu_service_at.
          destruct (sched t1 0); lia. }
        exact Hslot.
      * assert (Hlt' : S t1 < t2) by lia.
        assert (Hle' : S t1 <= t2) by lia.
        assert (Hlen' : len = t2 - S t1) by lia.
        rewrite (cpu_service_between_split sched t1 (S t1) t2) by lia.
        unfold cpu_service_between at 1.
        rewrite cumulative_cpu_service_step.
        pose proof (IH (S t1) t2 Hle' Hlen') as Hrest.
        assert (Hslot : cpu_service_at sched t1 <= 1).
        { unfold cpu_service_at.
          destruct (sched t1 0); lia. }
        lia.
Qed.

Lemma cpu_service_between_not_busy_slot :
  forall sched t1 t2 t,
    t1 <= t < t2 ->
    ~ cpu_busy_at sched t ->
    cpu_service_between sched t1 t2 < t2 - t1.
Proof.
  intros sched t1 t2 t Ht Hidle.
  assert (Hsplit :
      cpu_service_between sched t1 t2 =
      cpu_service_between sched t1 t +
      cpu_service_between sched t t2) by
      (apply cpu_service_between_split; lia).
  assert (Hsplit' :
      cpu_service_between sched t t2 =
      cpu_service_at sched t + cpu_service_between sched (S t) t2).
  {
    rewrite (cpu_service_between_split sched t (S t) t2) by lia.
    unfold cpu_service_between at 1.
    rewrite cumulative_cpu_service_step.
    lia.
  }
  rewrite Hsplit.
  rewrite Hsplit'.
  rewrite cpu_not_busy_at_cpu_service_zero by exact Hidle.
  assert (Hbound1 : cpu_service_between sched t1 t <= t - t1).
  { apply cpu_service_between_le_length. lia. }
  assert (Hbound2 : cpu_service_between sched (S t) t2 <= t2 - S t).
  { apply cpu_service_between_le_length. lia. }
  lia.
Qed.

Lemma service_job_le_cumulative_cpu_service :
  forall sched j t,
    service_job 1 sched j t <= cumulative_cpu_service sched t.
Proof.
  intros sched j t.
  induction t as [| t' IH].
  - reflexivity.
  - rewrite service_job_step.
    rewrite cumulative_cpu_service_step.
    destruct (sched t' 0) as [j'|] eqn:Hsched.
    + unfold cpu_count, runs_on.
      rewrite Hsched.
      unfold cpu_service_at.
      rewrite Hsched.
      destruct (Nat.eqb j' j); lia.
    + unfold cpu_count, runs_on.
      rewrite Hsched.
      unfold cpu_service_at.
      rewrite Hsched.
      lia.
Qed.

Lemma service_between_le_cpu_service_between :
  forall sched j t1 t2,
    t1 <= t2 ->
    service_between 1 sched j t1 t2 <= cpu_service_between sched t1 t2.
Proof.
  intros sched j t1 t2 Hle.
  remember (t2 - t1) as len eqn:Hlen.
  revert t1 t2 Hle Hlen.
  induction len as [| len IH]; intros t1 t2 Hle Hlen.
  - assert (t1 = t2) by lia.
    subst t2.
    rewrite service_between_refl.
    rewrite cpu_service_between_refl.
    lia.
  - destruct (Nat.eq_dec t2 t1) as [-> | Hneq].
    + lia.
    + destruct (Nat.eq_dec t2 (S t1)) as [-> | Hneq'].
      * unfold service_between, cpu_service_between.
        rewrite service_job_step.
        rewrite cumulative_cpu_service_step.
        assert (Hslot : cpu_count 1 sched j t1 <= cpu_service_at sched t1).
        { unfold cpu_count, runs_on, cpu_service_at.
          destruct (sched t1 0) as [j'|] eqn:Hsched.
          - destruct (Nat.eqb j' j); lia.
          - lia. }
        replace (service_job 1 sched j t1 + cpu_count 1 sched j t1 - service_job 1 sched j t1)
          with (cpu_count 1 sched j t1) by lia.
        replace (cumulative_cpu_service sched t1 + cpu_service_at sched t1 - cumulative_cpu_service sched t1)
          with (cpu_service_at sched t1) by lia.
        exact Hslot.
      * assert (Hle' : S t1 <= t2) by lia.
        assert (Hlen' : len = t2 - S t1) by lia.
        rewrite (service_between_split 1 sched j t1 (S t1) t2) by lia.
        rewrite (cpu_service_between_split sched t1 (S t1) t2) by lia.
        assert (Hslot : service_between 1 sched j t1 (S t1) <= cpu_service_between sched t1 (S t1)).
        {
          unfold service_between, cpu_service_between.
          rewrite service_job_step.
          rewrite cumulative_cpu_service_step.
          assert (Hslot0 : cpu_count 1 sched j t1 <= cpu_service_at sched t1).
          { unfold cpu_count, runs_on, cpu_service_at.
            destruct (sched t1 0) as [j'|] eqn:Hsched.
            - destruct (Nat.eqb j' j); lia.
            - lia. }
          replace (service_job 1 sched j t1 + cpu_count 1 sched j t1 - service_job 1 sched j t1)
            with (cpu_count 1 sched j t1) by lia.
          replace (cumulative_cpu_service sched t1 + cpu_service_at sched t1 - cumulative_cpu_service sched t1)
            with (cpu_service_at sched t1) by lia.
          exact Hslot0.
        }
        pose proof (IH (S t1) t2 Hle' Hlen') as Hrest.
        lia.
Qed.

Lemma service_between_le_busy_interval_length :
  forall sched j t1 t2,
    busy_interval sched t1 t2 ->
    service_between 1 sched j t1 t2 <= t2 - t1.
Proof.
  intros sched j t1 t2 Hbusy.
  eapply Nat.le_trans.
  - apply service_between_le_cpu_service_between.
    destruct Hbusy as [Hlt _].
    lia.
  - rewrite cpu_service_between_busy_interval_eq_length by exact Hbusy.
    lia.
Qed.
