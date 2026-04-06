# Proof Progress: Phase 0 — Common Foundation

## Status Overview
- Overall: Complete
- Complete Lemmas: 16/16
- Unproven (`Admitted`): none
- Failed/Abandoned Items: none

## Completed Lemmas

### `runs_on_true_iff`
```coq
Lemma runs_on_true_iff : forall sched j t c,
    runs_on sched j t c = true <-> sched t c = Some j.
Proof.
  intros. unfold runs_on.
  destruct (sched t c) as [j'|].
  - split.
    + intro H. apply Nat.eqb_eq in H. subst. reflexivity.
    + intro H. injection H as Heq. subst. apply Nat.eqb_refl.
  - split; discriminate.
Qed.
```

### `runs_on_false_iff`
```coq
Lemma runs_on_false_iff : forall sched j t c,
    runs_on sched j t c = false <-> sched t c <> Some j.
Proof.
  intros. unfold runs_on.
  destruct (sched t c) as [j'|].
  - split.
    + intro H. apply Nat.eqb_neq in H.
      intro Heq. injection Heq as Heq'. subst. exact (H eq_refl).
    + intro H. apply Nat.eqb_neq.
      intro Heq. subst. exact (H eq_refl).
  - split.
    + intros _. discriminate.
    + intros _. reflexivity.
Qed.
```

### `service_step`
```coq
Lemma service_step : forall m sched j t,
    service m sched j (S t) = service m sched j t + cpu_count sched j t m.
Proof.
  intros. simpl. reflexivity.
Qed.
```

### `cpu_count_zero_iff_not_executed`
```coq
Lemma cpu_count_zero_iff_not_executed : forall m sched j t,
    cpu_count sched j t m = 0 <->
    forall c, c < m -> sched t c <> Some j.
Proof.
  induction m as [| m' IH]; intros sched j t.
  - split; [intros _ c Hlt; lia | intros; reflexivity].
  - split.
    + intros Hzero c Hlt.
      simpl in Hzero.
      destruct (runs_on sched j t m') eqn:Erun.
      * simpl in Hzero. lia.
      * simpl in Hzero.
        apply Nat.lt_succ_r in Hlt.
        destruct (Nat.eq_dec c m') as [-> | Hne].
        -- exact (proj1 (runs_on_false_iff sched j t m') Erun).
        -- apply (proj1 (IH sched j t) Hzero). lia.
    + intros Hnone.
      simpl.
      destruct (runs_on sched j t m') eqn:Erun.
      * apply runs_on_true_iff in Erun.
        exfalso. exact (Hnone m' (Nat.lt_succ_diag_r m') Erun).
      * simpl.
        apply (proj2 (IH sched j t)).
        intros c Hlt. apply Hnone. lia.
Qed.
```

### `cpu_count_pos_iff_executed`
```coq
Lemma cpu_count_pos_iff_executed : forall m sched j t,
    0 < cpu_count sched j t m <->
    exists c, c < m /\ sched t c = Some j.
Proof.
  induction m as [| m' IH]; intros sched j t.
  - simpl. split.
    + intro H. lia.
    + intros [c [Hlt _]]. lia.
  - split.
    + intros Hpos.
      simpl in Hpos.
      destruct (runs_on sched j t m') eqn:Erun.
      * apply runs_on_true_iff in Erun.
        exists m'. split. lia. exact Erun.
      * simpl in Hpos.
        destruct (proj1 (IH sched j t) Hpos) as [c' [Hlt' Hrun']].
        exists c'. split. lia. exact Hrun'.
    + intros [c [Hlt Hrun]].
      simpl.
      apply Nat.lt_succ_r in Hlt.
      destruct (Nat.eq_dec c m') as [-> | Hne].
      * assert (Hruns : runs_on sched j t m' = true).
        { apply runs_on_true_iff. exact Hrun. }
        rewrite Hruns. simpl. lia.
      * assert (Hlt' : c < m') by lia.
        assert (Hpos : 0 < cpu_count sched j t m').
        { apply (proj2 (IH sched j t)). exists c. split. exact Hlt'. exact Hrun. }
        destruct (runs_on sched j t m'); simpl; lia.
Qed.
```

### `cpu_count_le_1`
```coq
Lemma cpu_count_le_1 : forall m sched j t,
    no_duplication m sched ->
    cpu_count sched j t m <= 1.
Proof.
  induction m as [| m' IH]; intros sched j t Hnd.
  - simpl. lia.
  - simpl.
    destruct (runs_on sched j t m') eqn:Erun.
    + apply runs_on_true_iff in Erun.
      simpl.
      assert (Hzero : cpu_count sched j t m' = 0).
      { apply (proj2 (cpu_count_zero_iff_not_executed m' sched j t)).
        intros c Hlt Hrun.
        assert (Heq : c = m').
        { apply (Hnd j t c m'). lia. lia. exact Hrun. exact Erun. }
        lia. }
      lia.
    + simpl.
      assert (Hnd' : no_duplication m' sched).
      { intros j0 t0 c1 c2 H1 H2 H3 H4.
        apply (Hnd j0 t0 c1 c2). lia. lia. exact H3. exact H4. }
      exact (IH sched j t Hnd').
Qed.
```

### `service_le_succ`
```coq
Lemma service_le_succ : forall m sched j t,
    service m sched j t <= service m sched j (S t).
Proof.
  intros. rewrite service_step. lia.
Qed.
```

### `service_monotone`
```coq
Lemma service_monotone : forall m sched j t1 t2,
    t1 <= t2 ->
    service m sched j t1 <= service m sched j t2.
Proof.
  intros m sched j t1 t2 Hle.
  induction t2 as [| t2' IH].
  - assert (t1 = 0) by lia. subst. lia.
  - apply Nat.le_succ_r in Hle.
    destruct Hle as [Hle | Heq].
    + eapply Nat.le_trans. apply IH. exact Hle. apply service_le_succ.
    + subst. lia.
Qed.
```

### `service_increase_at_most_1`
```coq
Lemma service_increase_at_most_1 : forall m sched j t,
    no_duplication m sched ->
    service m sched j (S t) <= service m sched j t + 1.
Proof.
  intros m sched j t Hnd.
  rewrite service_step.
  pose proof (cpu_count_le_1 m sched j t Hnd). lia.
Qed.
```

### `service_no_increase_if_not_executed`
```coq
Lemma service_no_increase_if_not_executed : forall m sched j t,
    (forall c, c < m -> sched t c <> Some j) ->
    service m sched j (S t) = service m sched j t.
Proof.
  intros m sched j t Hnone.
  rewrite service_step.
  apply (proj2 (cpu_count_zero_iff_not_executed m sched j t)) in Hnone.
  lia.
Qed.
```

### `service_increases_iff_executed`
```coq
Lemma service_increases_iff_executed : forall m sched j t,
    no_duplication m sched ->
    (service m sched j (S t) = service m sched j t + 1 <->
     exists c, c < m /\ sched t c = Some j).
Proof.
  intros m sched j t Hnd.
  rewrite service_step.
  split.
  - intros Heq.
    apply (proj1 (cpu_count_pos_iff_executed m sched j t)).
    pose proof (cpu_count_le_1 m sched j t Hnd). lia.
  - intros Hexists.
    apply (proj2 (cpu_count_pos_iff_executed m sched j t)) in Hexists.
    pose proof (cpu_count_le_1 m sched j t Hnd). lia.
Qed.
```

### `completed_not_ready`
```coq
Lemma completed_not_ready : forall jobs m sched j t,
    completed jobs m sched j t -> ~ready jobs m sched j t.
Proof.
  unfold completed, ready.
  intros jobs m sched j t Hcomp [_ Hnot].
  exact (Hnot Hcomp).
Qed.
```

### `not_ready_before_release`
```coq
Lemma not_ready_before_release : forall jobs m sched j t,
    t < job_release (jobs j) -> ~ready jobs m sched j t.
Proof.
  unfold ready.
  intros jobs m sched j t Hlt [Hrel _]. lia.
Qed.
```

### `completed_monotone`
```coq
Lemma completed_monotone : forall jobs m sched j t1 t2,
    t1 <= t2 ->
    completed jobs m sched j t1 ->
    completed jobs m sched j t2.
Proof.
  unfold completed.
  intros jobs m sched j t1 t2 Hle Hcomp.
  eapply Nat.le_trans. exact Hcomp.
  apply service_monotone. exact Hle.
Qed.
```

### `ready_iff_released_and_not_completed`
```coq
Lemma ready_iff_released_and_not_completed : forall jobs m sched j t,
    ready jobs m sched j t <->
    job_release (jobs j) <= t /\ ~completed jobs m sched j t.
Proof.
  unfold ready. tauto.
Qed.
```

### `valid_no_run_before_release`, `valid_no_run_after_completion`, `valid_running_implies_ready`
```coq
(* All three follow by destructuring valid_schedule and applying the relevant conjunct *)
Proof.
  unfold valid_schedule.
  intros ... [H _] / [_ [H _]] / [_ [_ H]] Hlt Hrun.
  apply (H j t c); assumption.
Qed.
```

## TODO
(none — all lemmas complete)
