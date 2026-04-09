# Proof Progress: EDFLemmas Section 1 — Service / Completion 補題

## Status Overview
- Overall: Complete
- Complete Lemmas: 12/12
- Unproven (`Admitted`): none
- Failed/Abandoned Items: none

## Completed Lemmas

### `service_between` (definition)
```coq
Definition service_between
    (m : nat) (sched : Schedule) (j : JobId) (t1 t2 : Time) : nat :=
  service_job m sched j t2 - service_job m sched j t1.
```

### `completed_iff_service_ge_cost`
```coq
Lemma completed_iff_service_ge_cost :
  forall jobs m sched j t,
    completed jobs m sched j t <->
    job_cost (jobs j) <= service_job m sched j t.
Proof.
  intros jobs m sched j t.
  unfold completed. lia.
Qed.
```

### `not_completed_iff_service_lt_cost`
```coq
Lemma not_completed_iff_service_lt_cost :
  forall jobs m sched j t,
    ~ completed jobs m sched j t <->
    service_job m sched j t < job_cost (jobs j).
Proof.
  intros jobs m sched j t.
  rewrite completed_iff_service_ge_cost. lia.
Qed.
```

### `missed_deadline_iff_not_completed_at_deadline`
```coq
Lemma missed_deadline_iff_not_completed_at_deadline :
  forall jobs m sched j,
    missed_deadline jobs m sched j <->
    ~ completed jobs m sched j (job_abs_deadline (jobs j)).
Proof.
  intros jobs m sched j.
  unfold missed_deadline. tauto.
Qed.
```

### `missed_deadline_iff_service_lt_cost_at_deadline`
```coq
Lemma missed_deadline_iff_service_lt_cost_at_deadline :
  forall jobs m sched j,
    missed_deadline jobs m sched j <->
    service_job m sched j (job_abs_deadline (jobs j)) < job_cost (jobs j).
Proof.
  intros jobs m sched j.
  rewrite missed_deadline_iff_not_completed_at_deadline.
  rewrite not_completed_iff_service_lt_cost.
  tauto.
Qed.
```

### `service_between_eq`
```coq
Lemma service_between_eq :
  forall m sched j t1 t2,
    t1 <= t2 ->
    service_between m sched j t1 t2 =
    service_job m sched j t2 - service_job m sched j t1.
Proof.
  intros m sched j t1 t2 _.
  unfold service_between. reflexivity.
Qed.
```

### `service_between_0_r`
```coq
Lemma service_between_0_r :
  forall m sched j t,
    service_between m sched j 0 t = service_job m sched j t.
Proof.
  intros m sched j t.
  unfold service_between. simpl. lia.
Qed.
```
Note: `simpl` reduces `service_job m sched j 0` to `0`, leaving `service_job m sched j t - 0`, then `lia` closes.

### `service_between_refl`
```coq
Lemma service_between_refl :
  forall m sched j t,
    service_between m sched j t t = 0.
Proof.
  intros m sched j t.
  unfold service_between. lia.
Qed.
```

### `service_between_split`
```coq
Lemma service_between_split :
  forall m sched j t1 t2 t3,
    t1 <= t2 ->
    t2 <= t3 ->
    service_between m sched j t1 t3 =
    service_between m sched j t1 t2 +
    service_between m sched j t2 t3.
Proof.
  intros m sched j t1 t2 t3 H12 H23.
  unfold service_between.
  pose proof (service_job_monotone m sched j t1 t2 H12) as Hle12.
  pose proof (service_job_monotone m sched j t2 t3 H23) as Hle23.
  lia.
Qed.
```

### `service_between_nonneg`
```coq
Lemma service_between_nonneg :
  forall m sched j t1 t2,
    t1 <= t2 ->
    service_job m sched j t1 <= service_job m sched j t2.
Proof.
  intros m sched j t1 t2 Hle.
  exact (service_job_monotone m sched j t1 t2 Hle).
Qed.
```

### `service_before_release_zero`
```coq
Lemma service_before_release_zero :
  forall jobs m sched j t,
    valid_schedule jobs m sched ->
    t <= job_release (jobs j) ->
    service_job m sched j t = 0.
Proof.
  intros jobs m sched j t Hvalid Hle.
  induction t as [| t' IH].
  - simpl. reflexivity.
  - assert (Ht'lt : t' < job_release (jobs j)) by lia.
    rewrite service_job_step.
    assert (Ht'le : t' <= job_release (jobs j)) by lia.
    rewrite (IH Ht'le).
    assert (Hzero : cpu_count m sched j t' = 0).
    { apply (proj2 (cpu_count_zero_iff_not_executed m sched j t')).
      intros c Hclt Hrun.
      pose proof (valid_no_run_before_release jobs m sched j t' c Hvalid Hclt Hrun) as Hrel.
      unfold released in Hrel. lia. }
    lia.
Qed.
```

### `service_at_release_zero`
```coq
Lemma service_at_release_zero :
  forall jobs m sched j,
    valid_schedule jobs m sched ->
    service_job m sched j (job_release (jobs j)) = 0.
Proof.
  intros jobs m sched j Hvalid.
  apply (service_before_release_zero jobs m sched j (job_release (jobs j))).
  - exact Hvalid.
  - lia.
Qed.
```
Note: `apply service_before_release_zero` fails ("Unable to find an instance for jobs"); must use `apply (service_before_release_zero jobs m sched j ...)` with explicit args.

## Proof Attempts & Diagnostics

### `service_between_0_r` — first attempt failed
- `simpl. reflexivity.` fails: goal becomes `service_job m sched j t - 0 = service_job m sched j t`, not definitionally equal.
- Fix: use `lia` instead of `reflexivity`.

### `service_at_release_zero` — first attempt failed
- `apply service_before_release_zero.` fails with "Unable to find an instance for the variable jobs".
- Fix: use `apply (service_before_release_zero jobs m sched j (job_release (jobs j)))` with explicit arguments.

## TODO

(all done)
