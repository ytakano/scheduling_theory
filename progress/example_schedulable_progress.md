# Proof Progress: example_schedulable

## Status Overview
- Overall: Complete
- Complete Lemmas: 4/4
- Unproven (`Admitted`): none
- Failed/Abandoned Items: none

## Completed Lemmas

### `cpu_count_le_m`

```coq
Lemma cpu_count_le_m : forall m sched j t,
    cpu_count sched j t m <= m.
Proof.
  induction m as [| m' IH]; intros sched j t.
  - simpl. lia.
  - simpl.
    pose proof (IH sched j t) as Hle.
    destruct (runs_on sched j t m'); simpl; lia.
Qed.
```

### `service_le_m_mul_t`

```coq
Lemma service_le_m_mul_t : forall m sched j t,
    service m sched j t <= m * t.
Proof.
  intros m sched j.
  induction t as [| t' IH].
  - simpl. lia.
  - rewrite service_step.
    pose proof (cpu_count_le_m m sched j t') as Hle.
    lia.
Qed.
```

### `ex1_job0_completed`

```coq
Lemma ex1_job0_completed : completed jobs_ex1 1 sched_ex1 0 3.
Proof.
  unfold completed, jobs_ex1, job_ex1, sched_ex1.
  simpl.
  lia.
Qed.
```

### `ex2_any_sched_misses`

```coq
Lemma ex2_any_sched_misses : forall sched, missed_deadline jobs_ex2 1 sched 0.
Proof.
  intro sched.
  unfold missed_deadline, completed, jobs_ex2, job_ex2.
  simpl.
  pose proof (service_le_m_mul_t 1 sched 0 2) as Hle.
  simpl in Hle.
  lia.
Qed.
```

## TODO
(すべて完了)
