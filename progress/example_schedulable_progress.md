> Obsolete note
>
> This progress log predates the current concrete examples. The current source of truth is
> `SchedulableExamples.v`, `SchedulerInterface.v`, and `DispatchSchedulerBridge.v`.

# Proof Progress: example_schedulable

## Status Overview (v2 — schedulable_by / schedulable_by_on)
- Overall: Complete
- Complete Lemmas: 11/11 (v2) + 4/4 (v1 example_feasible)
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

### `schedulable_by_implies_feasible` (v2)

```coq
Lemma schedulable_by_implies_feasible :
    forall alg jobs m,
      schedulable_by alg jobs m -> feasible jobs m.
Proof.
  intros alg jobs m [Hvalid Hfeas].
  unfold feasible.
  exists (run_scheduler alg jobs m).
  split; assumption.
Qed.
```

### `schedulable_by_implies_schedulable_by_on` (v2)

```coq
Lemma schedulable_by_implies_schedulable_by_on :
    forall (J : JobId -> Prop) alg jobs m,
      schedulable_by alg jobs m -> schedulable_by_on J alg jobs m.
Proof.
  intros J alg jobs m [Hvalid Hfeas].
  unfold schedulable_by_on, feasible_schedule_on.
  split.
  - exact Hvalid.
  - intros j _HJ. exact (Hfeas j).
Qed.
```

### `schedulable_by_on_monotone` (v2)

```coq
Lemma schedulable_by_on_monotone :
    forall (J J' : JobId -> Prop) alg jobs m,
      (forall j, J j -> J' j) ->
      schedulable_by_on J' alg jobs m ->
      schedulable_by_on J alg jobs m.
Proof.
  intros J J' alg jobs m Hsubset [Hvalid Hfeas].
  unfold schedulable_by_on, feasible_schedule_on.
  split.
  - exact Hvalid.
  - intros j HJ. exact (Hfeas j (Hsubset j HJ)).
Qed.
```

### Section SchedulableExample lemmas (v2)

All compiled successfully in first attempt (2026-04-08):
- `sc_cpu_count_le_1`: `simpl; unfold runs_on, sched_sc; rewrite Nat.eqb_refl; destruct; lia`
- `sc_service_le_t`: induction + `service_job_step` + `sc_cpu_count_le_1` + `lia`
- `sc_valid_schedule`: `c < 1 → c = 0`; `injection Hrun as Hj; subst j`; `Nat.ltb_lt`; `sc_service_le_t`
- `sc_job0_completed`: `unfold ...; simpl; lia`
- `sc_job0_meets_deadline`: `intro Hmiss; exact (Hmiss sc_job0_completed)`
- `sc_feasible_schedule_on`: `intros j Hj; subst j; exact sc_job0_meets_deadline`
- `sc_schedulable_by_on`: `rewrite alg_sc_runs_sched_sc; split; [exact ... | exact ...]`
- `sc_schedulable_by_on_empty`: `apply schedulable_by_on_monotone`; `False_ind`

## TODO
(すべて完了 — v1 + v2)
