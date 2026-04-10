# Proof Progress: EDF Optimality Phase 6 — swap_at preserves feasible_schedule_on

## Status Overview
- Overall: Complete
- Complete Lemmas: 5/5
- Unproven (`Admitted`): none
- Failed/Abandoned Items: none

## Completed Lemmas

### Lemma 14: `swap_at_preserves_missed_deadline_other_job`
```coq
Lemma swap_at_preserves_missed_deadline_other_job :
  forall jobs sched j j' t t' x,
    sched t 0 = Some j ->
    sched t' 0 = Some j' ->
    x <> j ->
    x <> j' ->
    missed_deadline jobs 1 (swap_at sched t t') x <->
    missed_deadline jobs 1 sched x.
Proof.
  intros jobs sched j j' t t' x Hj Hj' Hxj Hxj'.
  rewrite !missed_deadline_iff_service_lt_cost_at_deadline.
  rewrite (swap_at_service_unchanged_other_job sched x j j' t t'
             (job_abs_deadline (jobs x)) Hj Hj' Hxj Hxj').
  tauto.
Qed.
```

### Lemma 15: `swap_at_improves_front_job`
```coq
Lemma swap_at_improves_front_job :
  forall jobs sched j j' t t',
    t <= t' ->
    t' < job_abs_deadline (jobs j') ->
    sched t 0 = Some j ->
    sched t' 0 = Some j' ->
    ~ missed_deadline jobs 1 sched j' ->
    ~ missed_deadline jobs 1 (swap_at sched t t') j'.
```
Key: rewrite with `missed_deadline_iff_service_lt_cost_at_deadline`, case split `j = j'` / `j ≠ j'`.
- j = j': `service_job_eq_of_cpu_count_eq` + `cpu_count_1_swap_at_t1/t2/other`
- j ≠ j': `swap_at_service_j2_after_t2` with T = deadline(j') > t'

**Error encountered**: `exact (Hne Heq)` goal was `t < t`, not `False`. Fix: add `exfalso.` before.

### Lemma 16': `swap_at_service_at_deadline_same_for_back_job`
```coq
Lemma swap_at_service_at_deadline_same_for_back_job :
  forall jobs sched j j' t t',
    t <= t' ->
    t' < job_abs_deadline (jobs j) ->
    sched t 0 = Some j ->
    sched t' 0 = Some j' ->
    service_job 1 (swap_at sched t t') j (job_abs_deadline (jobs j)) =
    service_job 1 sched j (job_abs_deadline (jobs j)).
```
Symmetric to Lemma 15. j ≠ j' case uses `swap_at_service_j1_after_t2`.

### Lemma 16: `swap_at_does_not_hurt_later_deadline_job`
Trivial from Lemma 16' via `missed_deadline_iff_service_lt_cost_at_deadline`.

### Lemma 17: `swap_at_preserves_feasible_schedule_on`
Case split on x: j' → L15+Hfeas, j → L16+lia, other → L14+Hfeas.

## Proof Attempts & Diagnostics

### Compilation Error 1 (Lemma 15)
- Error: `"Hne Heq" has type "False" while it is expected to have type "t < t"`
- Diagnosis: After `subst t'`, the goal is `t < t`, not `False`. Need `exfalso.` first.
- Fix: Replace `exact (Hne Heq)` with `exfalso. exact (Hne Heq)`.

### Compilation Error 2 (Lemma 16')
- Same issue as Error 1, same fix applied.

## TODO
(none — all complete)
