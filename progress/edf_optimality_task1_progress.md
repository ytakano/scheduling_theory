# Proof Progress: eligible_feasible_implies_runs_later_before_deadline

## Status Overview
- Overall: Complete
- Complete Lemmas: 2/2
- Unproven (`Admitted`): none
- Failed/Abandoned Items: none

## Completed Lemmas

### `service_increases_implies_executed_in_interval` (6-1)

Helper lemma: if service strictly increases over [t1, t2), there exists t' ∈ [t1, t2) with cpu_count > 0.

```coq
Lemma service_increases_implies_executed_in_interval :
  forall m sched j t1 t2,
    t1 < t2 ->
    service_job m sched j t1 < service_job m sched j t2 ->
    exists t',
      t1 <= t' < t2 /\
      0 < cpu_count m sched j t'.
Proof.
  intros m sched j t1 t2 Hlt Hinc.
  induction t2 as [| t2' IH].
  - lia.
  - rewrite service_job_step in Hinc.
    destruct (Nat.eq_dec (cpu_count m sched j t2') 0) as [Hzero | Hpos].
    + rewrite Hzero in Hinc.
      rewrite Nat.add_0_r in Hinc.
      assert (Hlt' : t1 < t2').
      { destruct (Nat.eq_dec t1 t2') as [Heq | Hne].
        - subst t2'. lia.
        - lia. }
      destruct (IH Hlt' Hinc) as [t' [[Hle Hlt''] Hcpu]].
      exists t'. split. split. exact Hle. lia. exact Hcpu.
    + exists t2'. split. split. lia. lia. lia.
Qed.
```

### `eligible_feasible_implies_runs_later_before_deadline` (6-2)

Main lemma: if j is eligible at t in a feasible schedule, then j runs at some t' ∈ [t, deadline(j)).

```coq
Lemma eligible_feasible_implies_runs_later_before_deadline :
  forall J jobs sched j t,
    J j ->
    valid_schedule jobs 1 sched ->
    feasible_schedule_on J jobs 1 sched ->
    eligible jobs 1 sched j t ->
    exists t',
      t <= t' /\
      t' < job_abs_deadline (jobs j) /\
      sched t' 0 = Some j.
Proof.
  intros J jobs sched j t HJj Hvalid Hfeas Helig.
  assert (Hlt_cost : service_job 1 sched j t < job_cost (jobs j)).
  { apply not_completed_iff_service_lt_cost. exact (proj2 Helig). }
  assert (Hge_cost : job_cost (jobs j) <= service_job 1 sched j (job_abs_deadline (jobs j))).
  { apply completed_iff_service_ge_cost.
    apply NNPP.
    unfold missed_deadline in Hfeas.
    exact (Hfeas j HJj). }
  assert (Hinc : service_job 1 sched j t < service_job 1 sched j (job_abs_deadline (jobs j))).
  { lia. }
  assert (Htlt : t < job_abs_deadline (jobs j)).
  { destruct (classic (t < job_abs_deadline (jobs j))) as [Hlt | Hnlt].
    - exact Hlt.
    - exfalso.
      assert (Hge : job_abs_deadline (jobs j) <= t) by lia.
      pose proof (service_job_monotone 1 sched j _ _ Hge) as Hmon.
      lia. }
  destruct (service_increases_implies_executed_in_interval 1 sched j t (job_abs_deadline (jobs j))
              Htlt Hinc) as [t' [[Hle Hlt'] Hcpu]].
  destruct (proj1 (cpu_count_pos_iff_executed 1 sched j t') Hcpu) as [c [Hclt Hrun]].
  assert (Hc0 : c = 0) by lia.
  subst c.
  exists t'. split. exact Hle. split. exact Hlt'. exact Hrun.
Qed.
```

## Proof Attempts & Diagnostics

### Errors encountered during development

1. `Nat.lt_or_eq` — does not exist in Rocq 9 stdlib. Fixed by using `Nat.eq_dec` instead.
2. `Nat.le_or_lt` — does not exist. Fixed by using `classic` from Classical.
3. `le_or_lt` (unqualified) — not in scope. Fixed with `classic`.
4. `by_contra` — not in scope. Fixed by using `destruct (classic ...) as [Hlt | Hnlt]`.
5. `apply (Hfeas j HJj)` on goal `~missed_deadline` failed because `feasible_schedule_on` provides `~missed_deadline` and we needed `completed`. Fixed by:
   - `apply NNPP` (converts `~~P → P` proof obligation)
   - `unfold missed_deadline in Hfeas` to expose the `~~completed` structure

## TODO

(all done)
