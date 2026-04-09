# Proof Progress: Partitioned Scheduling — Local/Global Lifting

## Status Overview
- Overall: **Complete**
- Complete Lemmas: 3/3
- Unproven (`Admitted`): none
- Failed/Abandoned Items: none

---

## Completed Lemmas

### `missed_deadline_iff_on_assigned_cpu`

```coq
Corollary missed_deadline_iff_on_assigned_cpu :
  forall jobs sched j,
    respects_assignment sched ->
    missed_deadline jobs m sched j <->
      missed_deadline jobs 1 (cpu_schedule sched (assign j)) j.
Proof.
  intros jobs sched j Hresp.
  unfold missed_deadline.
  pose proof (completed_iff_on_assigned_cpu jobs sched Hresp j
                (job_abs_deadline (jobs j))) as Hiff.
  tauto.
Qed.
```

Strategy: unfold `missed_deadline` to `~completed ...`, instantiate `completed_iff_on_assigned_cpu`
at `t := job_abs_deadline (jobs j)`, then `tauto`.

---

### `local_feasible_implies_global_feasible_schedule`

```coq
Theorem local_feasible_implies_global_feasible_schedule :
  forall jobs sched,
    respects_assignment sched ->
    (forall c, c < m -> feasible_schedule jobs 1 (cpu_schedule sched c)) ->
    feasible_schedule jobs m sched.
Proof.
  intros jobs sched Hresp Hlocal.
  unfold feasible_schedule.
  intro j.
  pose proof (valid_assignment j) as Hlt.
  pose proof (Hlocal (assign j) Hlt) as Hfeas.
  unfold feasible_schedule in Hfeas.
  pose proof (Hfeas j) as Hnmiss.
  rewrite missed_deadline_iff_on_assigned_cpu by exact Hresp.
  exact Hnmiss.
Qed.
```

Strategy: for any `j`, look up per-CPU feasibility at `assign j`, get `~missed_deadline` locally,
then use `missed_deadline_iff_on_assigned_cpu` to transfer to global.

---

### `local_valid_feasible_implies_global`

```coq
Corollary local_valid_feasible_implies_global :
  forall jobs sched xs,
    valid_partitioned_schedule jobs sched xs ->
    (forall c, c < m ->
      valid_schedule jobs 1 (cpu_schedule sched c) /\
      feasible_schedule jobs 1 (cpu_schedule sched c)) ->
    valid_schedule jobs m sched /\ feasible_schedule jobs m sched.
Proof.
  intros jobs sched xs Hvps Hlocal.
  destruct Hvps as [Hpart Hresp].
  split.
  - apply local_to_global_validity with xs.
    + exact (conj Hpart Hresp).
    + intros c Hlt. exact (proj1 (Hlocal c Hlt)).
  - apply local_feasible_implies_global_feasible_schedule.
    + exact Hresp.
    + intros c Hlt. exact (proj2 (Hlocal c Hlt)).
Qed.
```

Strategy: destruct `valid_partitioned_schedule`; split and apply the two lifting theorems separately.

---

## TODO
(none — all goals complete)
