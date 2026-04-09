# Proof Progress: Phase 3 Partitioned.v Refactor

## Status Overview
- Overall: Complete
- Complete Lemmas: 6/6
- Unproven (`Admitted`): none
- Failed/Abandoned Items: none

## Completed Lemmas

### `candidates_for` simplification

Removed unused `jobs`, `sched`, `t` parameters.

```coq
Definition candidates_for (c : CPU) (xs : list JobId) : list JobId :=
  filter (fun j => Nat.eqb (assign j) c) xs.
```

### `candidates_for_assign_sound` (updated signature)

```coq
Lemma candidates_for_assign_sound :
  forall c xs j,
    In j (candidates_for c xs) -> assign j = c.
Proof.
  intros c xs j Hin.
  unfold candidates_for in Hin.
  apply filter_In in Hin.
  destruct Hin as [_ Heqb].
  apply Nat.eqb_eq in Heqb.
  exact Heqb.
Qed.
```

### `partitioned_schedule` (rewritten to local dispatch)

```coq
Definition partitioned_schedule (jobs : JobId -> Job) (sched : Schedule)
    (xs : list JobId) : Prop :=
  forall t c, c < m ->
    sched t c =
      spec.(dispatch) jobs 1 (cpu_schedule sched c) t (candidates_for c xs).
```

### `valid_partitioned_schedule` (simplified to alias)

```coq
Definition valid_partitioned_schedule (jobs : JobId -> Job) (sched : Schedule)
    (xs : list JobId) : Prop :=
  partitioned_schedule jobs sched xs.
```

### `partitioned_schedule_implies_respects_assignment` (new theorem)

```coq
Theorem partitioned_schedule_implies_respects_assignment :
  forall jobs sched xs,
    partitioned_schedule jobs sched xs ->
    respects_assignment sched.
Proof.
  intros jobs sched xs Hpart j t c Hlt Hrun.
  pose proof (Hpart t c Hlt) as Heq.
  rewrite Hrun in Heq.
  symmetry in Heq.
  apply (candidates_for_assign_sound c xs j).
  eapply spec.(dispatch_in_candidates).
  exact Heq.
Qed.
```

### `assignment_respect` (simplified)

```coq
Theorem assignment_respect :
  forall jobs sched xs,
    valid_partitioned_schedule jobs sched xs ->
    forall j t c,
      c < m -> sched t c = Some j -> assign j = c.
Proof.
  intros jobs sched xs Hvps j t c Hlt Hrun.
  exact (partitioned_schedule_implies_respects_assignment jobs sched xs Hvps j t c Hlt Hrun).
Qed.
```

### `partitioned_schedule_implies_valid_schedule` (new, replaces `local_to_global_validity`)

```coq
Theorem partitioned_schedule_implies_valid_schedule :
  forall jobs sched xs,
    partitioned_schedule jobs sched xs ->
    valid_schedule jobs m sched.
Proof.
  intros jobs sched xs Hpart j t c Hlt Hrun.
  pose proof (partitioned_schedule_implies_respects_assignment jobs sched xs Hpart) as Hresp.
  pose proof (Hpart t c Hlt) as Heq.
  rewrite Hrun in Heq. symmetry in Heq.
  pose proof (spec.(dispatch_ready) jobs 1 (cpu_schedule sched c) t (candidates_for c xs) j Heq) as Hready.
  unfold ready in Hready. destruct Hready as [Heloc _].
  unfold eligible in *.
  destruct Heloc as [Hrel Hncomp_local].
  split.
  - exact Hrel.
  - rewrite completed_iff_on_assigned_cpu by exact Hresp.
    pose proof (Hresp j t c Hlt Hrun) as Hassign.
    rewrite Hassign. exact Hncomp_local.
Qed.
```

### `local_valid_feasible_implies_global` (updated)

```coq
Corollary local_valid_feasible_implies_global :
  forall jobs sched xs,
    partitioned_schedule jobs sched xs ->
    (forall c, c < m -> feasible_schedule jobs 1 (cpu_schedule sched c)) ->
    valid_schedule jobs m sched /\ feasible_schedule jobs m sched.
Proof.
  intros jobs sched xs Hpart Hlocal.
  pose proof (partitioned_schedule_implies_respects_assignment jobs sched xs Hpart) as Hresp.
  split.
  - apply partitioned_schedule_implies_valid_schedule with xs. exact Hpart.
  - apply local_feasible_implies_global_feasible_schedule.
    + exact Hresp.
    + exact Hlocal.
Qed.
```

## TODO

(none — all complete)
