# Proof Progress: PartitionedCompose

## Status Overview
- Overall: Complete
- Complete Lemmas: 6/6
- Unproven (`Admitted`): none
- Failed/Abandoned Items: none

## Completed Lemmas

### `glue_local_schedules`

```coq
Definition glue_local_schedules (m : nat) (locals : CPU -> Schedule) : Schedule :=
  fun t c => if c <? m then locals c t 0 else None.
```

### `cpu_schedule_glue_eq`

```coq
Lemma cpu_schedule_glue_eq :
    forall m (locals : CPU -> Schedule) c,
      c < m ->
      (forall t cpu', 0 < cpu' -> locals c t cpu' = None) ->
      cpu_schedule (glue_local_schedules m locals) c = locals c.
Proof.
  intros m locals c Hc Hidle.
  extensionality t. extensionality cpu'.
  unfold cpu_schedule, glue_local_schedules.
  destruct (Nat.eqb cpu' 0) eqn:E0.
  - apply Nat.eqb_eq in E0. subst cpu'.
    apply Nat.ltb_lt in Hc. rewrite Hc. reflexivity.
  - apply Nat.eqb_neq in E0.
    symmetry. apply Hidle. lia.
Qed.
```

### `scheduler_rel_single_cpu_idle`

```coq
Lemma scheduler_rel_single_cpu_idle :
    forall spec cands jobs (sched : Schedule) t cpu',
      scheduler_rel (single_cpu_dispatch_schedule spec cands) jobs 1 sched ->
      0 < cpu' ->
      sched t cpu' = None.
Proof.
  intros spec cands jobs sched t cpu' [_ Hsteps] Hlt.
  exact (proj2 (Hsteps t) cpu' Hlt).
Qed.
```

### `glue_local_rels_imply_partitioned_schedule_on`

```coq
Theorem glue_local_rels_imply_partitioned_schedule_on :
    forall m spec (cands : CPU -> CandidateSource)
           jobs (locals : CPU -> Schedule),
      (forall c, c < m ->
        scheduler_rel
          (single_cpu_dispatch_schedule spec (cands c))
          jobs 1 (locals c)) ->
      raw_partitioned_schedule_on m spec cands jobs
        (glue_local_schedules m locals).
Proof.
  intros m spec cands jobs locals Hlocals.
  apply (proj2 (partitioned_schedule_on_iff_local_rel m spec cands jobs
                  (glue_local_schedules m locals))).
  intros c Hlt.
  pose proof (Hlocals c Hlt) as Hrel.
  rewrite (cpu_schedule_glue_eq m locals c Hlt).
  - exact Hrel.
  - intros t cpu' Hcpu'.
    exact (scheduler_rel_single_cpu_idle spec (cands c) jobs (locals c) t cpu'
             Hrel Hcpu').
Qed.
```

### `local_witnesses_imply_partitioned_schedulable_by_on`

```coq
Theorem local_witnesses_imply_partitioned_schedulable_by_on :
    forall (assign : JobId -> CPU) (m : nat)
           (valid_assignment : forall j, assign j < m)
           (spec : GenericDispatchSpec)
           (J : JobId -> Prop)
           (cands : CPU -> CandidateSource)
           (cands_spec : forall c, c < m ->
             CandidateSourceSpec (local_jobset assign J c) (cands c))
           (jobs : JobId -> Job)
           (locals : CPU -> Schedule),
      (forall c, c < m ->
        scheduler_rel
          (single_cpu_dispatch_schedule spec (cands c))
          jobs 1 (locals c) /\
        feasible_schedule_on (local_jobset assign J c) jobs 1 (locals c)) ->
      schedulable_by_on J (partitioned_scheduler m spec cands) jobs m.
Proof.
  (* set sched := glue, prove raw_partitioned_schedule_on, rewrite
     feasibility via cpu_schedule_glue_eq, apply
     partitioned_schedulable_by_on_from_local *)
  ...
Qed.
```

### `partitioned_edf_scheduler` and `local_edf_witnesses_imply_partitioned_edf_schedulable_by_on`

Both in `theories/PartitionedPolicies/PartitionedEDF.v`. Thin wrappers that unfold `edf_scheduler` and delegate to `local_witnesses_imply_partitioned_schedulable_by_on`.

## TODO
(none — all items complete)
