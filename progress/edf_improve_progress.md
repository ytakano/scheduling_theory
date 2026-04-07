# Proof Progress: EDF Improvement

## Status Overview
- Overall: Complete
- Complete Lemmas: 6/6
- Unproven (`Admitted`): none
- Failed/Abandoned Items: none

## Completed Lemmas

### A1: `choose_edf_none_if_no_ready`

```coq
Lemma choose_edf_none_if_no_ready : forall jobs m sched t candidates,
    (forall j, In j candidates -> ~ready jobs m sched j t) ->
    choose_edf jobs m sched t candidates = None.
Proof.
  intros jobs m sched t candidates Hnone.
  unfold choose_edf.
  apply min_dl_job_none_iff.
  induction candidates as [| j0 rest IH].
  - reflexivity.
  - simpl. destruct (readyb jobs m sched j0 t) eqn:Erb.
    + exfalso. apply (Hnone j0 (or_introl eq_refl)).
      apply readyb_iff. exact Erb.
    + apply IH. intros j Hin. apply Hnone. right. exact Hin.
Qed.
```

### B1: `choose_edf_complete`

```coq
Lemma choose_edf_complete : forall jobs m sched t candidates,
    NoDup candidates ->
    (forall j, ready jobs m sched j t <-> In j candidates) ->
    (exists j, ready jobs m sched j t) ->
    exists j', choose_edf jobs m sched t candidates = Some j'.
Proof.
  intros jobs m sched t candidates Hnd Href [j Hready].
  apply choose_edf_some_if_exists.
  exists j. split.
  - apply Href. exact Hready.
  - exact Hready.
Qed.
```

### B2: `choose_edf_optimal`

```coq
Lemma choose_edf_optimal : forall jobs m sched t candidates j,
    NoDup candidates ->
    (forall j', ready jobs m sched j' t <-> In j' candidates) ->
    choose_edf jobs m sched t candidates = Some j ->
    forall j', ready jobs m sched j' t ->
    job_abs_deadline (jobs j) <= job_abs_deadline (jobs j').
Proof.
  intros jobs m sched t candidates j Hnd Href Hchoose j' Hready.
  apply (choose_edf_min_deadline jobs m sched t candidates j Hchoose).
  - apply Href. exact Hready.
  - exact Hready.
Qed.
```

### A2: `choose_edf_unique_min`

```coq
Lemma choose_edf_unique_min : forall jobs m sched t candidates j,
    In j candidates ->
    ready jobs m sched j t ->
    (forall j', In j' candidates -> ready jobs m sched j' t ->
                j' <> j ->
                job_abs_deadline (jobs j) < job_abs_deadline (jobs j')) ->
    choose_edf jobs m sched t candidates = Some j.
Proof.
  intros jobs m sched t candidates j Hin Hready Hstrict.
  destruct (choose_edf_some_if_exists jobs m sched t candidates) as [j' Hchoose].
  { exists j. split. exact Hin. exact Hready. }
  assert (Hj'_ready : ready jobs m sched j' t).
  { apply (choose_edf_ready jobs m sched t candidates). exact Hchoose. }
  assert (Hj'_in : In j' candidates).
  { unfold choose_edf in Hchoose.
    apply min_dl_job_in in Hchoose.
    apply filter_In in Hchoose. exact (proj1 Hchoose). }
  assert (Hle : job_abs_deadline (jobs j') <= job_abs_deadline (jobs j)).
  { apply (choose_edf_min_deadline jobs m sched t candidates j' Hchoose j Hin Hready). }
  destruct (Nat.eq_dec j' j) as [Heq | Hneq].
  - rewrite Heq in Hchoose. exact Hchoose.
  - exfalso.
    pose proof (Hstrict j' Hj'_in Hj'_ready Hneq) as Hlt.
    lia.
Qed.
```

### C: `UniSchedulerInterface.v` (new file)

Created `/scheduling_theory/UniSchedulerInterface.v` with `Record UniSchedulerSpec` containing 4 fields:
- `choose_ready`
- `choose_min_deadline`
- `choose_some_if_ready`
- `choose_none_if_no_ready`

### C': `edf_scheduler_spec` instantiation

Added to end of `EDF.v`:
```coq
Definition edf_scheduler_spec : UniSchedulerSpec :=
  mkUniSchedulerSpec
    choose_edf
    choose_edf_ready
    choose_edf_min_deadline
    choose_edf_some_if_exists
    choose_edf_none_if_no_ready.
```

Makefile updated with `UniSchedulerInterface.vo` target and `EDF.vo` dependency.

## TODO
(all complete)
