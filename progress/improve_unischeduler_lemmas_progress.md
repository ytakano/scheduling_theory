# Proof Progress: Improve UniSchedulerLemmas

## Status Overview
- Overall: Complete
- Complete Lemmas: 11/11
- Unproven (`Admitted`): none
- Failed/Abandoned Items: none

## Completed Lemmas

### `ready_implies_released` (Schedule.v)

```coq
Lemma ready_implies_released : forall jobs m sched j t,
    ready jobs m sched j t -> released jobs j t.
Proof.
  unfold ready, waiting.
  intros jobs m sched j t Hr. exact (proj1 Hr).
Qed.
```

### `ready_implies_not_completed` (Schedule.v)

```coq
Lemma ready_implies_not_completed : forall jobs m sched j t,
    ready jobs m sched j t -> ~completed jobs m sched j t.
Proof.
  unfold ready, waiting.
  intros jobs m sched j t Hr. exact (proj2 Hr).
Qed.
```

### `choose_in_candidates` field (UniSchedulerInterface.v)

Added as Spec 5 field to `UniSchedulerSpec` record:
```coq
choose_in_candidates :
  forall jobs m sched t candidates j,
    choose jobs m sched t candidates = Some j ->
    In j candidates ;
```

### `choose_edf_in_candidates` (EDF.v)

```coq
Lemma choose_edf_in_candidates : forall jobs m sched t candidates j,
    choose_edf jobs m sched t candidates = Some j -> In j candidates.
Proof.
  intros jobs m sched t candidates j Hchoose.
  unfold choose_edf in Hchoose.
  apply min_dl_job_in in Hchoose.
  apply filter_In in Hchoose.
  exact (proj1 Hchoose).
Qed.
```

`edf_scheduler_spec` extended to include `choose_edf_in_candidates` as 6th argument.

### `candidates_sound` / `candidates_complete` definitions (UniSchedulerLemmas.v)

```coq
Definition candidates_sound (jobs : JobId -> Job) (m : nat) (sched : Schedule)
    (t : Time) (candidates : list JobId) : Prop :=
  forall j, In j candidates -> ready jobs m sched j t.

Definition candidates_complete (jobs : JobId -> Job) (m : nat) (sched : Schedule)
    (t : Time) (candidates : list JobId) : Prop :=
  forall j, ready jobs m sched j t -> In j candidates.
```

### `choose_some_implies_in_candidates` (E1, UniSchedulerLemmas.v)

```coq
Lemma choose_some_implies_in_candidates :
    forall j,
      spec.(choose) jobs m sched t candidates = Some j ->
      In j candidates.
Proof.
  intros j H.
  exact (spec.(choose_in_candidates) jobs m sched t candidates j H).
Qed.
```

### `exists_ready_candidate_implies_not_none` (E2, UniSchedulerLemmas.v)

```coq
Lemma exists_ready_candidate_implies_not_none :
    (exists j, In j candidates /\ ready jobs m sched j t) ->
    spec.(choose) jobs m sched t candidates <> None.
Proof.
  intros Hex Hnone.
  destruct (ready_exists_implies_choose_some Hex) as [j' Hj'].
  rewrite Hnone in Hj'. discriminate.
Qed.
```

### `choose_none_implies_each_candidate_unreleased_or_completed` (E3, UniSchedulerLemmas.v)

```coq
Lemma choose_none_implies_each_candidate_unreleased_or_completed :
    spec.(choose) jobs m sched t candidates = None ->
    forall j, In j candidates ->
      ~released jobs j t \/ completed jobs m sched j t.
Proof.
  intros Hnone j Hin.
  pose proof (choose_none_implies_no_ready Hnone j Hin) as Hnready.
  unfold ready, pending in Hnready.
  destruct (classic (released jobs j t)) as [Hrel | Hnrel].
  - right. apply NNPP. intro Hnc. apply Hnready. split; assumption.
  - left. exact Hnrel.
Qed.
```
Note: Requires `From Stdlib Require Import Classical.`

### `choose_some_under_sound_candidates` (F3, UniSchedulerLemmas.v)

```coq
Lemma choose_some_under_sound_candidates :
    candidates_sound jobs m sched t candidates ->
    forall j,
      spec.(choose) jobs m sched t candidates = Some j ->
      In j candidates /\ ready jobs m sched j t.
Proof.
  intros Hsound j Hchoose.
  split.
  - exact (choose_some_implies_in_candidates j Hchoose).
  - exact (choose_some_implies_ready j Hchoose).
Qed.
```

### `choose_some_if_any_ready_under_complete_candidates` (F4, UniSchedulerLemmas.v)

```coq
Lemma choose_some_if_any_ready_under_complete_candidates :
    candidates_complete jobs m sched t candidates ->
    (exists j, ready jobs m sched j t) ->
    exists j', spec.(choose) jobs m sched t candidates = Some j'.
Proof.
  intros Hcomplete [j Hready].
  apply ready_exists_implies_choose_some.
  exists j. split.
  - apply Hcomplete. exact Hready.
  - exact Hready.
Qed.
```

## Proof Attempts & Diagnostics

All lemmas compiled successfully on first attempt.

## TODO

(all done)
