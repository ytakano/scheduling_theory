# Proof Progress: EDFLemmas Section 5

## Status Overview
- Overall: Complete
- Complete Lemmas: 3/3
- Unproven (`Admitted`): none
- Failed/Abandoned Items: none

## Completed Lemmas

### `edf_violation_exposes_exchange_pair` (5-1)

Note: Plan's statement included `J j` hypothesis and `J j'` conclusion, but no
`CandidateSourceSpec` is available to derive `J j'` from mere eligibility.
Implemented simpler provable form (no `J`).

```coq
Lemma edf_violation_exposes_exchange_pair :
  forall jobs sched t j,
    sched t 0 = Some j ->
    edf_violation_at jobs sched t ->
    exists j',
      eligible jobs 1 sched j' t /\
      job_abs_deadline (jobs j') < job_abs_deadline (jobs j).
Proof.
  intros jobs sched t j Hsched Hviol.
  unfold edf_violation_at in Hviol.
  destruct Hviol as [j_run [j' [Hrun [Helig Hlt]]]].
  rewrite Hsched in Hrun.
  injection Hrun as Heq. subst j_run.
  exists j'.
  split. exact Helig. exact Hlt.
Qed.
```

### `matches_choose_edf_at_with_no_earlier_eligible_job` (5-2)

```coq
Lemma matches_choose_edf_at_with_no_earlier_eligible_job :
  forall J candidates_of
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched t j,
    matches_choose_edf_at_with jobs candidates_of sched t ->
    sched t 0 = Some j ->
    forall j',
      J j' ->
      eligible jobs 1 sched j' t ->
      job_abs_deadline (jobs j') < job_abs_deadline (jobs j) ->
      False.
Proof.
  intros J candidates_of cand_spec jobs sched t j Hmatch Hsched j' HJj' Helig Hlt.
  unfold matches_choose_edf_at_with in Hmatch.
  rewrite Hsched in Hmatch.
  assert (Hchoose : choose_edf jobs 1 sched t (candidates_of jobs 1 sched t) = Some j).
  { symmetry. exact Hmatch. }
  assert (Hin : In j' (candidates_of jobs 1 sched t)).
  { destruct cand_spec as [_ Hcomplete _].
    exact (Hcomplete jobs 1 sched t j' HJj' Helig). }
  pose proof (choose_edf_min_deadline jobs 1 sched t _ j Hchoose j' Hin Helig) as Hle.
  lia.
Qed.
```

### `matches_choose_edf_at_with_implies_respects_edf_priority_at_on` (5-3)

```coq
Lemma matches_choose_edf_at_with_implies_respects_edf_priority_at_on :
  forall J candidates_of
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched t,
    matches_choose_edf_at_with jobs candidates_of sched t ->
    respects_edf_priority_at_on J jobs sched t.
Proof.
  intros J candidates_of cand_spec jobs sched t Hmatch.
  unfold respects_edf_priority_at_on.
  intros j j' _ HJj' Hsched Helig Hlt.
  exact (matches_choose_edf_at_with_no_earlier_eligible_job
           J candidates_of cand_spec jobs sched t j Hmatch Hsched j' HJj' Helig Hlt).
Qed.
```

## Proof Attempts & Diagnostics

### Note on 5-1 statement

The plan's statement had `J j` in hypotheses and `J j'` in the conclusion, but without a
`CandidateSourceSpec`, `J j'` cannot be derived from eligibility alone. The simpler form
(without `J`) is what is actually needed: `edf_violation_at` already provides the witness.

## TODO

(all done)
