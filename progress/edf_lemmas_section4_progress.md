# Proof Progress: EDFLemmas Section 4

## Status Overview
- Overall: Complete
- Complete Lemmas: 2/2 (+ 6 definitions)
- Unproven (`Admitted`): none
- Failed/Abandoned Items: none

## Completed Definitions

- `matches_choose_edf_at` (4-1): `sched t 0 = choose_edf jobs 1 sched t candidates`
- `matches_choose_edf_at_with` (4-1b): `sched t 0 = choose_edf jobs 1 sched t (candidates_of jobs 1 sched t)`
- `matches_choose_edf_before` (4-2): `forall t, t < H -> matches_choose_edf_at_with ...`
- `respects_edf_priority_at` (4-3): no earlier-deadline eligible job ignored
- `respects_edf_priority_at_on` (4-3b): same with explicit `J`
- `edf_violation_at` (4-4): `exists j j', sched t 0 = Some j /\ eligible ... j' /\ dl j' < dl j`

## Completed Lemmas

### `canonical_non_edf_step_has_other_min_or_better_eligible_job` (4-5)

```coq
Lemma canonical_non_edf_step_has_other_min_or_better_eligible_job :
  forall J candidates_of
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched t j,
    valid_schedule jobs 1 sched ->
    sched t 0 = Some j ->
    J j ->
    ~ matches_choose_edf_at_with jobs candidates_of sched t ->
    exists j',
      In j' (candidates_of jobs 1 sched t) /\
      eligible jobs 1 sched j' t /\
      job_abs_deadline (jobs j') <= job_abs_deadline (jobs j) /\
      j' <> j.
Proof.
  intros J candidates_of cand_spec jobs sched t j Hvalid Hsched HJj Hnot.
  assert (Helig_j : eligible jobs 1 sched j t).
  { apply (valid_running_implies_eligible jobs 1 sched j t 0).
    - exact Hvalid.
    - lia.
    - exact Hsched. }
  assert (Hin_j : In j (candidates_of jobs 1 sched t)).
  { destruct cand_spec as [_ Hcomplete _].
    exact (Hcomplete jobs 1 sched t j HJj Helig_j). }
  destruct (choose_edf_some_if_exists jobs 1 sched t (candidates_of jobs 1 sched t))
      as [j' Hchoose].
  { exists j. split. exact Hin_j. exact Helig_j. }
  assert (Hj'_in : In j' (candidates_of jobs 1 sched t)).
  { exact (choose_edf_in_candidates jobs 1 sched t _ j' Hchoose). }
  assert (Hj'_elig : eligible jobs 1 sched j' t).
  { exact (choose_edf_eligible jobs 1 sched t _ j' Hchoose). }
  assert (Hj'_le : job_abs_deadline (jobs j') <= job_abs_deadline (jobs j)).
  { exact (choose_edf_min_deadline jobs 1 sched t _ j' Hchoose j Hin_j Helig_j). }
  assert (Hneq : j' <> j).
  { intro Heq. subst j'.
    apply Hnot. unfold matches_choose_edf_at_with.
    rewrite Hsched. symmetry. exact Hchoose. }
  exists j'.
  split. exact Hj'_in.
  split. exact Hj'_elig.
  split. exact Hj'_le.
  exact Hneq.
Qed.
```

### `exists_first_edf_violation_before` (4-6)

```coq
Lemma exists_first_edf_violation_before :
  forall jobs sched H,
    (exists t, t < H /\ edf_violation_at jobs sched t) ->
    exists t0,
      t0 < H /\
      edf_violation_at jobs sched t0 /\
      (forall t, t < t0 -> ~ edf_violation_at jobs sched t).
Proof.
  intros jobs sched H [t [HtH Hviol]].
  revert H HtH.
  induction t as [t IH] using (well_founded_induction lt_wf).
  intros H HtH.
  destruct (classic (exists t', t' < t /\ edf_violation_at jobs sched t'))
      as [[t' [Hlt' Hviol']] | Hmin].
  - exact (IH t' Hlt' Hviol' H (Nat.lt_trans _ _ _ Hlt' HtH)).
  - exists t.
    split. exact HtH.
    split. exact Hviol.
    intros t' Hlt' Hviol'.
    apply Hmin. exists t'. split. exact Hlt'. exact Hviol'.
Qed.
```

## Proof Attempts & Diagnostics

### Initial compile error in 4-5

- Error: "The term 'Hchoose' has type `choose_edf ... = Some j'` while expected `Some j' = ...`"
- Fix: use `subst j'` + `symmetry` before `exact Hchoose`.

### Initial compile error in 4-6

- Error: "The term 'H' has type 'nat' while expected 'edf_violation_at ...'"
- Cause: `well_founded_induction` generalizes `Hviol` into IH because it depends on `t`.
  So IH has signature `forall y, y < t -> edf_violation_at ... y -> forall H, y < H -> ...`.
- Fix: pass `Hviol'` before `H`: `IH t' Hlt' Hviol' H (Nat.lt_trans _ _ _ Hlt' HtH)`.

## TODO

(all done — Section 5 is next)
