# Proof Progress: EDF Optimality Phase 7 — repair_first_violation

## Status Overview
- Overall: Complete
- Complete Lemmas: 2/2
- Unproven (`Admitted`): none
- Failed/Abandoned Items: none

## Completed Lemmas

### Lemma 18': `first_violation_yields_canonical_repair_job`
```coq
Lemma first_violation_yields_canonical_repair_job :
  forall J (candidates_of : CandidateSource)
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched t j,
    valid_schedule jobs 1 sched ->
    sched t 0 = Some j ->
    J j ->
    edf_violation_at_with J candidates_of jobs sched t ->
    exists j',
      In j' (candidates_of jobs 1 sched t) /\
      eligible jobs 1 sched j' t /\
      job_abs_deadline (jobs j') < job_abs_deadline (jobs j) /\
      j' <> j /\
      choose_edf jobs 1 sched t (candidates_of jobs 1 sched t) = Some j'.
```
Key: violation gives j_viol with In+eligible+strict<. `choose_edf_min_deadline` gives
`deadline(j') <= deadline(j_viol)`, so `deadline(j') < deadline(j)`. `j' ≠ j` by strict deadline gap.

### Lemma 18: `repair_first_violation`
```coq
Lemma repair_first_violation :
  forall J (J_bool : JobId -> bool) (candidates_of : CandidateSource)
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched (H : nat) t0 j,
    (forall x, J_bool x = true <-> J x) ->
    valid_schedule jobs 1 sched ->
    feasible_schedule_on J jobs 1 sched ->
    t0 < H ->
    sched t0 0 = Some j ->
    edf_violation_at_with J candidates_of jobs sched t0 ->
    (forall t, t < t0 -> ~ edf_violation_at_with J candidates_of jobs sched t) ->
    exists sched',
      valid_schedule jobs 1 sched' /\
      feasible_schedule_on J jobs 1 sched' /\
      agrees_before sched sched' t0 /\
      matches_choose_edf_at_with jobs candidates_of sched' t0.
```
Construction: j' = choose_edf result, t' = time j' runs, sched' = swap_at sched t0 t'.
Valid/feasible from Phases 5-6 lemmas. agrees_before from swap_at_same_outside.
matches_choose_edf_at_with: swap_at_t1 + candidates_of_agrees_before + choose_edf_agrees_before.

## Proof Attempts & Diagnostics

### Compilation Error 1 (repair_first_violation)
- Error: "No such goal. Focus next goal with bullet -." (line 972)
- Diagnosis: Interleaved `split.` and `-` bullets: after `- exact ...` closes first goal,
  the next `split.` at the same indentation level was seen as inside the bullet scope.
- Fix: Replace `split. - ... split. - ... split. - ... - ...` with `refine (conj _ (conj _ (conj _ _))).`
  followed by four `-` bullets.

### Compilation Error 2 (repair_first_violation)
- Error: Hchoose has type `choose_edf ... = Some j'` but expected `Some j' = choose_edf ...`.
- Diagnosis: After `rewrite swap_at_t1; rewrite Ht'_run`, the LHS becomes `Some j'` and
  after the two `rewrite` steps the RHS becomes `choose_edf ... = Some j'` — reversed direction.
- Fix: Use `exact (eq_sym Hchoose)` instead of `exact Hchoose`.

## TODO
(none — all complete)
