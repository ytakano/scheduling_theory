# Proof Progress: EDF Optimality Phase 8 — edf_normalize_up_to

## Status Overview
- Overall: Complete
- Complete Lemmas: 2/2
- Unproven (`Admitted`): none
- Failed/Abandoned Items: none

## Completed Lemmas

### Lemma 19: `repair_pushes_first_violation_forward`
```coq
Lemma repair_pushes_first_violation_forward :
  forall J (candidates_of : CandidateSource)
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched sched' t0,
    agrees_before sched sched' t0 ->
    matches_choose_edf_at_with jobs candidates_of sched' t0 ->
    (forall t, t < t0 -> ~ edf_violation_at_with J candidates_of jobs sched t) ->
    forall t, t <= t0 -> ~ edf_violation_at_with J candidates_of jobs sched' t.
```
Key: split on t < t0 vs t = t0.
- t < t0: transfer violation sched' → sched via agrees_before_weaken + sym +
  candidates_of_agrees_before + agrees_before_eligible (proj1 direction).
  Use `rewrite (Hagree t 0 Hlt)` (not `<-`) to convert `sched t 0 = sched' t 0`
  in goal `sched t 0 = Some j` → `sched' t 0 = Some j = Hrun'`.
- t = t0: matches_choose_edf_at_with_no_finite_violation.

### Lemma 20: `edf_normalize_up_to`
```coq
Lemma edf_normalize_up_to :
  forall J (J_bool : JobId -> bool) (candidates_of : CandidateSource)
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched H,
    (forall x, J_bool x = true <-> J x) ->
    valid_schedule jobs 1 sched ->
    feasible_schedule_on J jobs 1 sched ->
    exists sched',
      valid_schedule jobs 1 sched' /\
      feasible_schedule_on J jobs 1 sched' /\
      (forall t, t < H -> ~ edf_violation_at_with J candidates_of jobs sched' t).
```
Key: induction on H.
- H = 0: trivial.
- H = S H': IH + edf_violationb_at_with bool check.
  - false: sched_ih suffices (no violations before S H').
  - true: extract j, apply repair_first_violation (t0=H', H=S H'),
    then repair_pushes_first_violation_forward gives no violation at t ≤ H'.

## Proof Attempts & Diagnostics

### Compilation Error 1 (repair_pushes_first_violation_forward)
- Error: "Found no subterm matching 'sched' t 0'" at `rewrite <- (Hagree t 0 Hlt)`.
- Diagnosis: Goal was `sched t 0 = Some j`. `Hagree t 0 Hlt : sched t 0 = sched' t 0`.
  Using `<-` tries to replace `sched' t 0` in goal but it's not there.
- Fix: Use `rewrite (Hagree t 0 Hlt)` (forward) to replace `sched t 0` with `sched' t 0`,
  making goal `sched' t 0 = Some j = Hrun'`.

### Compilation Error 2 (repair_pushes_first_violation_forward)
- Error: `Helig' : eligible sched' j' t` but expected `eligible sched j' t`.
- Diagnosis: Used `proj2` instead of `proj1` for agrees_before_eligible.
  `agrees_before_eligible sched' sched t : eligible sched' j' t <-> eligible sched j' t`.
  `proj1` goes from `eligible sched' j' t` → `eligible sched j' t`. ✓
- Fix: Replace `proj2` with `proj1`.

## TODO
(none — all complete)
