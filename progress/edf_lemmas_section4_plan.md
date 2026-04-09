# Proof Plan: EDFLemmas Section 4

## Goal

Implement Section 4 of `plan/edf_lemmas.md` in `theories/UniPolicies/EDFLemmas.v`.

Section 4 defines:
- `matches_choose_edf_at` (4-1)
- `matches_choose_edf_at_with` (4-1b)
- `matches_choose_edf_before` (4-2)
- `respects_edf_priority_at` (4-3)
- `respects_edf_priority_at_on` (4-3b)
- `edf_violation_at` (4-4)

And proves:
- `canonical_non_edf_step_has_other_min_or_better_eligible_job` (4-5, constructive)
- `exists_first_edf_violation_before` (4-6, classical)

## Proof Strategy

### Definitions (4-1 to 4-4)
All are direct transcriptions from the plan. Need to add `Classical` to imports for lemma 4-6.

### Lemma 4-5 (constructive)

```
valid_schedule + sched t 0 = Some j
  => valid_running_implies_eligible (c=0, c<1)
  => eligible jobs 1 sched j t

J j + eligible ... j t + cand_spec.candidates_complete
  => In j (candidates_of jobs 1 sched t)

In j candidates + eligible ... j t
  => choose_edf_some_if_exists => Some j'

choose_edf_in_candidates => In j' candidates
choose_edf_eligible => eligible ... j' t
choose_edf_min_deadline(j, Hin_j, Helig_j) => dl j' <= dl j

choose_edf ... = Some j' AND sched t 0 = Some j AND ~ matches
  => if j' = j then sched t 0 = choose_edf ... (contradiction)
  => j' <> j
```

### Lemma 4-6 (classical)

Use `well_founded_induction` on the witness `t`:
- `classic` on `exists t', t' < t /\ edf_violation_at jobs sched t'`
- If yes: apply IH to `t'`
- If no: `t` is the minimum, return it directly

Need `From Stdlib Require Import ... Classical` (or `Classical_Prop`).

## Proposed Lemmas

- [ ] Definitions 4-1 to 4-4 (add to EDFLemmas.v)
- [ ] `canonical_non_edf_step_has_other_min_or_better_eligible_job` (4-5)
- [ ] `exists_first_edf_violation_before` (4-6)

## Proof Order

1. Add definitions 4-1 to 4-4 + import Classical
2. `canonical_non_edf_step_has_other_min_or_better_eligible_job` (4-5)
3. `exists_first_edf_violation_before` (4-6)
