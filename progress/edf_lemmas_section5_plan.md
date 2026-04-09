# Proof Plan: EDFLemmas Section 5

## Goal

Implement Section 5 ("最適性定理への橋渡し補題") of `theories/UniPolicies/EDFLemmas.v`.

Three lemmas from `plan/edf_lemmas.md` § Section 5:

1. `edf_violation_exposes_exchange_pair` (5-1)
2. `matches_choose_edf_at_with_no_earlier_eligible_job` (5-2)
3. `matches_choose_edf_at_with_implies_respects_edf_priority_at_on` (5-3)

## Proof Strategy

### 5-1: `edf_violation_exposes_exchange_pair`

Note: The plan statement includes `J j` hypothesis and `J j'` conclusion, but there is no
`CandidateSourceSpec` from which to derive `J j'` for an arbitrary eligible job.
Decision: implement without `J` entirely — drop J from both hypothesis and conclusion.
The essential content is: `edf_violation_at` + `sched t 0 = Some j` → exists j' eligible with earlier deadline.

Proof flow:
- Unfold `edf_violation_at`: `exists j_run j', sched t 0 = Some j_run /\ eligible ... j' /\ dl j' < dl j_run`
- From `sched t 0 = Some j`, use `injection` + `subst` to get `j_run = j`
- Return `j'` as witness

### 5-2: `matches_choose_edf_at_with_no_earlier_eligible_job`

Uses `CandidateSourceSpec J candidates_of`.

Proof flow:
- `matches_choose_edf_at_with` + `sched t 0 = Some j` → `choose_edf ... = Some j`
- `cand_spec.(candidates_complete)` + `J j'` + `eligible j' t` → `In j' (candidates_of ...)`
- `choose_edf_min_deadline` → `dl j <= dl j'`
- Contradicts `dl j' < dl j` via `lia`

### 5-3: `matches_choose_edf_at_with_implies_respects_edf_priority_at_on`

Directly calls 5-2.

Proof flow:
- Unfold `respects_edf_priority_at_on`
- Apply `matches_choose_edf_at_with_no_earlier_eligible_job`

## Proposed Lemmas

- [ ] `edf_violation_exposes_exchange_pair`
- [ ] `matches_choose_edf_at_with_no_earlier_eligible_job`
- [ ] `matches_choose_edf_at_with_implies_respects_edf_priority_at_on`

## Proof Order

1. `edf_violation_exposes_exchange_pair`
2. `matches_choose_edf_at_with_no_earlier_eligible_job`
3. `matches_choose_edf_at_with_implies_respects_edf_priority_at_on`
