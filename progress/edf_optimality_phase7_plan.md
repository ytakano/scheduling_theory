# Proof Plan: EDF Optimality Phase 7 — repair_first_violation

## Goal

Prove two lemmas in `theories/UniPolicies/EDFTransform.v`:

**Lemma 18'** `first_violation_yields_canonical_repair_job`: Given valid_schedule,
`sched t 0 = Some j`, `J j`, and `edf_violation_at_with`, extract canonical `j'`
(choose_edf result) with: `In j' cands`, `eligible j' t`, `deadline(j') < deadline(j)` (strict),
`j' ≠ j`, `choose_edf = Some j'`.

**Lemma 18** `repair_first_violation`: Given valid+feasible `sched` with EDF violation at `t0`,
produce `sched' = swap_at sched t0 t'` satisfying:
- `valid_schedule sched'`
- `feasible_schedule_on J sched'`
- `agrees_before sched sched' t0`
- `matches_choose_edf_at_with jobs candidates_of sched' t0`

## Proof Strategy

### Lemma 18'

1. From violation: extract `j_viol` with `In j_viol cands`, `eligible j_viol t`, `deadline(j_viol) < deadline(j)`.
2. `choose_edf_some_if_exists` → get `j'` = choose_edf result (j_viol is eligible + in cands).
3. `choose_edf_min_deadline` → `deadline(j') <= deadline(j_viol) < deadline(j)` → strict.
4. `j' ≠ j` from `deadline(j') < deadline(j)`.
5. Return `j'` with all properties.

### Lemma 18

1. Extract `J j` from violation definition.
2. Apply Lemma 18' → canonical `j'` with all properties.
3. `candidates_sound cand_spec` → `J j'`.
4. `eligible_feasible_implies_runs_later_before_deadline` → `t'` with `t0 ≤ t'`, `t' < deadline(j')`, `sched t' 0 = Some j'`.
5. `sched' = swap_at sched t0 t'`.
6. **validity**: `swap_at_preserves_valid_schedule`.
7. **feasibility**: `swap_at_preserves_feasible_schedule_on`.
8. **agrees_before**: `swap_at_same_outside` (for `u < t0`: `u ≠ t0` and `u ≠ t'`).
9. **matches_choose_edf**: `swap_at_t1` + `candidates_of_agrees_before` + `choose_edf_agrees_before`.

## Proposed Lemmas

- [ ] `first_violation_yields_canonical_repair_job` (Lemma 18')
- [ ] `repair_first_violation` (Lemma 18)

## Proof Order

1. `first_violation_yields_canonical_repair_job`
2. `repair_first_violation`
