# Proof Plan: EDF Optimality Phase 8 — edf_normalize_up_to

## Goal

Prove two lemmas in `theories/UniPolicies/EDFTransform.v`:

**Lemma 19** `repair_pushes_first_violation_forward`: Given
- `agrees_before sched sched' t0`
- `matches_choose_edf_at_with jobs candidates_of sched' t0`
- `forall t, t < t0 -> ~ edf_violation_at_with J candidates_of jobs sched t`

Conclude: `forall t, t <= t0 -> ~ edf_violation_at_with J candidates_of jobs sched' t`.

**Lemma 20** `edf_normalize_up_to`: Given valid+feasible sched, produce sched' valid+feasible
with no EDF violations before H. By induction on H.

## Proof Strategy

### Lemma 19

Split on t < t0 vs t = t0.
- t < t0: transfer violation sched' → sched through agrees_before_weaken + agrees_before_sym,
  candidates_of_agrees_before, agrees_before_eligible. Contradiction.
- t = t0: matches_choose_edf_at_with_no_finite_violation.

### Lemma 20

Induction on H.
- H = 0: trivial (vacuously no violations).
- H = S H':
  1. Apply IH → sched_ih valid+feasible+no-violation-before-H'.
  2. Decide `edf_violationb_at_with J_bool candidates_of jobs sched_ih H'`.
  3. false: use sched_ih directly.
  4. true: convert to Prop, extract j, apply repair_first_violation (t0=H', H=S H'),
     then repair_pushes_first_violation_forward.

## Proposed Lemmas

- [ ] `repair_pushes_first_violation_forward` (Lemma 19)
- [ ] `edf_normalize_up_to` (Lemma 20)

## Proof Order

1. `repair_pushes_first_violation_forward`
2. `edf_normalize_up_to`
