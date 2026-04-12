# Canonicalization Stabilization Plan

## Generic Core

- `matches_dispatch_at_with`
- `matches_dispatch_before`
- `deadline_horizon`
- `J_implies_deadline_le_horizon`
- `CanonicalRepairSpec`
- `DispatchAgreesBefore`
- `repair_pushes_forward_generic`
- `normalize_to_canonical_generic`
- `finite_J_restricted_schedule`
- `finite_normalized_schedule`
- `finite_truncated_schedule`
- `finite_canonical_schedule_yields_scheduler_rel`
- `finite_optimality_via_normalization`

## Policy-Specific

- EDF:
  - `is_canonical_at_b_*`
  - `edf_canonical_at_dec`
  - `repair_non_canonical_at`
  - `edf_dispatch_agrees_before`
  - `EDFCanonicalRepairSpec`
- LLF:
  - `is_llf_canonical_at_b_*`
  - `llf_canonical_at_dec`
  - `repair_non_canonical_at_llf`
  - `llf_dispatch_agrees_before`
  - `LLFCanonicalRepairSpec`

## Wrapper-Only

- `edf_normalize_to_canonical`
- `llf_normalize_to_canonical`
- `edf_optimality_on_finite_jobs`
- `llf_optimality_on_finite_jobs`

These wrappers are intentionally thin. Their role is not to introduce new
policy-specific proof structure, but to expose a uniform policy-facing API on
top of the shared canonicalization and optimality skeletons.

## Required ingredients for a new uniprocessor policy

1. A generic scheduling-algorithm instance:
   - `x_generic_spec : GenericSchedulingAlgorithm`

2. A policy-facing canonical-at predicate, or a direct alias to
   `matches_dispatch_at_with`.

3. A constructive decider for canonicality at a single time point:
   - `x_canonical_at_dec`

4. A local one-step repair lemma:
   - repairs non-canonicality at time `t`
   - preserves validity
   - preserves feasibility on the target job set
   - preserves the J-only invariant
   - preserves the single-CPU shape invariant
   - preserves agreement before `t`

5. A dispatcher prefix-agreement lemma:
   - `x_dispatch_agrees_before : DispatchAgreesBefore ...`

6. A packaged repair specification:
   - `XCanonicalRepairSpec : CanonicalRepairSpec ...`

7. A policy-specific normalization wrapper:
   - `x_normalize_to_canonical`

8. A policy-specific finite optimality wrapper:
   - `x_optimality_on_finite_jobs`

## Typical file placement

- Policy definition / chooser:
  policy file such as `EDF.v`, `LLF.v`, or a future policy-specific file.
- Local repair lemma:
  policy transform file such as `*Transform.v`.
- Prefix-agreement lemma:
  policy lemmas file such as `*Lemmas.v`.
- Canonical repair packaging, normalization wrapper, and optimality wrapper:
  policy optimality file such as `*Optimality.v`.

## What is already generic

The following pieces should not be reproved for each policy:

- finite-horizon normalization recursion
- propagation from one repaired time step to the next prefix
- truncation at the deadline horizon
- conversion from canonical finite schedules to `scheduler_rel`
- the final finite optimality theorem
