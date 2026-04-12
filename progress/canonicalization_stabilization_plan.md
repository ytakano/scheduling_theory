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

## New Policy Checklist

- Provide `x_generic_spec : GenericSchedulingAlgorithm`.
- Define the policy-specific canonical-at predicate or alias.
- Prove a constructive canonical decider.
- Prove a local repair lemma for one non-canonical step.
- Prove `DispatchAgreesBefore` for the policy.
- Build `XCanonicalRepairSpec`.
- Instantiate `finite_optimality_via_normalization`.
