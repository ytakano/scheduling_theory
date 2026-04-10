# Proof Plan: EDF Optimality Phase 9 — `edf_optimality_on_finite_jobs`

## Goal

Prove the final EDF optimality theorem for finite job sets:

```coq
Theorem edf_optimality_on_finite_jobs :
  forall J (J_bool : JobId -> bool) enumJ (candidates_of : CandidateSource)
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs,
    (forall x, J_bool x = true <-> J x) ->
    (forall j, J j -> In j enumJ) ->
    (forall j, In j enumJ -> J j) ->
    feasible_on J jobs 1 ->
    schedulable_by_on J (edf_scheduler candidates_of) jobs 1.
```

File: `theories/UniPolicies/EDFOptimality.v`

## Proof Strategy

Phase 8 produced `edf_normalize_up_to` (no violations before H), but the plan
requires `matches_choose_edf_before H`. We need to:
1. Close the gap: "no violations" → `matches_choose_edf_before H`
2. Bridge: `matches_choose_edf_before H` + idle after H → `scheduler_rel`
3. Combine to get `schedulable_by_on`

### Gap Analysis

`edf_normalize_up_to` handles strict EDF violations (sched t 0 = Some j with J j,
exists j' in J with eligible+smaller deadline). Cases NOT handled:
- (A) `sched t 0 = None` and `choose_edf = Some j'` (idle-when-should-run)
- (B) `sched t 0 = Some j` (j ∉ J) and `choose_edf ≠ sched t 0`
- (C) `sched t 0 = Some j` (j ∈ J) and `choose_edf = Some j'` with equal deadline

### Approach

**Step 1**: Restrict schedule to J-only jobs (validity+feasibility preserved).
**Step 2**: Apply `edf_normalize_up_to` to eliminate strict violations.
**Step 3**: Apply additional repair for case (A) (idle→running swap) and case (C) (tie-breaking).
**Step 4**: Truncate to H (make idle at t ≥ H).
**Step 5**: Bridge to `scheduler_rel`.
**Step 6**: Apply `single_cpu_dispatch_schedulable_by_on_intro`.

## Proposed Lemmas

### Service lemmas for None-to-Some swap (None at t1, Some j2 at t2)
- [x] `swap_at_service_j2_front_before_t2_none`: when sched t1 0 = None, service of j2 in swap increases by 1 in (t1, t2]
- [x] `swap_at_service_j2_after_t2_none`: when sched t1 0 = None, service of j2 unchanged after t2

### Validity/feasibility for None-to-Some swap
- [x] `swap_at_valid_new_front_job_none`: j2 eligible at t1 in swap_at when sched t1 0 = None
- [x] `swap_at_preserves_valid_schedule_none`: valid_schedule preserved when sched t1 0 = None, sched t2 0 = Some j2, eligible j2 t1, t1 < t2
- [x] `swap_at_preserves_feasible_schedule_on_none`: feasible_schedule_on J preserved

### J-restriction
- [x] `restrict_to_J_jobs`: define and prove valid+feasible for J-only schedule

### Stronger normalization
- [x] `edf_normalize_to_canonical`: produces `matches_choose_edf_before H` (induction, using repair for all non-canonical cases)

### Truncation
- [x] `truncate_schedule`: define and prove validity, feasibility, canonical preservation

### Bridge
- [x] `matches_choose_edf_before_implies_scheduler_rel`: bridge to scheduler_rel
- [x] `edf_optimality_on_finite_jobs`: main theorem

## Proof Order
1. `swap_at_service_j2_front_before_t2_none`
2. `swap_at_service_j2_after_t2_none`
3. `swap_at_valid_new_front_job_none`
4. `swap_at_preserves_valid_schedule_none`
5. `swap_at_preserves_feasible_schedule_on_none`
6. `restrict_to_J_jobs`
7. `edf_normalize_to_canonical`
8. `truncate_schedule` (definition + lemmas)
9. `matches_choose_edf_before_implies_scheduler_rel`
10. `edf_optimality_on_finite_jobs`
