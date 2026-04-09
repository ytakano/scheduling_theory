# Proof Plan: Partitioned Scheduling (Lv.5)

## Goal

1. Refactor `UniSchedulerInterface.v`: replace `UniSchedulerSpec` with `GenericSchedulerDecisionSpec` (4 fields, no `choose_min_deadline`)
2. Refactor `UniSchedulerLemmas.v`: use `GenericSchedulerDecisionSpec`; remove EDF-specific lemmas A5/C1/C2
3. Refactor `EDF.v`: add `EDFSchedulerSpec` (with `choose_min_deadline`); move A5/C1/C2 here
4. Create `Partitioned.v` with 3 core theorems (Lv.5)

## Proof Strategy

### Phase A: Interface Refactoring (Steps 1–3)

Purely syntactic + type-level changes. Verify each file compiles after each step.

### Phase B: `Partitioned.v` Helper Lemmas

Build from simple to complex:
- `candidates_for_assign_sound`: filter property
- `non_assigned_cpu_zero`: contraposition of `respects_assignment`
- `partitioned_implies_sequential`: uniqueness from `respects_assignment`
- `cpu_count_assigned_only`: induction on m, using `non_assigned_cpu_zero`
- `service_decomposition_step`: bridge `cpu_count m` to `cpu_count 1`

### Phase C: Core Theorems

Prove in this order (Theorem 3 must come first):
1. `service_decomposition` (induction on t)
2. `completed_iff_on_assigned_cpu` (corollary of above)
3. `assignment_respect` (unfold)
4. `local_to_global_validity` (assembly of 2 + 3 + per-CPU validity)

## Proposed Lemmas

### Phase A (refactoring)
- [x] `UniSchedulerInterface.v`: `GenericSchedulerDecisionSpec` record
- [ ] `UniSchedulerLemmas.v`: updated to `GenericSchedulerDecisionSpec`
- [ ] `EDF.v`: `EDFSchedulerSpec` + `edf_scheduler_spec : EDFSchedulerSpec`

### Phase B (Partitioned.v helpers)
- [ ] `candidates_for_assign_sound`
- [ ] `non_assigned_cpu_zero`
- [ ] `partitioned_implies_sequential`
- [ ] `cpu_count_assigned_only`
- [ ] `service_decomposition_step`

### Phase C (core theorems)
- [ ] `service_decomposition`
- [ ] `completed_iff_on_assigned_cpu`
- [ ] `assignment_respect`
- [ ] `local_to_global_validity`

## Proof Order

1. Refactor UniSchedulerInterface.v
2. Refactor UniSchedulerLemmas.v
3. Refactor EDF.v
4. Create Partitioned.v skeleton (definitions only)
5. `candidates_for_assign_sound`
6. `non_assigned_cpu_zero`
7. `partitioned_implies_sequential`
8. `cpu_count_assigned_only`
9. `service_decomposition_step`
10. `service_decomposition`
11. `completed_iff_on_assigned_cpu`
12. `assignment_respect`
13. `local_to_global_validity`
