# Proof Plan: Laxity / LLF Implementation

## Goal

Add `remaining_cost`, `laxity`, and the LLF (Least Laxity First) scheduling policy to the Rocq scheduling formalization, following the pattern of existing EDF/FIFO/RR policies.

## Proof Strategy

Phased implementation:
1. **Phase A**: Add definitions `remaining_cost : nat` and `laxity : Z` to `ScheduleModel.v`
2. **Phase B**: Add basic lemmas to `ScheduleLemmas/ScheduleFacts.v`
3. **Phase C**: Create generic `MetricChooser.v`
4. **Phase D**: Create `UniPolicies/Laxity.v` with full LLF policy
5. **Phase E**: Create `PartitionedPolicies/PartitionedLLF.v`
6. **Phase F**: Update `_CoqProject` and regenerate Makefile

## Proof Style
- [x] Constructive (preferred)
- [ ] Classical (must justify below)

## Proposed Lemmas

### Phase A: ScheduleModel.v definitions
- [ ] `remaining_cost`: `job_cost (jobs j) - service_job m sched j t`
- [ ] `laxity`: `Z.of_nat deadline - Z.of_nat t - Z.of_nat remaining_cost`

### Phase B: ScheduleFacts.v lemmas
- [ ] `remaining_cost_le_cost`
- [ ] `completed_implies_remaining_cost_zero`
- [ ] `remaining_cost_zero_implies_completed`
- [ ] `not_completed_implies_remaining_cost_pos`
- [ ] `service_job_step_uni`
- [ ] `remaining_cost_step_running_uni`
- [ ] `remaining_cost_step_not_running_uni`
- [ ] `laxity_unfold`
- [ ] `completed_implies_laxity_deadline_minus_now`
- [ ] `laxity_step_running_uni`
- [ ] `laxity_step_not_running_uni`

### Phase C: MetricChooser.v
- [ ] `min_metric_job` (Fixpoint)
- [ ] `choose_min_metric`
- [ ] `min_metric_job_none_iff`
- [ ] `min_metric_job_in`
- [ ] `min_metric_job_min`
- [ ] `choose_min_metric_eligible`
- [ ] `choose_min_metric_none_if_no_eligible`
- [ ] `choose_min_metric_some_if_exists`
- [ ] `choose_min_metric_in_candidates`

### Phase D: Laxity.v
- [ ] `llf_metric`
- [ ] `choose_llf`
- [ ] `llf_generic_spec`
- [ ] `choose_llf_min_laxity`
- [ ] `llf_policy`
- [ ] `llf_policy_sane`
- [ ] `choose_llf_refines_llf_policy`
- [ ] `llf_bundle`
- [ ] `llf_scheduler_on`

### Phase E: PartitionedLLF.v
- [ ] `partitioned_llf_scheduler`
- [ ] `local_llf_witnesses_imply_partitioned_llf_schedulable_by_on`

## Proof Order

1. remaining_cost (definition)
2. laxity (definition)
3. remaining_cost_le_cost
4. completed_implies_remaining_cost_zero
5. remaining_cost_zero_implies_completed
6. not_completed_implies_remaining_cost_pos
7. service_job_step_uni
8. remaining_cost_step_running_uni
9. remaining_cost_step_not_running_uni
10. laxity_unfold
11. completed_implies_laxity_deadline_minus_now
12. laxity_step_running_uni
13. laxity_step_not_running_uni
14. MetricChooser.v (all definitions + lemmas)
15. Laxity.v (llf_metric, choose_llf, llf_generic_spec, etc.)
16. PartitionedLLF.v
