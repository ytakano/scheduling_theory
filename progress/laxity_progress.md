# Proof Progress: Laxity / LLF Implementation

## Status Overview
- Overall: Complete
- Complete Lemmas: All
- Unproven (`Admitted`): none
- Failed/Abandoned Items: none

## Completed Lemmas

### Phase A: `remaining_cost` and `laxity` definitions (ScheduleModel.v)

```coq
Definition remaining_cost
    (jobs : JobId -> Job) (m : nat) (sched : Schedule)
    (j : JobId) (t : Time) : nat :=
  job_cost (jobs j) - service_job m sched j t.

Definition laxity
    (jobs : JobId -> Job) (m : nat) (sched : Schedule)
    (j : JobId) (t : Time) : Z :=
  Z.of_nat (job_abs_deadline (jobs j))
  - Z.of_nat t
  - Z.of_nat (remaining_cost jobs m sched j t).
```

### Phase B: Basic lemmas (ScheduleLemmas/ScheduleFacts.v)

All proved constructively:
- `remaining_cost_le_cost`
- `completed_implies_remaining_cost_zero`
- `remaining_cost_zero_implies_completed`
- `not_completed_implies_remaining_cost_pos`
- `service_job_step_uni`
- `remaining_cost_step_running_uni`
- `remaining_cost_step_not_running_uni`
- `laxity_unfold`
- `completed_implies_laxity_deadline_minus_now`
- `laxity_step_running_uni`
- `laxity_step_not_running_uni`

### Phase C: MetricChooser.v

- `min_metric_job` (Fixpoint)
- `choose_min_metric`
- `min_metric_job_none_iff`
- `min_metric_job_in`
- `min_metric_job_min`
- `choose_min_metric_eligible`
- `choose_min_metric_none_if_no_eligible`
- `choose_min_metric_some_if_exists`
- `choose_min_metric_in_candidates`
- `choose_min_metric_min`
- `choose_min_metric_complete`
- `choose_min_metric_optimal`
- `choose_min_metric_unique_min`

### Phase D: Laxity.v

- `llf_metric`
- `choose_llf`
- `choose_llf_eligible`
- `choose_llf_some_if_exists`
- `choose_llf_none_if_no_eligible`
- `choose_llf_in_candidates`
- `llf_generic_spec`
- `choose_llf_min_laxity`
- `llf_policy`
- `llf_policy_sane`
- `choose_llf_none_implies_no_eligible`
- `choose_llf_refines_llf_policy`
- `LLFSchedulerSpec`
- `llf_scheduler_spec`
- `llf_bundle`
- `llf_scheduler_on`
- `llf_policy_scheduler_on`
- `llf_scheduler`

### Phase E: PartitionedPolicies/PartitionedLLF.v

- `partitioned_llf_scheduler`
- `local_llf_witnesses_imply_partitioned_llf_schedulable_by_on`

## Proof Attempts & Diagnostics

### Z_scope issue in ScheduleFacts.v laxity lemmas

- Attempt 1: Used `Local Open Scope Z_scope.` before laxity lemmas section.
  - Error: `0` in `sched t 0 = Some j` was parsed as `0%Z` (Z), not `0%nat` (CPU).
  - Diagnosis: With `Z_scope` open, even `sched t 0` caused type errors.
  - Fix: Used `%Z` explicit annotations in lemma statements and `0%nat` for CPU, and used `Nat2Z.inj_sub`, `Nat2Z.inj_succ` for Z.of_nat rewrites.

### `Restart` in compiled proof

- Attempt 1 of `choose_llf_none_implies_no_eligible`: Used `Restart` interactively.
  - Error: `Restart` is not valid in compiled mode.
  - Fix: Rewrote as a single clean proof using contradiction from `choose_llf_some_if_exists`.

## TODO
(all complete)
