# Proof Plan: Policy Abstraction Layer

## Goal
Add a `DispatchPolicy` abstraction layer on top of the existing `GenericDispatchSpec` / `single_cpu_dispatch_schedule` infrastructure, without breaking any existing proofs. The concrete steps are:
1. `theories/SchedulerValidity.v` — `DispatchPolicy`, `PolicySanity`, `respects_policy_*`, `single_cpu_policy_scheduler` + 4 lemmas
2. `theories/DispatcherRefinement.v` — `dispatcher_refines_policy` + 3 lemmas
3. `theories/UniPolicies/EDF.v` — add `edf_policy`, `edf_policy_sane`, `choose_edf_refines_edf_policy`
4. `theories/UniPolicies/EDFLemmas.v` — add 2 compatibility lemmas
5. `theories/UniPolicies/FIFO.v` — add `fifo_policy`, `fifo_policy_sane`, `choose_fifo_refines_fifo_policy`

## Proof Strategy
New files added on top of existing infrastructure. Each file adds definitions and small lemmas that follow directly from existing properties. No existing proofs were changed.

## Proof Style
- [x] Constructive (all proofs fully constructive)

## Proposed Lemmas
- [x] `respects_policy_at_with_in_candidates`
- [x] `respects_policy_at_with_implies_eligible`
- [x] `respects_policy_at_with_in_subset`
- [x] `single_cpu_policy_schedulable_by_on_intro`
- [x] `single_cpu_dispatch_schedule_respects_policy_at_with`
- [x] `single_cpu_dispatch_schedule_respects_policy_before`
- [x] `single_cpu_dispatch_schedule_implies_single_cpu_policy_schedule`
- [x] `edf_policy_sane`
- [x] `choose_edf_refines_edf_policy`
- [x] `matches_choose_edf_at_with_implies_respects_edf_policy_at_with`
- [x] `respects_edf_policy_at_with_implies_respects_edf_priority_at_on`
- [x] `fifo_policy_sane`
- [x] `choose_fifo_refines_fifo_policy`

## Proof Order
All lemmas proven in file dependency order. Full `make` passes.

## Status: Complete
