# Proof Plan: Round Robin Policy

## Goal

Implement and verify `theories/UniPolicies/RoundRobin.v`, `theories/PartitionedPolicies/PartitionedRR.v`, and `theories/RRExamples.v` following the same structural pattern as FIFO/EDF.

## Proof Strategy

The key insight from `plan/rr.md`: **RR's semantics is entirely in the CandidateSource ordering**. The chooser (`choose_rr`) is structurally identical to `choose_fifo` — first-eligible scan. The RR invariant (which job rotates to the front) is expressed externally via the candidate list provided by the caller.

Unit-quantum (q=1) for the first implementation. General quantum can be added later.

## Proof Style
- [x] Constructive (preferred)
- [ ] Classical

## Proposed Lemmas (RoundRobin.v)

- [ ] `choose_rr`: dispatch function (first-eligible scan, identical to choose_fifo)
- [ ] `choose_rr_eligible`: chosen job is eligible
- [ ] `choose_rr_none_if_no_eligible`: None iff no eligible candidate
- [ ] `choose_rr_some_if_exists`: Some iff eligible candidate exists
- [ ] `choose_rr_in_candidates`: chosen job is in candidates
- [ ] `rr_generic_spec`: GenericSchedulingAlgorithm record
- [ ] `choose_rr_first_eligible`: policy invariant (prefix all ineligible)
- [ ] `rr_policy`: SchedulingAlgorithmSpec
- [ ] `rr_policy_sane`: SchedulingAlgorithmSpecSanity rr_policy
- [ ] `choose_rr_refines_rr_policy`: algorithm_refines_spec
- [ ] `rr_bundle`: UniSchedulerBundle
- [ ] `rr_scheduler_on`: concrete scheduler wrapper
- [ ] `rr_policy_scheduler_on`: abstract policy scheduler wrapper

## Proposed Items (PartitionedRR.v)

- [ ] `partitioned_rr_scheduler`: thin wrapper over partitioned_scheduler
- [ ] `local_rr_witnesses_imply_partitioned_rr_schedulable_by_on`: main theorem

## Proposed Items (RRExamples.v)

- [ ] Small job definitions (2-3 jobs)
- [ ] RR candidate source (unit-quantum rotation)
- [ ] `rr_scheduler_on` witness schedule
- [ ] `schedulable_by_on` derivation

## Proof Order

1. `choose_rr` + 4 generic lemmas + `rr_generic_spec`
2. `choose_rr_first_eligible` + `rr_policy` + `rr_policy_sane` + `choose_rr_refines_rr_policy`
3. `rr_bundle` + `rr_scheduler_on` + `rr_policy_scheduler_on`
4. Compile `RoundRobin.v`
5. `partitioned_rr_scheduler` + `local_rr_witnesses_imply_partitioned_rr_schedulable_by_on`
6. Compile `PartitionedRR.v`
7. `RRExamples.v` contents
8. Compile `RRExamples.v`
9. Update `_CoqProject`, regenerate Makefile, run `make`

## Completion Status

All items completed. See `progress/round_robin_progress.md` for details.
