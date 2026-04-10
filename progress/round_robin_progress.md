# Proof Progress: Round Robin Policy

## Status Overview
- Overall: **Complete**
- Complete Items: 15/15
- Unproven (`Admitted`): none
- Failed/Abandoned Items: none

## Completed Items

### `theories/UniPolicies/RoundRobin.v`

All definitions and lemmas compile cleanly:
- `choose_rr` — first-eligible scan (identical to `choose_fifo`)
- `choose_rr_eligible`, `choose_rr_none_if_no_eligible`, `choose_rr_some_if_exists`, `choose_rr_in_candidates`
- `rr_generic_spec : GenericSchedulingAlgorithm`
- `choose_rr_first_eligible` — policy invariant
- `rr_policy : SchedulingAlgorithmSpec`
- `rr_policy_sane : SchedulingAlgorithmSpecSanity rr_policy`
- `choose_rr_refines_rr_policy`
- `rr_bundle : UniSchedulerBundle`
- `rr_scheduler_on` — concrete scheduler wrapper
- `rr_policy_scheduler_on` — abstract policy scheduler wrapper

### `theories/PartitionedPolicies/PartitionedRR.v`

- `partitioned_rr_scheduler` — thin wrapper over `PartitionedCompose`
- `local_rr_witnesses_imply_partitioned_rr_schedulable_by_on` — main theorem

### `theories/RRExamples.v`

2-job single-CPU example demonstrating the full RR interface:
- `rr_example_jobs`, `J_rr`, `rr_example_cands`, `rr_example_sched`
- `rr_example_cands_spec` — CandidateSourceSpec
- `rr_example_cpu_count_j0_pos`, `rr_example_cpu_count_j1_pos2`
- `rr_example_service_j0`, `rr_example_service_j1`
- `rr_example_satisfies_scheduler`, `rr_example_valid`, `rr_example_feasible`
- `rr_two_jobs_schedulable`

### Build

- `_CoqProject` updated with 3 new entries
- Makefile regenerated with `rocq makefile`
- `make` passes cleanly (all 32 files compile)

## Key Pitfalls Encountered

1. **`simpl` iota reduction on Fixpoints**: After `rewrite service_job_step`, do NOT call `simpl` — it will unfold `service_job` further since `S t` is constructor-headed. Use `rewrite Nat.add_0_r` instead.

2. **`rewrite X` vs `unfold` ordering**: Always `rewrite HNone` (where HNone involves `rr_example_sched`) BEFORE `unfold rr_example_sched`. If you unfold first, the goal no longer contains `rr_example_sched` and the rewrite fails.

3. **`->` pattern with opaque predicates**: After `simpl in Hin` on `In j [1; 0]`, the disjuncts are `1 = j` (not `j = 1`). Using `->` tries to rewrite `1` in the goal — fails if the goal `J_rr j` is opaque. Use `destruct as [H|[H|[]]]` + `exact (eq_sym H)`.

4. **`cpu_count` free-variable reduction**: For case splits on `t =? 0` inside cpu_count, prove a helper lemma using `destruct (t =? 0); reflexivity` rather than trying `lia` or `simpl` on the full goal.

5. **`uni_scheduler_on_valid` type mismatch**: Use `single_cpu_algorithm_valid` directly rather than `uni_scheduler_on_valid` to avoid implicit argument confusion.
