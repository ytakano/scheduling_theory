# EDFInfiniteSchedulability no-carry-in progress

## Done

- Added reusable support lemmas to `theories/TaskModels/Periodic/PeriodicEDFInfiniteBridge.v`.
  - `generated_periodic_edf_schedule_scheduler_rel`
  - `generated_periodic_edf_schedule_valid`
  - `generated_periodic_edf_schedule_upto_agrees_before_generated`
  - `generated_periodic_edf_schedule_upto_completed_iff_generated_before`
- Added concrete specializations to `Tutorials/EDFInfiniteSchedulability.v`.
  - `sched_inf_ex_scheduler_rel`
  - `sched_inf_ex_valid`
  - `sched_upto_ex_completed_iff_sched_inf_ex`

These lemmas isolate the generic part of the remaining proof:
- the infinite generated EDF schedule is a valid EDF schedule,
- the finite `upto` schedule agrees with the infinite one before the horizon,
- and completion facts can be moved between them.

## Why this matters

`generated_edf_busy_prefix_no_carry_in_bridge_ex` is blocked less by EDF processor-demand theory than by schedule-local reasoning. The missing proof needs to show that any job running in `[release(j), deadline(j))` cannot be an earlier-release carry-in job.

The generic lemmas above remove the repeated boilerplate:
- no need to rebuild `scheduler_rel` for `sched_inf_ex`,
- no need to re-derive `valid_schedule`,
- no need to manually repackage prefix coherence each time a local completion fact is proved on `sched_inf_ex` and then used on `generated_periodic_edf_schedule_upto`.

## Current proof shape for the remaining bridge

The remaining work should stay tutorial-local in `Tutorials/EDFInfiniteSchedulability.v`.

Target:
- prove `generated_edf_busy_prefix_no_carry_in_bridge_ex`

Recommended proof route:
1. Work on `sched_inf_ex`, not directly on `generated_periodic_edf_schedule_upto`.
2. Prove local execution/completion facts around releases.
3. Transport completion facts to the finite schedule with `sched_upto_ex_completed_iff_sched_inf_ex`.
4. Use those facts to discharge the `periodic_edf_busy_prefix_no_carry_in_only` field.

## Next TODOs

1. Add concrete release/deadline normalization lemmas for `jobs_ex`.
   - even job ids are task 0 with release `5 * k` and deadline `5 * k + 2`
   - odd job ids are task 1 with release `7 * k` and deadline `7 * k + 3`

2. Add concrete EDF scheduling lemmas on `sched_inf_ex`.
   - task 0 job runs at each of its release times
   - task 1 job runs at its release time except at simultaneous releases
   - at simultaneous releases (`35 * q`), task 0 runs first and task 1 runs at the next slot

3. Convert those run facts into completion facts.
   - use `sched_inf_ex_valid`
   - use `service_at_release_zero`
   - use `remaining_cost_step_running_uni`
   - conclude completion at `release + 1`
   - then extend with `completed_monotone`

4. Prove a no-carry-in lemma on the infinite schedule.
   - if `job_release (jobs_ex j_run) < job_release (jobs_ex j)`
   - and `job_release (jobs_ex j) <= t`
   - then `j_run` is already completed at `t`
   - hence `sched_inf_ex t 0 <> Some j_run`

5. Transfer the no-carry-in fact to the finite `upto` schedule.
   - use prefix coherence at horizon `S (job_abs_deadline (jobs_ex j))`
   - use the completed-equivalence lemma added in this step

6. Finish `generated_edf_busy_prefix_no_carry_in_bridge_ex`.
   - unpack `periodic_jobset_deadline_between`
   - reduce to the no-earlier-job-runs fact
   - close with arithmetic on releases/deadlines

## Risks / open points

- The concrete EDF-choice proof may still need a small helper to control candidate membership at each release time.
- The real difficulty is not `busy_prefix_witness`; it is proving that earlier jobs are completed by the time the current window starts being relevant.
- If the local schedule proof becomes repetitive, add one more helper lemma in the tutorial, not in `theories/`, unless it is clearly reusable outside this example.

## 2026-04-16 follow-up

- Added concrete normalization lemmas in `Tutorials/EDFInfiniteSchedulability.v`:
  - `jobs_ex_task0_release`
  - `jobs_ex_task0_deadline`
  - `jobs_ex_task0_cost`
  - `jobs_ex_task1_release`
  - `jobs_ex_task1_deadline`
  - `jobs_ex_task1_cost`
- Added initial local definitions:
  - `service_slot_ex`
  - `slot_job_ex`
- Added a reusable arithmetic helper file:
  - `theories/TaskModels/Periodic/PeriodicArithmetic.v`
  - registered in `_CoqProject`
  - currently contains:
    - `nat_div2_double`
    - `nat_div2_succ_double`
    - `nat_div_mul_exact`
    - `nat_mod_mul_left`
    - `nat_div_35q_plus_1_by_7`
    - `nat_mod_35q_plus_1_by_35`
- Reintroduced a first stable batch of tutorial-local helper lemmas:
  - `jobs_ex_in_periodic_jobset`
  - `service_slot_ex_task0`
  - `service_slot_ex_task1`
  - `slot_job_ex_task0`
  - `slot_job_ex_task1_simultaneous`
- Reintroduced a second stable batch of tutorial-local helper lemmas:
  - `slot_job_ex_task1_non_simultaneous`
  - `jobs_ex_release_le_service_slot_ex`
  - `service_slot_ex_before_deadline_ex`

This keeps the tutorial compiling and fixes the concrete arithmetic interface needed for the next step.

What was attempted but intentionally not kept in this round:
- generic “soundness” lemmas tying every `slot_job_ex t = Some j` back to `service_slot_ex j = t`
- an initial direct proof pass toward the no-carry-in bridge using those stronger local facts
- an optional compatibility layer
  - `slot_job_ex t = Some j -> service_slot_ex j = t`
  - `slot_job_ex (service_slot_ex j) = Some j`

Why it was rolled back:
- the arithmetic normalizers are now available, but the local schedule lemmas still need a cleaner proof shape
- the first pass mixed arithmetic normalization and schedule reasoning too tightly
- keeping those partially stabilized proofs in the tutorial would make the next iteration harder, not easier
- in particular, the `job_id_of_ex` / `Nat.div2` normalization in the compatibility proof was still too brittle to justify keeping it

Current repository state after this pass:
- `theories/TaskModels/Periodic/PeriodicArithmetic.v` compiles
- `Tutorials/EDFInfiniteSchedulability.v` compiles
- the attempted compatibility lemmas were fully rolled back, so there is no new tracked code beyond the last stable helper batch
- the concrete helper layer is partially restored, but only for:
  - all jobs being in the periodic jobset
  - task-0 service slots
  - task-1 service-slot normalization
  - task-0 slot decoding
  - non-simultaneous task-1 slot decoding at `7 * k`
  - simultaneous task-1 slot decoding at `35 * q + 1`
  - the release-to-service-slot lower bound
  - the service-slot-before-deadline bound
- the bridge assumption `generated_edf_busy_prefix_no_carry_in_bridge_ex` is still not proved

Updated next step:
1. Prove exact run facts on `sched_inf_ex` from EDF candidate completeness/min-deadline reasoning.
   - task 0 at `5 * k`
   - task 1 at `7 * k` when `k mod 5 <> 0`
   - task 1 at `35 * q + 1` in the simultaneous-release case
   - optional idle lemma for all remaining slots
2. Do not block on the optional `slot_job_ex` / `service_slot_ex` compatibility lemma.
   - if a compatibility statement is reintroduced later, it should come only after the exact run lemmas are already stable
3. Turn run facts into completion facts using:
   - `sched_inf_ex_valid`
   - `service_at_release_zero`
   - `remaining_cost_step_running_uni`
   - `completed_monotone`
4. Prove the infinite-schedule no-carry-in lemma first, then transfer it to `generated_periodic_edf_schedule_upto` via `sched_upto_ex_completed_iff_sched_inf_ex`.
5. Only after those pieces are in place, finish `generated_edf_busy_prefix_no_carry_in_bridge_ex`.
