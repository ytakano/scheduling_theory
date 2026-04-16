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
