# Semantics

## Scope

This document describes the semantic layer of the current RocqSched implementation.

Its scope is:

- `theories/Semantics/Schedule.v`
- `theories/Semantics/ScheduleLemmas/ScheduleFacts.v`
- `theories/Semantics/ScheduleLemmas/SchedulePrefix.v`
- `theories/Semantics/ScheduleLemmas/ScheduleRestriction.v`
- `theories/Semantics/ScheduleLemmas/ScheduleTruncationCore.v`
- `theories/Semantics/ScheduleLemmas/ScheduleTruncation.v`
- `theories/Semantics/ScheduleLemmas/ScheduleTransform.v`

This layer gives meaning to the raw `Schedule` carrier from Foundation and packages the semantic preservation lemmas that later abstraction, policy, and analysis layers reuse.

## Purpose of the Semantics layer

The semantics layer is where schedule meaning is fixed.

Its role is to define:

- what it means for a job to occupy a CPU at a time slot,
- how much service a job has accumulated up to a time,
- when a job is completed, running, eligible, or ready,
- what makes a schedule valid,
- what it means to miss a deadline or to be feasible,
- and which of these notions are preserved by prefix agreement, restriction, truncation, and local schedule rewrites.

This layer is intentionally policy-neutral. It does not decide which job should run; it only defines the semantic universe in which scheduler, analysis, and refinement layers operate.

## Core definitions

The central carrier remains:

```coq
Schedule := Time -> CPU -> option JobId
```

As in Foundation, this is only the schedule shape. The CPU bound `m` is not embedded into the type; semantic predicates take `m` explicitly.

### Slot-level execution

`Schedule.v` defines:

```coq
runs_on : Schedule -> JobId -> Time -> CPU -> bool
cpu_count : nat -> Schedule -> JobId -> Time -> nat
running : nat -> Schedule -> JobId -> Time -> Prop
```

with the following intended meanings:

- `runs_on sched j t c` is the boolean test that CPU `c` runs job `j` at time `t`
- `cpu_count m sched j t` counts how many CPUs in `0 .. m - 1` run job `j` at time `t`
- `running m sched j t := exists c, c < m /\ sched t c = Some j`

This makes the layer multicore-aware from the start, even when later developments specialize to `m = 1`.

### Service and completion

The cumulative service definition is:

```coq
service_job : nat -> Schedule -> JobId -> Time -> nat
```

where `service_job m sched j t` is the total service received by job `j` in the interval `[0, t)`, summed over CPUs `0 .. m - 1`.

Completion is defined by comparing service to cost:

```coq
completed :
  (JobId -> Job) -> nat -> Schedule -> JobId -> Time -> Prop
```

with meaning:

```coq
completed jobs m sched j t :=
  service_job m sched j t >= job_cost (jobs j)
```

So `completed ... t` means "completed by the start of slot `t`".

### Eligibility and readiness

`Schedule.v` distinguishes:

```coq
eligible :
  (JobId -> Job) -> nat -> Schedule -> JobId -> Time -> Prop
ready :
  (JobId -> Job) -> nat -> Schedule -> JobId -> Time -> Prop
```

with meanings:

- `eligible jobs m sched j t := released jobs j t /\ ~ completed jobs m sched j t`
- `ready jobs m sched j t := eligible jobs m sched j t /\ ~ running m sched j t`

This distinction is deliberate:

- running jobs are still eligible
- ready jobs are eligible jobs that are currently waiting rather than executing

`ScheduleFacts.v` also exposes boolean counterparts:

- `eligibleb`
- `readyb`

with specification lemmas `eligibleb_iff` and `readyb_iff`.

### Sequential-job discipline

The file also defines:

```coq
sequential_jobs : nat -> Schedule -> Prop
```

meaning that the same job cannot run simultaneously on two distinct CPUs in `0 .. m - 1`.

This is a job-level discipline used by several service/count lemmas. Future DAG-aware developments are expected to move this kind of exclusivity to node level rather than keep it at job level.

### Validity, deadlines, and feasibility

The main semantic well-formedness predicate is:

```coq
valid_schedule :
  (JobId -> Job) -> nat -> Schedule -> Prop
```

with meaning:

```coq
forall j t c, c < m -> sched t c = Some j -> eligible jobs m sched j t
```

So `valid_schedule` enforces that any scheduled job is already released and not yet completed. It is phrased in terms of `eligible`, not `ready`, because a currently running job should still be valid.

Deadline and feasibility notions are:

```coq
missed_deadline :
  (JobId -> Job) -> nat -> Schedule -> JobId -> Prop
feasible_schedule :
  (JobId -> Job) -> nat -> Schedule -> Prop
feasible :
  (JobId -> Job) -> nat -> Prop
feasible_schedule_on :
  (JobId -> Prop) -> (JobId -> Job) -> nat -> Schedule -> Prop
feasible_on :
  (JobId -> Prop) -> (JobId -> Job) -> nat -> Prop
```

Their meanings are:

- `missed_deadline` means not completed at `job_abs_deadline`
- `feasible_schedule` quantifies over all `JobId`
- `feasible` means there exists a schedule that is both valid and feasible
- `feasible_schedule_on` and `feasible_on` restrict deadline satisfaction to a designated subset `J`

The `*_on` versions are the forward-compatible interface for finite or subset-based reasoning.

### Remaining cost and laxity

`Schedule.v` finally defines:

```coq
remaining_cost :
  (JobId -> Job) -> nat -> Schedule -> JobId -> Time -> nat
laxity :
  (JobId -> Job) -> nat -> Schedule -> JobId -> Time -> Z
```

with meanings:

- `remaining_cost` is `job_cost - service_job`, using `nat` subtraction and therefore flooring at `0`
- `laxity` is deadline slack, represented in `Z` so that negative laxity is expressible

This is the semantic bridge used later by dynamic-metric policies such as LLF and by analysis layers.

## Major lemma groups

### `ScheduleFacts.v`

This file packages the first reusable consequences of the core definitions.

#### Reflection and count/service basics

It includes:

- `runs_on_true_iff`, `runs_on_false_iff`
- `service_job_unfold`, `service_job_step`
- `cpu_count_zero_iff_not_executed`
- `cpu_count_pos_iff_executed`, `cpu_count_nonzero_iff_executed`

Under `sequential_jobs`, it also provides:

- `cpu_count_le_1`
- `cpu_count_0_or_1`
- `cpu_count_eq_1_iff_executed`
- `service_job_increase_at_most_1`
- `service_job_increases_iff_executed`

These lemmas justify reading `cpu_count` and `service_job` as execution-counting objects rather than mere recursive functions.

#### Readiness, eligibility, and validity consequences

The file includes the main relational facts:

- `completed_not_ready`
- `ready_implies_released`
- `ready_implies_not_completed`
- `not_ready_before_release`
- `completed_monotone`
- `eligible_iff_released_and_not_completed`
- `ready_iff_eligible_and_not_running`
- `valid_no_run_before_release`
- `valid_no_run_after_completion`
- `valid_running_implies_eligible`
- `pre_release_not_eligible`
- `pre_release_not_ready`
- `ready_implies_not_running`
- `running_implies_not_ready`
- `completed_not_eligible`
- `eligible_after_release`
- `ready_after_release`
- `scheduled_implies_running`

Together these make the semantic relationships between release, execution, completion, readiness, and validity explicit.

#### Interval-service and deadline-miss lemmas

The file defines:

```coq
service_between : nat -> Schedule -> JobId -> Time -> Time -> nat
```

meaning service received in `[t1, t2)`.

It then proves:

- `completed_iff_service_ge_cost`
- `not_completed_iff_service_lt_cost`
- `missed_deadline_iff_not_completed_at_deadline`
- `missed_deadline_iff_service_lt_cost_at_deadline`
- `service_between_eq`
- `service_between_0_r`
- `service_between_refl`
- `service_between_split`
- `service_between_nonneg`
- `service_before_release_zero`
- `service_at_release_zero`
- `service_increases_implies_executed_in_interval`

These are the main bridge lemmas from raw semantic definitions to interval reasoning.

#### Remaining-cost and laxity lemmas

The file also provides:

- `remaining_cost_le_cost`
- `completed_implies_remaining_cost_zero`
- `remaining_cost_zero_implies_completed`
- `not_completed_implies_remaining_cost_pos`
- `remaining_cost_after_interval`
- `completed_if_service_between_covers_remaining_cost`
- `not_completed_if_service_between_insufficient`

For `m = 1`, it further packages:

- `service_job_step_uni`
- `remaining_cost_step_running_uni`
- `remaining_cost_step_not_running_uni`
- `laxity_unfold`
- `completed_implies_laxity_deadline_minus_now`
- `laxity_step_running_uni`
- `laxity_step_not_running_uni`

and also includes the feasibility-facing lemma:

- `eligible_feasible_implies_runs_later_before_deadline`

### `SchedulePrefix.v`

This file defines prefix agreement:

```coq
agrees_before : Schedule -> Schedule -> Time -> Prop
```

meaning that two schedules agree at every time strictly before `t`, on every CPU.

It provides:

- `agrees_before_weaken`
- `agrees_before_refl`
- `agrees_before_sym`
- `agrees_before_trans`

and then the prefix-extensionality lemmas:

- `cpu_count_agrees_at`
- `agrees_before_service_job`
- `agrees_before_completed`
- `agrees_before_eligible`
- `agrees_before_ready`
- `eligibleb_agrees_before`
- `agrees_before_remaining_cost`
- `agrees_before_laxity`

One subtle point matters here: `ready` reads the current slot through `running`, so `agrees_before_ready` requires agreement before `S t`, not merely before `t`.

### `ScheduleRestriction.v`

This file is more concrete than a generic "restriction framework". Its current API focuses on one-CPU and chosen-job-set restrictions.

It defines:

```coq
single_cpu_only : Schedule -> Prop
mk_single_cpu : Schedule -> Schedule
J_restrict : (JobId -> bool) -> Schedule -> Schedule
```

with meanings:

- `single_cpu_only sched` means all CPUs except `0` are idle
- `mk_single_cpu sched` keeps CPU `0` and clears all others
- `J_restrict J_bool sched` keeps only CPU `0`, and on that CPU keeps only jobs accepted by `J_bool`

It then proves preservation lemmas such as:

- `mk_single_cpu_cpu0`, `mk_single_cpu_other`, `mk_single_cpu_only`
- `mk_single_cpu_service`, `mk_single_cpu_valid`, `mk_single_cpu_feasible`
- `swap_at_single_cpu_only`
- `J_restrict_cpu0`, `J_restrict_other`, `J_restrict_only`
- `J_restrict_J_only`
- `J_restrict_service_J`
- `J_restrict_valid`, `J_restrict_feasible`

So the current restriction layer is explicitly geared toward extracting one-CPU or one-subset schedules while preserving semantic obligations.

### `ScheduleTruncationCore.v` and `ScheduleTruncation.v`

`ScheduleTruncationCore.v` defines the raw finite-horizon truncation operator:

```coq
trunc_sched : Schedule -> nat -> Schedule
```

with behavior:

- before horizon `H`, it agrees with the original schedule
- at or after `H`, it returns `None`

The core lemmas are:

- `trunc_sched_before`
- `trunc_sched_after`
- `trunc_sched_agrees_before`

`ScheduleTruncation.v` is currently a thin wrapper. It re-exports:

- `Semantics.ScheduleLemmas.ScheduleTruncationCore`
- `Uniprocessor.Generic.ScheduleTruncationPreservation`

So its role is not to add a new independent truncation semantics, but to provide one entry point that combines the raw truncation operator with the currently available uniprocessor preservation theorems:

- `trunc_sched_single_cpu_only`
- `trunc_sched_valid`
- `trunc_sched_feasible`
- `trunc_sched_preserves_canonical_before`

### `ScheduleTransform.v`

This file currently centers on a single local rewrite:

```coq
swap_at : Schedule -> Time -> Time -> Schedule
```

which swaps the CPU-0 contents of two time slots while leaving all other points unchanged.

The rest of the file is a structured library around this transformation:

- pointwise stability lemmas such as `swap_at_same_outside`, `swap_at_t1`, `swap_at_t2`
- one-CPU count helpers such as `cpu_count_1_swap_at_t1`, `cpu_count_1_swap_at_t2`, `cpu_count_1_swap_at_other`, `cpu_count_1_some_eq`, `cpu_count_1_some_neq`, `cpu_count_1_none`
- the generic bridge lemma `service_job_eq_of_cpu_count_eq`
- service-change lemmas such as `swap_at_service_unchanged_other_job`, `swap_at_service_prefix_before_t1`, `swap_at_service_j1_back_before_t2`, `swap_at_service_j2_front_before_t2`, `swap_at_service_j1_after_t2`, `swap_at_service_j2_after_t2`
- validity lemmas such as `valid_schedule_1_service_le_cost`, `swap_at_validity_new_front_job`, `swap_at_validity_new_back_job`, `swap_at_preserves_valid_schedule`
- feasibility lemmas such as `swap_at_preserves_missed_deadline_other_job`, `swap_at_improves_front_job`, `swap_at_does_not_hurt_later_deadline_job`, `swap_at_preserves_feasible_schedule_on`
- additional variants handling `None`, non-strict equalities, and related side conditions, including `*_none`, `*_ne`, and `*_le` families

So the current transform layer is specifically an exchange-argument toolkit for one-CPU proofs, rather than a fully generic schedule-rewrite algebra.

## Public entry points

The stable entry points for this layer are:

- `theories/Semantics/Schedule.v`
- `theories/Semantics/ScheduleLemmas/ScheduleFacts.v`
- `theories/Semantics/ScheduleLemmas/SchedulePrefix.v`
- `theories/Semantics/ScheduleLemmas/ScheduleRestriction.v`
- `theories/Semantics/ScheduleLemmas/ScheduleTruncationCore.v`
- `theories/Semantics/ScheduleLemmas/ScheduleTruncation.v`
- `theories/Semantics/ScheduleLemmas/ScheduleTransform.v`

In practice:

- downstream definitions should start from `Schedule.v`
- downstream proofs should prefer the packaged lemmas from `ScheduleLemmas/*` rather than repeatedly unfolding semantic definitions

## Design boundaries

This layer includes:

- schedule meaning,
- service, completion, running, eligibility, and readiness semantics,
- validity and deadline/feasibility semantics,
- remaining-cost and laxity semantics,
- prefix, restriction, truncation, and local-transform preservation lemmas.

This layer does not include:

- concrete scheduling policies such as EDF, LLF, FIFO, RR, or top-`m`,
- scheduler or algorithm interfaces,
- periodic, sporadic, or jitter-aware job generation,
- analysis concepts such as busy windows, demand bound, or interference bounds,
- operational traces or implementation-facing state machines.

Those belong respectively to:

- `design/Uniprocessor.md` and `design/Multicore.md`
- `design/Abstractions.md`
- `design/TaskModels.md`
- `design/Analysis.md`
- `design/Operational.md`

## Extension points

The current semantic layer already exposes natural growth directions:

- more multicore-generic service, remaining-cost, and laxity lemmas,
- deeper subset and finite-horizon wrappers built on `feasible_schedule_on` and `feasible_on`,
- future node-level or DAG-aware execution semantics,
- additional local transformation lemmas that preserve the same semantic core.

Such extensions should preserve the role of this layer as the place where schedule meaning is fixed, not the place where policies or analyses are defined.

## File map

- `theories/Semantics/Schedule.v`
  Core semantic definitions for execution, service, completion, eligibility, readiness, validity, feasibility, remaining cost, and laxity.
- `theories/Semantics/ScheduleLemmas/ScheduleFacts.v`
  Reflection lemmas, service/count facts, validity consequences, interval-service lemmas, remaining-cost lemmas, and uniprocessor laxity/step facts.
- `theories/Semantics/ScheduleLemmas/SchedulePrefix.v`
  Prefix agreement and prefix-extensionality results for service, completion, eligibility, readiness, remaining cost, and laxity.
- `theories/Semantics/ScheduleLemmas/ScheduleRestriction.v`
  One-CPU restriction operators and chosen-job-set restriction operators with service, validity, and feasibility preservation lemmas.
- `theories/Semantics/ScheduleLemmas/ScheduleTruncationCore.v`
  Raw finite-horizon truncation operator and its core agreement lemmas.
- `theories/Semantics/ScheduleLemmas/ScheduleTruncation.v`
  Re-export wrapper that bundles truncation core with the currently available uniprocessor preservation lemmas.
- `theories/Semantics/ScheduleLemmas/ScheduleTransform.v`
  CPU-0 slot-swap transformation lemmas used by exchange, repair, and normalization arguments.

## Summary

The semantics layer is the policy-neutral core that turns the raw schedule carrier into a precise semantic object.

It defines the meaning of execution, service, completion, validity, feasibility, remaining work, and slack, and it packages the preservation lemmas that later layers rely on when they compare, restrict, truncate, or locally transform schedules. Its scope should remain explicit and semantic, without drifting into policy definitions or analysis-specific reasoning.
