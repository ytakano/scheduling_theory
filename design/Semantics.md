# Semantics

## Scope

This document describes the **semantic layer** of the current RocqSched implementation. Its purpose is to explain the core schedule model, the meaning of the main semantic predicates, and the small family of schedule-preserving transformations and prefix lemmas built on top of that model.

The current scope is limited to the following files:

- `theories/Semantics/Schedule.v`
- `theories/Semantics/ScheduleLemmas/ScheduleFacts.v`
- `theories/Semantics/ScheduleLemmas/SchedulePrefix.v`
- `theories/Semantics/ScheduleLemmas/ScheduleRestriction.v`
- `theories/Semantics/ScheduleLemmas/ScheduleTruncation.v`
- `theories/Semantics/ScheduleLemmas/ScheduleTransform.v`

This document does **not** specify:
- any scheduling policy such as EDF, LLF, FIFO, or Round Robin,
- any schedulability analysis such as demand-bound or processor-demand reasoning,
- any task-generation semantics for periodic or sporadic task models,
- any OS-level operational semantics such as interrupts, wakeups, or migrations.

---

## 1. Purpose of the Semantics Layer

The semantics layer provides the shared meaning of schedules and job states used by the rest of the development.

Its role is to answer questions such as:

- what it means for a job to be running,
- how much service a job has received,
- when a job is eligible or ready,
- what it means for a schedule to be valid,
- what it means for deadlines to be met,
- which properties are preserved under prefix agreement, restriction, truncation, and local schedule transformations.

This layer is intentionally policy-neutral. It does not decide **which** job should run. Instead, it defines the semantic universe in which policy layers and analysis layers operate.

---

## 2. Core Semantic Objects

The semantic layer builds on the base types defined in `Foundation/Base.v`:

- `JobId`
- `TaskId`
- `CPU`
- `Time`
- `Job`
- `Task`
- `Schedule`

A schedule is currently modeled as:

```coq
Schedule := Time -> CPU -> option JobId
```

This is a total function from time and CPU to either:
- `Some j`, meaning that job `j` is scheduled on that CPU at that time, or
- `None`, meaning that the CPU is idle at that time.

This is a **multicore schedule model** from the start. Uniprocessor reasoning is obtained by instantiating the CPU bound to `1` or by restricting a schedule to CPU 0.

The current execution unit is a **job**. The base layer already notes that future DAG extensions may replace this with node-level execution, but the present semantics is still job-based.

---

## 3. Execution Semantics

### `runs_on`

`runs_on sched j t c` is the Boolean test that checks whether job `j` runs on CPU `c` at time `t`.

It is the most local execution predicate and is used to connect slot-level scheduling with higher-level service accounting.

### `cpu_count`

`cpu_count m sched j t` counts how many CPUs among `0 .. m-1` execute job `j` at time `t`.

This definition is important because the semantic layer is multicore-aware even when later proofs focus on the uniprocessor case.

### `service_job`

`service_job m sched j t` is the cumulative service received by job `j` in the interval `[0, t)` over all CPUs below `m`.

This left-closed, right-open convention is central. It means that completion at time `t` always refers to service accumulated **before** slot `t`, which keeps the discrete-time semantics consistent.

---

## 4. Job-State Predicates

### `completed`

A job is `completed` at time `t` if its cumulative service in `[0, t)` is at least its execution cost.

Thus, completion means “completed by the beginning of time slot `t`.”

### `running`

A job is `running` at time `t` if there exists some CPU below `m` on which the schedule contains that job at time `t`.

### `eligible`

A job is `eligible` at time `t` if:
- it has been released, and
- it is not yet completed.

This is the minimum semantic condition for CPU assignment.

### `ready`

A job is `ready` at time `t` if:
- it is eligible, and
- it is not currently running on any CPU.

This matches the classical ready-queue intuition: a ready job is available to run, but not executing right now.

The distinction between `eligible` and `ready` is deliberate. A running job is still eligible, but it is not ready.

---

## 5. Schedule Well-Formedness

### `sequential_jobs`

`sequential_jobs m sched` states that the same job cannot run simultaneously on two different CPUs.

This is a job-level non-parallelism assumption. It fits the current non-DAG model. The comments in the code already indicate that DAG extensions would likely move this constraint from the job level to the node level.

### `valid_schedule`

`valid_schedule jobs m sched` requires that every scheduled job is eligible at the time it is scheduled.

This subsumes two essential sanity conditions:

- no job may run before its release,
- no job may continue running after it has already completed.

The validity predicate is therefore expressed in terms of `eligible`, not `ready`. A running job should be legal if it is released and unfinished, even though it is not in the “ready queue” sense.

---

## 6. Deadline and Feasibility Semantics

### `missed_deadline`

A job misses its deadline if it is not completed by its absolute deadline.

### `feasible_schedule`

A schedule is feasible if no job misses its deadline.

### `feasible`

A job set is feasible if there exists some schedule that is both valid and feasible.

The current semantics uses a total-function view over all `JobId`. This is simple and uniform, but it is not always the best fit for finite-horizon or subset-based reasoning.

### `feasible_schedule_on` and `feasible_on`

To support forward-compatible finite-set reasoning, the semantics layer also provides restricted variants:
- `feasible_schedule_on`
- `feasible_on`

These predicates express feasibility only for jobs in a designated set `J`.

This is an important bridge toward later developments that reason about generated job subsets, bounded horizons, or task-model-specific finite job sets.

---

## 7. Laxity Semantics

### `remaining_cost`

`remaining_cost` is the unfinished amount of work for a job at time `t`.

It is defined with `nat` subtraction, so it saturates at zero once the job has completed.

### `laxity`

`laxity` is the standard slack quantity:

deadline minus current time minus remaining work.

It is defined in `Z`, not `nat`, because negative laxity is semantically meaningful: it represents overdue work and directly captures deadline-miss situations.

This makes the definition suitable for LLF-style reasoning and for later comparisons between policy metrics.

---

## 8. Boolean Reflection Lemmas

The semantic layer includes Boolean counterparts of some Prop-valued predicates.

### `readyb`

`readyb` is the Boolean form of `ready`.

### `eligibleb`

`eligibleb` is the Boolean form of `eligible`.

### Reflection lemmas

The core reflection lemmas are:

- `readyb_iff`
- `eligibleb_iff`

These are important because selection functions and filtering code often need Boolean-valued predicates, while proofs are cleaner over propositions. The reflection lemmas connect these two views.

The same file also includes basic equivalences such as:

- `runs_on_true_iff`
- `runs_on_false_iff`
- `service_job_unfold`
- `service_job_step`

These lemmas make the semantic definitions usable in downstream proofs without repeatedly unfolding raw Fixpoints.

---

## 9. Prefix-Based Semantic Reasoning

The main prefix notion is:

```coq
agrees_before s1 s2 t
```

It states that two schedules agree at all times strictly before `t`, for all CPUs.

This is the key extensionality principle for finite-prefix reasoning. If two schedules agree on a prefix, then all quantities that only depend on the prefix should agree as well.

The semantics layer proves such preservation results for:

- `service_job`
- `completed`
- `eligible`
- `ready`
- `remaining_cost`
- `laxity`

This is one of the most stable and reusable parts of the current development. It is also the main reason the semantic layer can support transformation-based proofs without committing to any particular policy.

---

## 10. Schedule Restriction Operators

The restriction file introduces two useful constructions.

### `single_cpu_only`

This predicate states that every CPU except CPU 0 is always idle.

### `mk_single_cpu`

`mk_single_cpu` converts an arbitrary schedule into a schedule that keeps only CPU 0 and makes all other CPUs idle.

This provides a semantic bridge from multicore schedules to uniprocessor reasoning.

### `J_restrict`

`J_restrict` additionally filters execution on CPU 0 by a Boolean predicate over jobs.

This construction is useful when reasoning about designated job subsets while preserving schedule shape as much as possible.

The restriction lemmas show preservation of service and, where appropriate, preservation of validity and restricted feasibility.

---

## 11. Schedule Truncation

`trunc_sched` cuts a schedule at a finite horizon.

Before the truncation point, the truncated schedule agrees with the original schedule. After the truncation point, execution is removed.

This operator exists because many later arguments are fundamentally finite-prefix arguments even when the semantic model itself is total and unbounded in time.

The truncation lemmas are therefore not an ad hoc convenience. They are part of the core semantic toolkit for finite-horizon reasoning.

---

## 12. Local Schedule Transformations

The semantics layer also supports small local rewrites of schedules.

### `swap_at`

`swap_at` exchanges two time slots on CPU 0.

This is used by policy proofs and normalization arguments that transform one schedule into another while preserving selected semantic invariants.

The transformation lemmas track how such local rewrites affect:

- CPU counts,
- cumulative service,
- prefix behavior,
- job-specific service changes.

These lemmas are especially useful for exchange arguments and schedule normalization proofs in the uniprocessor layer.

---

## 13. Design Boundaries

The semantics layer deliberately avoids three things.

### No policy semantics

This layer does not encode EDF, LLF, FIFO, RR, or top-`m` selection. Those belong to policy and abstraction layers.

### No task-generation semantics

This layer does not define how periodic or sporadic tasks generate jobs. It only consumes a `jobs : JobId -> Job` mapping.

### No OS operational semantics

This layer is not yet a machine semantics for interrupts, migrations, wakeups, locks, or hardware events. It is a clean schedule semantics, not an operational kernel model.

These exclusions are intentional. They keep the semantic layer small, reusable, and stable.

---

## 14. Extension Points

The code already indicates several future extension directions.

### DAG-aware execution

The current semantics counts service at the job level. A DAG extension would likely introduce node-level execution and revise:
- `Schedule`
- `sequential_jobs`
- `service_job`
- readiness conditions

### Finite-set semantics

The restricted feasibility predicates already anticipate more explicit finite job-set reasoning.

### Richer multicore semantics

The current schedule model is multicore-capable, but it does not yet encode migration events, affinity transitions, or machine-level concurrency. Those belong to future operational or refinement layers.

---

## 15. File Map

- `Semantics/Schedule.v`
  Core semantic definitions: execution, service, eligibility, readiness, validity, deadlines, feasibility, laxity.

- `Semantics/ScheduleLemmas/ScheduleFacts.v`
  Basic equivalence lemmas, reflection lemmas, and foundational service/count facts.

- `Semantics/ScheduleLemmas/SchedulePrefix.v`
  Prefix agreement and prefix-extensionality results.

- `Semantics/ScheduleLemmas/ScheduleRestriction.v`
  Single-CPU restriction and job-set restriction.

- `Semantics/ScheduleLemmas/ScheduleTruncation.v`
  Finite-horizon truncation lemmas.

- `Semantics/ScheduleLemmas/ScheduleTransform.v`
  Local schedule rewrites such as slot swapping.

---

## Summary

The semantics layer defines the common meaning of schedules, service, job states, validity, and deadline satisfaction in a policy-independent way.

Its current design has three notable strengths:

1. it is multicore-aware from the beginning,
2. it cleanly separates `eligible` from `ready`,
3. it already supports prefix reasoning, restriction, truncation, and local transformation.

These features make it stable enough to serve as the semantic base for the current abstraction, uniprocessor, and analysis layers, while still leaving room for future DAG and operational extensions.
