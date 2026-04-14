# Scheduling Architecture

This document explains the intended architectural separation between **Schedule**, **SchedulingAlgorithm**, and **Scheduler**, together with their roles in the formalization.

## 1. Schedule

A **schedule** is the execution timeline produced by a scheduler.
For each time step `t` and CPU `c`, it returns the job running there, if any.

In `Semantics/Schedule.v`, it is defined as:

```coq
Definition Schedule := Time -> CPU -> option JobId.
```

### Role

`Schedule` is the semantic object that represents an execution result.
It does not describe how scheduling decisions are made. Instead, it records the outcome of those decisions over time.

### Key predicates on schedules

The following predicates are defined in `Semantics/Schedule.v`:

* `eligible j t`
  Job `j` has been released and has not yet completed at time `t`.

* `ready j t`
  Job `j` is eligible at time `t` and is not currently running.

* `valid_schedule`
  Every job running in the schedule is eligible at the time it runs.

* `feasible_schedule_on J`
  Every job in `J` completes no later than its deadline.

These predicates capture the basic semantic correctness conditions of a schedule.

For multicore reasoning, `theories/Multicore/Common/MultiCoreBase.v` adds the
projection `cpu_schedule`, which turns one CPU view of a multicore schedule
into a 1-CPU schedule. This keeps per-CPU service and completion reasoning in
the common multicore layer instead of policy-specific files.

---

## 2. SchedulingAlgorithm

A **scheduling algorithm** is an executable local decision procedure.

Given the current scheduling context:

* the job map,
* the number of CPUs,
* the schedule constructed so far,
* the current time,
* and a candidate job list,

the algorithm selects the next job to run, if any.

This abstraction is defined by `GenericSchedulingAlgorithm` in
`theories/Abstractions/SchedulingAlgorithm/Interface.v`.

### Role

`SchedulingAlgorithm` captures the **local choice rule** used at each scheduling step.
It is intentionally executable and operational: it describes how the next job is selected from the current candidates.

### Generic correctness contract

The interface captures the minimal obligations shared by all concrete algorithms:

* the chosen job is eligible at the current time,
* if an eligible candidate exists, some job is chosen,
* if no candidate is eligible, `None` is returned,
* the chosen job is always a member of the candidate list.

This interface is designed to support multiple concrete policies while preserving a common correctness boundary.

### Examples

Concrete algorithms such as the following are instances of this interface:

* EDF
* FIFO
* Round Robin

These are defined, for example, in:

* `Uniprocessor/Policies/EDF.v`
* `Uniprocessor/Policies/FIFO.v`
* `Uniprocessor/Policies/RoundRobin.v`

---

## 3. Scheduler

A **scheduler** is a semantic scheduling object.

Rather than being only a local decision rule, it characterizes which schedules are admitted for a given job set and machine size. In general, it combines:

* a scheduling algorithm,
* a candidate-generation mechanism,
* validity conditions,
* refinement obligations,
* and machine or CPU structure.

In `theories/Abstractions/Scheduler/Interface.v`, it is defined as:

```coq
Record Scheduler := mkScheduler { scheduler_rel : ... }.
```

### Role

`Scheduler` is the **global semantic wrapper** around scheduling behavior.
It bridges executable local decisions and the full semantic notion of admitted schedules.

This makes it possible to reason about schedulability independently of the exact implementation details of any one algorithm.

### Key predicates on schedulers

The main predicates are:

* `schedulable_by S jobs m`
  There exists some valid and feasible schedule for `jobs` on a machine with `m` CPUs, admitted by scheduler `S`.

* `schedulable_by_on J S jobs m`
  The same notion, restricted to a designated job set `J`.

These predicates express schedulability at the semantic level.

---

## 4. Intended Layering

The intended architecture separates concerns as follows:

* **Schedule**
  The execution result, represented as a timeline.

* **SchedulingAlgorithm**
  A local executable choice rule applied at each scheduling step.

* **SchedulingAlgorithmSpec**
  An abstract specification describing the property that a scheduling algorithm must satisfy.

* **Scheduler**
  A global semantic object that packages:

  * a scheduling algorithm,
  * a candidate source,
  * validity conditions,
  * refinement obligations,
  * CPU or machine structure,
  * and the resulting schedule semantics.

This layering is intended to cleanly separate:

1. **what a schedule is**,
2. **how local dispatch decisions are computed**, and
3. **how full schedulability is defined semantically**.

---

## 5. Mapping of Concepts

The following examples illustrate how major concepts fit into this layering:

### SchedulingAlgorithm

These are executable local policies:

* EDF
* FIFO
* RR

### SchedulingAlgorithmSpec

These describe the abstract property that a policy must satisfy:

* EDF minimum-deadline choice
* FIFO first-eligible choice

### Scheduler-level predicates

These describe global semantic schedulability:

* `schedulable_by`
* `schedulable_by_on`

---

## 6. Design Intent

The purpose of this separation is to make the framework extensible and proof-friendly.

In particular, it allows us to:

* define executable scheduling policies independently from global schedulability semantics,
* reuse common algorithmic correctness interfaces across multiple policies,
* express scheduler-specific validity and refinement conditions without overloading the notion of schedule itself,
* and scale the framework from uniprocessor scheduling to richer settings such as partitioned or global multiprocessor scheduling.

This architecture also clarifies the distinction between:

* **execution artifacts** (`Schedule`),
* **decision procedures** (`SchedulingAlgorithm`),
* and **semantic schedulability objects** (`Scheduler`).
