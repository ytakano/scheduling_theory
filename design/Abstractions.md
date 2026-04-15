# Abstractions

## Scope

This document describes the abstraction layer that connects schedule semantics, local scheduling algorithms, candidate provisioning, and global scheduler-level schedulability statements.

The current scope includes:

- `theories/Abstractions/SchedulingAlgorithm/Interface.v`
- `theories/Abstractions/SchedulingAlgorithm/Lemmas.v`
- `theories/Abstractions/SchedulingAlgorithm/ClassicalLemmas.v`
- `theories/Abstractions/SchedulingAlgorithm/EnumCandidates.v`
- `theories/Abstractions/SchedulingAlgorithm/SchedulerBridge.v`
- `theories/Abstractions/SchedulingAlgorithm/TopMInterface.v`
- `theories/Abstractions/SchedulingAlgorithm/TopMSchedulerBridge.v`
- `theories/Abstractions/Scheduler/Interface.v`
- `theories/Abstractions/Scheduler/Validity.v`

It also refers to the generic canonical bridge:

- `theories/Uniprocessor/Generic/SchedulingAlgorithmCanonicalBridge.v`

---

## 1. Core notions used in this document

Before describing the abstraction layer, we fix the main notions that are used throughout the rest of this document.

### `GenericSchedulingAlgorithm`

A `GenericSchedulingAlgorithm` is a local single-CPU choice procedure.

It provides a function

```coq
choose :
  (JobId -> Job) -> nat -> Schedule -> Time -> list JobId -> option JobId
```

which selects one job from a candidate list, or returns `None`.

Its interface guarantees that:

- any chosen job is eligible,
- if some candidate is eligible, the result is `Some`,
- if no candidate is eligible, the result is `None`,
- any chosen job comes from the candidate list.

### `CandidateSource`

A `CandidateSource` is a function that supplies the candidate list seen by the scheduling algorithm at each time step:

```coq
CandidateSource :=
  (JobId -> Job) -> nat -> Schedule -> Time -> list JobId
```

A scheduling algorithm chooses from this list, but does not construct it.

### `Scheduler`

A `Scheduler` is a global semantic scheduler relation:

```coq
Record Scheduler := mkScheduler {
  scheduler_rel : (JobId -> Job) -> nat -> Schedule -> Prop
}.
```

It does not describe how choices are computed. It describes which full schedules are admitted.

### `schedulable_by` and `schedulable_by_on`

A job set is `schedulable_by` a scheduler if there exists a schedule that:

- is admitted by the scheduler,
- is valid,
- and is feasible.

The restricted form `schedulable_by_on J` requires feasibility only for jobs in a designated subset `J`.

---

## 2. Canonical schedules

In the current development, **canonicality** means that the schedule agrees with the scheduling algorithm’s `choose` result.

This notion is defined generically in
`Uniprocessor/Generic/SchedulingAlgorithmCanonicalBridge.v`.

### Canonicality at one time step

```coq
Definition matches_choose_at_with
    (alg : GenericSchedulingAlgorithm)
    (jobs : JobId -> Job)
    (candidates_of : CandidateSource)
    (sched : Schedule)
    (t : Time) : Prop :=
  sched t 0 = choose alg jobs 1 sched t (candidates_of jobs 1 sched t).
```

A schedule is canonical at time `t` when CPU 0 contains exactly the job chosen by the algorithm from the candidate list at that time.

### Canonicality on a prefix

```coq
Definition matches_choose_before
    (alg : GenericSchedulingAlgorithm)
    (jobs : JobId -> Job)
    (candidates_of : CandidateSource)
    (sched : Schedule)
    (H : Time) : Prop :=
  forall t, t < H ->
    matches_choose_at_with alg jobs candidates_of sched t.
```

A schedule is canonical before horizon `H` when it matches the algorithm at every time strictly before `H`.

### Why canonicality comes first

Canonicality is the bridge notion between:

- a local executable scheduling algorithm,
- a candidate source,
- and a full schedule.

Because later bridge and normalization arguments are stated in terms of canonicality, it should be defined before the rest of the abstraction story.

---

## 3. Purpose of the abstraction layer

The abstraction layer separates four concerns:

1. the meaning of schedules,
2. the local choice procedure,
3. the source of candidate jobs,
4. the global notion of scheduler-admitted schedules.

Canonicality is the first point where these concerns meet.

---

## 4. Candidate-source contracts

A `CandidateSource` is constrained by `CandidateSourceSpec J candidates_of`.

This contract requires:

- soundness: every candidate belongs to `J`,
- completeness: every eligible job in `J` appears in the candidate list,
- prefix extensionality: the candidate list at time `t` depends only on the schedule history before `t`.

These conditions are not part of `GenericSchedulingAlgorithm` itself. They belong to the bridge layer.

---

## 5. From local choice to global scheduler relations

The standard bridge is `single_cpu_algorithm_schedule`.

It lifts:

- a `GenericSchedulingAlgorithm`,
- and a `CandidateSource`

into a global `Scheduler` relation.

At this point, canonicality becomes the natural statement that the schedule follows the algorithm at every time step.

---

## 6. The rest of this document

The remaining sections describe:

- generic lemmas for `GenericSchedulingAlgorithm`,
- classical add-on lemmas,
- finite candidate enumeration,
- the standard single-CPU bridge,
- declarative policy specifications via `SchedulingAlgorithmSpec`,
- policy-respecting schedules,
- the top-`m` multicore analogue.
