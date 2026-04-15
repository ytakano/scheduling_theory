# Abstractions

## Scope

This document describes the abstraction layer that connects:

- the semantic notion of schedules,
- local scheduling algorithms,
- candidate-job provisioning,
- global scheduler-level schedulability statements,
- and the canonical bridge notions that connect local choice with concrete schedules.

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
- `theories/Uniprocessor/Generic/SchedulingAlgorithmCanonicalBridge.v`

This document does **not** define:

- concrete policy rules such as EDF, LLF, FIFO, or Round Robin,
- schedulability analyses such as demand-bound or processor-demand arguments,
- task-generation semantics for periodic or sporadic models,
- OS-level operational semantics such as interrupts, migrations, or wakeups.

---

## 1. Purpose of the abstraction layer

The abstraction layer separates five concerns that should not be conflated:

1. the semantic meaning of schedules,
2. local executable choice,
3. candidate provisioning,
4. global scheduler admission,
5. canonical agreement between schedules and local choice.

The first four are the core abstractions. The fifth is the bridge notion that turns a local chooser into a concrete schedule-oriented object.

---

## 2. Abstractions core

This section introduces the core abstractions before any canonical bridge notion is stated.

### 2.1 `GenericSchedulingAlgorithm`

A `GenericSchedulingAlgorithm` is a local single-CPU choice procedure.

It provides a function of the form

```coq
choose :
  (JobId -> Job) -> nat -> Schedule -> Time -> list JobId -> option JobId
```

Given the job map, CPU count, current schedule prefix, current time, and a candidate list, it returns either:

- `Some j`, meaning that job `j` is selected, or
- `None`, meaning that no candidate is selected.

The interface guarantees that:

- any chosen job is eligible,
- any chosen job belongs to the candidate list,
- if some candidate is eligible, the result is `Some`,
- if no candidate is eligible, the result is `None`.

This is the smallest executable abstraction for single-CPU scheduling.

---

### 2.2 `CandidateSource`

A `CandidateSource` provides the candidate list seen by the local scheduling algorithm:

```coq
CandidateSource :=
  (JobId -> Job) -> nat -> Schedule -> Time -> list JobId
```

The key separation is:

- the scheduling algorithm decides **which** visible job to choose,
- the candidate source decides **which jobs are visible**.

This keeps local scheduling choice independent from ownership, affinity, finite-horizon restriction, or subset enumeration.

---

### 2.3 `CandidateSourceSpec`

A candidate source is constrained by `CandidateSourceSpec J candidates_of`.

This specification requires three properties.

#### Soundness

Every candidate belongs to the designated subset `J`.

#### Completeness

Every eligible job in `J` appears in the candidate list.

#### Prefix extensionality

The candidate list at time `t` depends only on the schedule history strictly before `t`.

This last condition is structurally important because it prevents circular definitions during inductive schedule construction.

---

### 2.4 `Scheduler`

A `Scheduler` is a global semantic scheduler relation:

```coq
Record Scheduler := mkScheduler {
  scheduler_rel : (JobId -> Job) -> nat -> Schedule -> Prop
}.
```

Unlike `GenericSchedulingAlgorithm`, it does not describe how a choice is computed. It describes which full schedules are admitted.

This is the main relational abstraction used by schedulability statements.

---

### 2.5 `schedulable_by` and `schedulable_by_on`

A job set is `schedulable_by` a scheduler if there exists a schedule that:

- is admitted by the scheduler,
- is valid,
- and is feasible.

The restricted form `schedulable_by_on J` requires feasibility only for jobs in a designated subset `J`.

This restricted form is important for finite-horizon reasoning, subset-based bridge arguments, and generated finite job sets.

---

### 2.6 `SchedulingAlgorithmSpec`

The abstraction layer also supports a declarative policy view:

```coq
SchedulingAlgorithmSpec :=
  (JobId -> Job) -> nat -> Schedule -> Time -> list JobId -> option JobId -> Prop
```

This does not compute a choice. It specifies which choices are allowed.

This abstraction is useful when one wants to state policy properties without committing to a concrete executable chooser.

---

### 2.7 `SchedulingAlgorithmSpecSanity`

A declarative policy predicate is constrained by basic sanity conditions.

At minimum:

- if the policy allows `Some j`, then `j` is in the candidate list,
- if the policy allows `Some j`, then `j` is eligible.

The `None` case is intentionally left unconstrained.

This keeps the abstraction broad enough to describe both work-conserving and non-work-conserving specifications.

---

## 3. Canonical bridge notions

This section introduces the bridge notions that connect the abstraction core to concrete schedules.

In the current development, **canonicality** means that a schedule agrees with the scheduling algorithm’s `choose` result.

These notions are defined generically in:

- `theories/Uniprocessor/Generic/SchedulingAlgorithmCanonicalBridge.v`

Canonicality is not one of the core abstraction primitives. It is a bridge notion built on top of:

- `GenericSchedulingAlgorithm`,
- `CandidateSource`,
- and `Schedule`.

---

### 3.1 Canonicality at one time step

```coq
Definition matches_choose_at_with
    (alg : GenericSchedulingAlgorithm)
    (jobs : JobId -> Job)
    (candidates_of : CandidateSource)
    (sched : Schedule)
    (t : Time) : Prop :=
  sched t 0 = choose alg jobs 1 sched t (candidates_of jobs 1 sched t).
```

A schedule is canonical at time `t` if CPU 0 contains exactly the job selected by the algorithm from the candidate list at that time.

This is the smallest schedule-level bridge between:

- an executable local chooser,
- a candidate-source contract,
- and a concrete schedule slot.

---

### 3.2 Canonicality on a prefix

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

A schedule is canonical before horizon `H` if it agrees with the algorithm at every time strictly before `H`.

This prefix-oriented notion is the form most often used in witness, normalization, and repair arguments.

---

### 3.3 Why canonicality is separated from the core

Canonicality should be stated **after** the abstraction core because it depends on previously introduced notions:

- a local executable algorithm,
- a candidate source,
- and a schedule.

It should nevertheless appear **before** bridge-specific theorems, because later bridge arguments are most naturally phrased in terms of canonicality.

That is why the document separates:

- **Abstractions core**, and
- **Canonical bridge notions**.

---

## 4. Single-CPU executable abstraction

The single-CPU executable abstraction is still `GenericSchedulingAlgorithm`, but the important point here is how it is used.

Its design is intentionally minimal:

- ineligible jobs may appear in the candidate list,
- the algorithm must never choose them,
- candidate completeness is handled by `CandidateSourceSpec`,
- canonicality is expressed separately by `matches_choose_at_with` and `matches_choose_before`.

This separation is one of the main design choices of the current abstraction layer.

---

## 5. Generic lemmas for single-CPU algorithms

`SchedulingAlgorithm/Lemmas.v` develops generic consequences of the single-CPU interface.

These lemmas derive facts such as:

- a chosen job is released,
- a chosen job is not completed,
- if an eligible candidate exists, `choose` cannot return `None`,
- if `choose = None`, then no candidate is eligible,
- the chosen job belongs to the candidate list.

These are interface-level facts. They are used by bridges and later policy proofs without unfolding the raw algorithm definition.

---

## 6. Constructive core and classical add-ons

The abstraction layer explicitly separates constructive reasoning from classical reasoning.

### Constructive core

`SchedulingAlgorithm/Lemmas.v` remains constructive.

### Classical add-ons

`SchedulingAlgorithm/ClassicalLemmas.v` contains convenience lemmas that rely on classical logic.

This separation avoids polluting the core abstraction layer with classical reasoning while still allowing classical helper lemmas in confined modules.

---

## 7. Constant finite candidate enumeration

`EnumCandidates.v` provides a simple canonical candidate source:

```coq
enum_candidates_of : list JobId -> CandidateSource
```

It ignores time and schedule state and always returns the same finite list.

This is useful for:

- finite examples,
- finite-horizon witness constructions,
- subset-based bridge arguments.

Its simplicity makes it one of the most stable candidate-source constructions in the current development.

---

## 8. The standard single-CPU bridge

`SchedulingAlgorithm/SchedulerBridge.v` provides the standard route from a local executable algorithm to a global scheduler relation.

### `single_cpu_algorithm_schedule`

This construction lifts:

- a `GenericSchedulingAlgorithm`,
- and a `CandidateSource`

into a `Scheduler`.

Its intended meaning is:

- `m = 1`,
- CPU 0 follows the algorithm’s choice,
- every other CPU is idle.

---

### Validity theorem

The key theorem is that schedules admitted by this bridge are valid.

This follows directly from the generic interface:
- any chosen job is eligible,
- and no other CPU runs anything.

---

### Relation to canonicality

The single-CPU bridge is the first place where canonicality becomes operationally meaningful.

Intuitively:

- the bridge constructs schedule behavior from `choose`,
- canonicality states that the schedule agrees with `choose`.

Thus, `matches_choose_at_with` and `matches_choose_before` are the natural schedule-facing views of the bridge.

---

## 9. Declarative policy validity

`Scheduler/Validity.v` defines what it means for a schedule to respect a declarative policy specification.

The key predicates are:

- `respects_algorithm_spec_at`
- `respects_algorithm_spec_at_with`
- `respects_algorithm_spec_before`

These allow the abstraction layer to connect:

- declarative policy predicates,
- candidate sources,
- and full schedules.

This yields a second path from local policy reasoning to global scheduler reasoning, parallel to the executable bridge path.

---

## 10. Top-`m` multicore abstraction

The multicore executable analogue of single-CPU local choice is `GenericTopMSchedulingAlgorithm`.

Instead of choosing one job, it chooses a list of up to `m` jobs.

This abstraction requires:

- no duplicates in the chosen list,
- every chosen job belongs to the candidate list,
- every chosen job is eligible,
- the chosen list has length at most `m`,
- if an eligible candidate is omitted, the chosen list is already full.

This is the current generic abstraction boundary for global multicore local selection.

---

## 11. The top-`m` scheduler bridge

`TopMSchedulerBridge.v` lifts a top-`m` algorithm into a global `Scheduler`.

Its intended reading is:

- CPU `c` runs the `c`-th selected job,
- if no such job exists, CPU `c` is idle.

This bridge proves that:

- admitted schedules are valid,
- CPUs outside the selected range are idle,
- the same job cannot run on two CPUs simultaneously.

This is the multicore counterpart of the standard single-CPU executable bridge.

---

## 12. Intended layering

The current architecture is best read as the following stack.

### Level 1: schedule semantics

The semantics layer defines:

- execution,
- service,
- eligibility,
- validity,
- deadline satisfaction.

### Level 2: abstractions core

The abstraction layer defines:

- `GenericSchedulingAlgorithm`
- `CandidateSource`
- `CandidateSourceSpec`
- `Scheduler`
- `schedulable_by`
- `schedulable_by_on`
- `SchedulingAlgorithmSpec`

### Level 3: canonical bridge notions

The abstraction layer then defines:

- `matches_choose_at_with`
- `matches_choose_before`

These express canonical agreement between a schedule and a local executable chooser.

### Level 4: executable bridges

The abstraction layer provides:

- `single_cpu_algorithm_schedule`
- `top_m_algorithm_schedule`

### Level 5: declarative policy validity

The abstraction layer also provides:
- policy-respecting schedule predicates,
- declarative schedule-admission views.

This split is more precise than mixing canonicality directly into the abstraction core.

---

## 13. Design boundaries

The abstraction layer deliberately does **not** do the following.

### It does not define concrete policies

EDF, LLF, FIFO, RR, and similar policy-specific rules belong in policy modules.

### It does not perform schedulability analysis

Busy intervals, response-time bounds, demand-bound functions, and processor-demand theorems belong in the analysis layer.

### It does not define task-generation semantics

Periodic, sporadic, jitter-aware, and DAG-related generation logic belong in task-model layers.

### It does not define OS operational behavior

Interrupts, migrations, wakeups, timer events, and machine-level concurrency belong in operational or refinement layers.

---

## 14. Extension points

Several extension directions are already visible.

### Richer candidate sources

The current `CandidateSource` abstraction can support:

- partition ownership,
- affinity filtering,
- finite-horizon restriction,
- subset-based filtering.

### Declarative-to-executable refinement

Because executable algorithms and declarative specifications coexist, the layer is already prepared for future refinement arguments showing that one implements the other.

### Multicore policy refinement

The top-`m` interface is the current generic hook for global multicore scheduling policies.

### Operational refinement

The abstraction layer is still schedule-level rather than event-level. It can later serve as the schedule-facing target of an operational kernel semantics.

---

## 15. File map

- `Abstractions/SchedulingAlgorithm/Interface.v`
  Core single-CPU executable choice abstraction.

- `Abstractions/SchedulingAlgorithm/Lemmas.v`
  Constructive generic lemmas for single-CPU algorithms.

- `Abstractions/SchedulingAlgorithm/ClassicalLemmas.v`
  Classical convenience lemmas.

- `Abstractions/SchedulingAlgorithm/EnumCandidates.v`
  Constant finite candidate enumeration.

- `Abstractions/SchedulingAlgorithm/SchedulerBridge.v`
  Standard bridge from a single-CPU algorithm to a scheduler relation.

- `Abstractions/SchedulingAlgorithm/TopMInterface.v`
  Multicore top-`m` executable choice abstraction.

- `Abstractions/SchedulingAlgorithm/TopMSchedulerBridge.v`
  Bridge from top-`m` selection to multicore scheduler semantics.

- `Abstractions/Scheduler/Interface.v`
  Global scheduler relation and schedulability predicates.

- `Abstractions/Scheduler/Validity.v`
  Declarative policy specifications and policy-respecting schedules.

- `Uniprocessor/Generic/SchedulingAlgorithmCanonicalBridge.v`
  Canonical bridge notions relating `choose` and concrete schedules.

---

## Summary

The abstraction layer should be documented in two clearly separated parts:

- **Abstractions core**
- **Canonical bridge notions**

The core introduces the stable abstraction objects:

- local algorithms,
- candidate sources,
- scheduler relations,
- schedulability predicates,
- declarative policy specifications.

The canonical bridge layer then introduces the derived notions:

- `matches_choose_at_with`
- `matches_choose_before`

that connect those abstraction objects to concrete schedule prefixes.

This separation makes the document read in dependency order and reflects the current implementation structure more accurately.