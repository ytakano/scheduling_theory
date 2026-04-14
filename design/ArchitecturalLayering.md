# Architectural Layering

This document explains the intended architectural layering of the RocqSched development.
The goal is not only to organize files, but to make the proof structure visible from the directory structure itself.

The central design principle is:

> Define scheduling semantics first, separate executable scheduling algorithms from the schedules they induce, and connect concrete implementations to abstract specifications by refinement.

This separation keeps the library extensible across scheduling policies, machine models, task models, and later OS-level semantics.

---

## 1. Overall Structure

The development is organized around the following conceptual layers:

1. **Foundation**
2. **Semantics**
3. **Abstractions**
4. **Refinement**
5. **Analysis**
6. **Uniprocessor**
7. **Multicore**
8. **Operational**
9. **TaskModels**
10. **Examples**

These layers are not merely thematic.
They define the intended dependency direction of the library.

A higher layer may depend on lower layers, but a lower layer should not depend on a higher one.

---

## 2. Dependency Direction

The intended dependency direction is:

```text
Foundation
  -> Semantics
  -> Abstractions
  -> Refinement
  -> Analysis
  -> { Uniprocessor, Multicore, Operational, TaskModels }
  -> Examples
```

More concretely:

- `Foundation` contains reusable base definitions and proof utilities.
- `Semantics` defines what schedules, jobs, executions, and feasibility mean.
- `Abstractions` packages common interfaces and canonical views used across policies.
- `Refinement` connects executable or operational objects to semantic specifications.
- `Analysis` provides reusable schedulability-analysis theory on top of semantic schedules.
- `Uniprocessor` and `Multicore` build policy-specific theory for abstract machine models.
- `Operational` connects the abstract model to implementation-oriented scheduler state machines.
- `TaskModels` defines task-generation models that instantiate semantic job sets.
- `Examples` provides concrete instantiations and regression-style proof clients.

This is a logical dependency structure, not a claim that every file must follow a perfectly linear order.
However, new developments should preserve this direction unless there is a strong reason not to.

---

## 3. Foundation

**Purpose:** provide shared mathematical and proof infrastructure.

Typical contents include:

- time domains
- identifiers
- finite maps and finite sets
- list lemmas
- arithmetic utilities
- canonical proof helpers

This layer must remain policy-independent and model-independent.

It should not contain scheduling-specific theorems except for the most basic reusable definitions that are required everywhere.

---

## 4. Semantics

**Purpose:** define the meaning of scheduling objects.

This is the semantic core of the project.

Typical contents include:

- jobs and job parameters
- schedules
- release/completion predicates
- service and execution accounting
- validity and feasibility
- horizon-bounded schedule reasoning

A key principle is that **a schedule is defined first as a mathematical object**.
For example, a schedule may be modeled as a function from time and CPU to the job running there, if any.

This layer answers questions such as:

- What does it mean for a job to be running?
- What does it mean for a schedule to be valid?
- What does it mean for a job to complete?
- What does it mean for a job set to be feasible?

This layer should not commit to a particular scheduling algorithm.

---

## 5. Abstractions

**Purpose:** introduce reusable interfaces and canonical forms above raw semantics.

This layer exists to avoid duplicating structurally identical proof arguments across EDF, LLF, and future policies.

Typical contents include:

- generic scheduling algorithm interfaces
- canonical priority views
- witness-oriented abstractions
- common finite-horizon proof skeletons
- policy-independent exchange or local-step interfaces

This is the place where one factors out “the shape of a proof” from a specific policy.

For example, if EDF and LLF both use a finite-horizon witness argument with the same structure, that structure belongs here, while the policy-specific ordering facts belong higher up.

---

## 6. Refinement

**Purpose:** connect concrete scheduling procedures to abstract semantic objects.

This layer expresses statements of the form:

- an executable scheduler induces a schedule
- a local scheduling step refines an abstract policy condition
- an implementation-level scheduler is correct with respect to the semantic model

This separation is essential for long-term goals involving OS verification.
The project should be able to state and prove:

- an abstract scheduling specification,
- an executable scheduling algorithm,
- and a refinement theorem connecting the two.

This makes it possible to reuse schedule-level theory even when the implementation model changes.

---

## 7. Analysis

**Purpose:** provide reusable schedulability-analysis theory on top of semantic schedules.

This layer sits above semantic schedules and refinement, but below policy-specific theorem files.
Its role is to host analysis concepts that are neither task-generation logic nor scheduler implementation logic.

Typical contents include:

- busy intervals
- busy windows
- processor supply over intervals
- workload and demand aggregation
- request-bound and demand-bound style interfaces
- response-time search-space reduction lemmas
- generic interval decomposition lemmas

This layer is important because these concepts are used by many later results, but they do not belong to:

- `Semantics`, because they are not part of the meaning of schedules themselves
- `TaskModels`, because they are not about how jobs are generated
- `Operational`, because they are not implementation state machines
- `Uniprocessor` or `Multicore`, because many analysis patterns should be shared before specialization

In short:

- `Semantics` says what schedules mean.
- `Analysis` says how to reason about schedulability over intervals.
- `TaskModels` says where jobs come from.

This distinction should remain explicit in the directory structure.

---

## 8. Uniprocessor

**Purpose:** develop uniprocessor scheduling theory on top of the common core.

Typical contents include:

- EDF theorems
- LLF theorems
- finite optimality results
- uniprocessor feasibility theorems
- policy-specific witness constructions

This layer should reuse:

- semantic schedule definitions from `Semantics`
- reusable proof shapes from `Abstractions`
- refinement hooks from `Refinement`
- interval reasoning from `Analysis`

The uniprocessor layer should not redefine generic interval concepts if they can live in `Analysis`.

---

## 9. Multicore

**Purpose:** develop multicore scheduling theory.

Typical contents include:

- partitioned scheduling
- global scheduling
- migration-aware reasoning
- multicore feasibility and optimality theorems
- multicore witness constructions

As in the uniprocessor case, this layer should depend on shared lower layers rather than cloning them.

Whenever a proof concept is common to both uniprocessor and multicore reasoning, it should be pushed downward into `Abstractions` or `Analysis` instead of being duplicated.

---

## 10. Operational

**Purpose:** model scheduler execution as an implementation-oriented transition system.

This layer is for reasoning about operational scheduler states, such as:

- run queues
- local or global dispatcher state
- scheduling steps
- enqueue/dequeue behavior
- implementation invariants

The operational layer is intentionally distinct from the schedule semantics layer.

The semantic question is:

- what schedule is produced?

The operational question is:

- how does a scheduler state evolve to produce it?

This distinction is necessary for future refinement results involving actual kernels or scheduler implementations.

---

## 11. TaskModels

**Purpose:** define reusable job-generation models.

Typical contents include:

- periodic tasks
- sporadic tasks
- jittered periodic tasks
- DAG-style release structures
- finite-horizon job-set generation theorems

This layer explains how a task model generates a semantic job set.
It should not contain policy-specific scheduling theorems unless those are merely thin instantiations.

Conceptually:

- `TaskModels` generates jobs.
- `Semantics` interprets schedules over jobs.
- `Analysis` reasons about intervals and schedulability.
- `Uniprocessor` / `Multicore` prove policy-specific results.

Keeping these roles separate prevents the library from entangling generation logic with schedulability reasoning.

---

## 12. Examples

**Purpose:** provide small proof clients and concrete instantiations.

Examples serve several roles:

- sanity checks for APIs
- documentation by instantiation
- regression tests for refactoring
- minimal demonstrations of how layers fit together

Examples should consume the library rather than define new core abstractions.

---

## 13. Why Analysis Is a Separate Layer

The `Analysis` layer is intentionally separated because schedulability arguments often introduce theory that is not semantic in the narrow sense and not policy-specific in the final-theorem sense.

For example, a busy interval theorem is typically:

- not a definition of what a schedule is,
- not a description of how jobs are generated,
- not an implementation state transition,
- and not tied to EDF alone.

It is a reusable intermediate reasoning layer.

Without a separate `Analysis` layer, such theory tends to be scattered across:

- uniprocessor policy files,
- task-model-specific proofs,
- or ad hoc utility files.

That makes later extensions harder, especially when adding:

- utilization-based bounds,
- demand-bound analyses,
- response-time analyses,
- or multicore generalizations.

Therefore, interval-based analysis theory should live in `theories/Analysis/...` whenever it is meant to be reused across multiple later developments.

---

## 14. Design Rules for New Files

When adding a new file, use the following rules.

### Put it in `Semantics` if:

- it defines the meaning of schedules, jobs, service, completion, or feasibility

### Put it in `Abstractions` if:

- it factors out a reusable proof interface or canonical proof shape

### Put it in `Refinement` if:

- it connects a concrete scheduler or step relation to an abstract semantic property

### Put it in `Analysis` if:

- it reasons about workload, demand, supply, busy windows, or interval-based schedulability arguments

### Put it in `Uniprocessor` or `Multicore` if:

- it proves policy-specific theorems for those machine models

### Put it in `Operational` if:

- it models implementation-style scheduler state evolution

### Put it in `TaskModels` if:

- it defines how jobs are generated from a task model

### Put it in `Examples` if:

- it is mainly illustrative, demonstrative, or regression-oriented

---

## 15. Long-Term Intended Use

This layering is designed to support the following long-term path:

1. define schedules semantically,
2. define scheduling algorithms and operational schedulers separately,
3. prove refinement from implementation-oriented models to semantic schedules,
4. prove schedulability and optimality theorems on the semantic side,
5. instantiate the framework with richer task models and eventually OS-level semantics.

This path is meant to scale from:

- finite-horizon witness arguments,
- to uniprocessor and multicore theory,
- to refinement results for actual schedulers,
- and eventually to system-level validation or verification.

---

## 16. Summary

The core architectural principle is:

> semantics first, algorithms second, refinement in between, analysis as a reusable reasoning layer, and policy-specific theorems above them.

Accordingly, the project should preserve the following conceptual separation:

- **Semantics** for meaning
- **Abstractions** for reusable proof structure
- **Refinement** for correctness bridges
- **Analysis** for schedulability reasoning infrastructure
- **Uniprocessor / Multicore** for policy-specific theorems
- **Operational** for implementation models
- **TaskModels** for job generation

If this separation is reflected consistently in the directory structure, then the codebase itself will communicate the intended proof architecture.
