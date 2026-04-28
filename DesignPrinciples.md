## Design Principles

This project aims to provide a shared foundation for **scheduler semantic
layers**, **executable scheduler models**, **schedulability analysis**, and
**refinement theories** connecting them.

Its central concern is not only whether scheduling theory can be stated
abstractly, but also whether abstract scheduling policies, executable decision
procedures, observable traces, and OS-level scheduler behavior can be related in
a single mechanized framework.

The project is intended to scale from **single-CPU scheduling**, to
**multicore scheduling**, and eventually to **trace-based and OS-level scheduler
semantics**.

### 1. Schedule semantics first

The project treats schedule semantics as the primary semantic foundation.

A schedule is the mathematical object over which execution, service,
completion, readiness, deadline misses, validity, feasibility, and
schedulability properties are defined. This gives the framework a stable base
that is independent of any particular scheduling algorithm, task model, or OS
implementation.

Executable scheduling logic, trace semantics, and OS-level operational
semantics are then connected back to this schedule-level foundation.

### 2. Separate semantic layers from reasoning theories

The project distinguishes semantic objects from theories about those objects.

The scheduler semantic layers consists of:

- **schedule semantics**, the mathematical model used by analysis and policy
  specifications;
- **trace semantics**, the observable event model used to connect logs and
  executions to schedules;
- **OS-level scheduler operational semantics**, the state-transition model that
  explains how scheduler traces are produced.

Around these semantic layers, the project develops reasoning theories such as
analysis theory, refinement theory, and checker correctness theory.

This separation avoids treating analysis or refinement as additional semantic
objects. Analysis proves properties over schedules, while refinement proves
correctness of the connections between semantic layers.

### 3. Refinement as a core design objective

Refinement is a first-class goal.

The framework is designed to connect abstract scheduling policies, executable
scheduling algorithms, traces, and OS-level operational executions through
explicit correctness statements.

Typical refinement obligations include:

- executable choosers satisfy declarative policy specifications;
- generated schedules are admitted by schedule semantics;
- traces project to schedules correctly;
- operational executions produce well-formed traces;
- implementation-facing scheduler behavior refines abstract scheduler
  specifications.

Thus, correctness can be established not only at the level of abstract
specifications, but also at the level of executable decision procedures and
implementation-facing scheduler behavior.

### 4. Clear separation between policy, validity, and scheduling algorithm

A key design principle is to separate:

- abstract scheduling policy,
- semantic validity conditions for schedules,
- concrete scheduling algorithms that make choices,
- scheduler interfaces that combine choices with system constraints,
- refinement arguments that connect algorithms and operational behavior back to
  policy and semantics.

This separation keeps specifications modular and reusable while preserving a
clear path from theory to implementation.

### 5. Executable scheduler models as certified witnesses

For concrete algorithms, the objective is not merely to restate classical
results, but to mechanize the path from declarative policy to executable choice.

This includes:

- finite candidate reasoning,
- tie handling,
- deterministic canonicalization,
- schedule transformations,
- swap lemmas,
- executable choosers,
- proofs that a chooser implements the intended scheduling discipline.

Executable scheduler models should be usable both as proof artifacts and as
components that can be extracted into checkers or witness validators.

### 6. Multicore as an early semantic target

Multicore scheduling is treated as an early semantic concern rather than a late
extension.

The project is structured to support:

- partitioned scheduling,
- global scheduling,
- clustered scheduling,
- affinity-aware scheduling,
- migration-aware scheduling,
- top-`m` selection,
- per-CPU projections,
- multicore validity and no-duplication invariants.

These developments should be built over a common schedule-level framework, so
that multicore semantics can be developed systematically rather than retrofitted
after uniprocessor theory has already hardened.

### 7. Toward trace and OS-level scheduler semantics

The long-term direction is to move beyond abstract schedules toward
implementation-facing scheduler models.

This includes trace semantics for observable scheduling events such as:

- release,
- dispatch,
- preemption,
- completion,
- blocking,
- wakeup,
- migration,
- timer events,
- IPI-related events.

It also includes OS-level scheduler operational semantics for mechanisms such
as:

- run queues,
- current task state,
- scheduler state updates,
- wakeup paths,
- blocking paths,
- choose points,
- preemption points,
- timer-driven scheduling,
- IPI-driven scheduling,
- bounded dispatch or handoff delay.

The purpose of these layers is to justify that concrete or OS-facing executions
produce traces that can be projected back to schedule semantics.

### 8. Task models as extensions over a semantic core

Periodic, sporadic, jitter-aware, and DAG-based task models remain important,
but they are treated as extensions over the semantic core rather than as the
foundation of the framework.

Task models define how jobs are generated and what assumptions those generated
job sets satisfy. They should connect to scheduler policies and analysis
theories without redefining the basic meaning of schedules.

This keeps the framework centered on scheduler meaning and correctness, while
still supporting richer workload models and schedulability results.

### 9. Analysis theory built on top of schedule semantics

Schedulability analysis is an important outcome, but it is not the organizing
principle of the framework.

The intended architecture is to place analysis theory on top of schedule
semantics. Analysis proves timing and schedulability properties of schedules,
such as:

- service and completion properties,
- no-deadline-miss theorems,
- busy-interval and busy-window results,
- demand and supply bounds,
- interference bounds,
- workload absorption lemmas,
- bounded tardiness,
- finite-horizon bridge theorems,
- infinite-time wrappers.

Trace semantics and OS-level operational semantics justify that concrete
executions give rise to the schedules to which these analysis results apply.

### 10. Related Work

A natural point of comparison is **Prosa**, a mechanized framework for
real-time scheduling theory.

Prosa places verified schedulability analysis at the center of its design and
provides substantial libraries for priority models, schedule models,
interference reasoning, response-time analysis, and classical results such as
EDF-related optimality and schedulability theorems.

By contrast, this project takes the connection between **scheduler semantic
layers**, **executable scheduler models**, and **refinement theories** as its
organizing principle.

The difference is therefore not whether familiar scheduling algorithms are
formalized, but how far the mechanization is intended to proceed:

```text
abstract policy
  -> executable chooser
  -> semantic schedule admission
  -> trace semantics
  -> OS-level scheduler operational semantics
  -> schedulability analysis over the resulting schedules
````

The goal is to connect scheduling theory, executable scheduler behavior,
multicore semantics, trace-based validation, and OS-facing operational models
within one Rocq development.
