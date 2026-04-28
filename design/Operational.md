# Operational

## Scope

This document describes the current operational layer of RocqSched.

Its scope is centered on:

- `theories/Operational/Common/*`

This is the reference document for the OS-neutral operational projection
slice. It is not a concrete OS semantics. Instead, it defines the common
proof-facing operational vocabulary, the projection boundary from concrete
states into that vocabulary, and the theorem families that recover semantic
schedule facts from projected executions.

## Purpose of the Operational layer

The operational layer exists to model implementation-facing scheduler behavior
without replacing the abstract schedule model from `design/Semantics.md`.

Its role is to define:

- proof-facing operational scheduler state and traces,
- small-step operational events and executions,
- OS-neutral projection from concrete machine states into that common view,
- theorem families that recover semantic validity from projected behavior,
- and adapter-local contract records that downstream concrete runtimes can
  discharge.

This layer is intentionally modest. It does not yet provide a full OS
semantics with full interrupt routing, migration behavior, or
scheduler-relation closure.

The common layer also does not define adapter-local emitted trace formats such
as Awkernel's `sched_trace` or `task_trace`. Those artifacts live below the
common interface. Downstream adapters may use them to reconstruct local replay
states, worker-slot occupancy, or scheduler-facing witnesses, but that
reconstruction is not itself part of `Operational/Common`.

## Core definitions

### Operational state and traces

The central common state is:

```coq
Record OpState : Type := mkOpState {
  op_current : CPU -> option JobId;
  op_runnable : list JobId;
  op_need_resched : CPU -> bool;
  op_dispatch_target : CPU -> option JobId;
}.
```

`OpState` is a proof-relevant scheduler view, not a concrete kernel state. It
records only the common observables needed by the operational bridge:

- `op_current`: which job currently occupies each CPU,
- `op_runnable`: a runnable-job view,
- `op_need_resched`: per-CPU reschedule requests,
- `op_dispatch_target`: per-CPU dispatch intentions.

The common operational trace is:

```coq
OpTrace := Time -> OpState
```

So an operational trace is a time-indexed stream of proof-facing scheduler
snapshots. It is not the full runtime execution trace of a concrete kernel.

### Operational events and steps

The common operational event vocabulary is:

```coq
Inductive OpEvent : Type :=
| EvWakeup (j : JobId)
| EvBlock (j : JobId)
| EvComplete (j : JobId)
| EvJoinTargetReady (j : JobId)
| EvRequestResched (c : CPU)
| EvHandleResched (c : CPU)
| EvChoose (c : CPU) (j : JobId)
| EvDispatch (c : CPU) (j : JobId)
| EvPreempt (c : CPU) (old new : JobId)
| EvStutter | EvTick.
```

These constructors define the common event categories used by the operational
step relation. They are not a concrete interrupt vocabulary, and they do not
encode full OS-specific causes or routing details. Their payloads are the
minimum common identifiers needed by proof-facing steps:

- `EvWakeup j` projects that job `j` entered the runnable view,
- `EvBlock j` projects that running job `j` became ineligible,
- `EvComplete j` projects that running job `j` completed,
- `EvJoinTargetReady j` projects adapter evidence that a join target for `j`
  is ready while leaving the common `OpState` unchanged,
- `EvRequestResched c` and `EvHandleResched c` are per-CPU reschedule
  request/handling observations,
- `EvChoose c j` records CPU `c` choosing runnable job `j` as a dispatch
  target,
- `EvDispatch c j` records CPU `c` installing job `j`,
- `EvPreempt c old new` records CPU `c` replacing `old` with `new`,
- and `EvStutter` / `EvTick` are state-preserving common observations.

At this layer, `EvBlock` only fixes an abstract effect: a released job may
become temporarily ineligible for selection. The common layer does not define
which concrete wait cause produced that effect or which concrete hook
re-enables the job later. There is no separate common `EvUnblock` event in the
current interface; an adapter proves that a concrete unblock, wake, or readiness
observation is enough evidence for a later projected runnable/wakeup fact.

`EvJoinTargetReady` is deliberately also common but weak: it names the job whose
join dependency became ready without adding concrete join queues, wait lists, or
waker mechanics to `Operational/Common`. Adapters decide which runtime event
source justifies that label.

The common small-step skeleton is:

```coq
op_step : OpState -> OpEvent -> OpState -> Prop
```

This is the common operational relation over proof-facing states. Downstream
adapters may justify that concrete steps project to this relation, but the
common layer does not itself define a concrete runtime.

### Execution packages

The layer packages small-step behavior into:

- `execution`
- `labeled_execution`

`execution` records stepwise operational evolution. `labeled_execution`
extends it with a per-step `OpEvent` label. These are common execution objects;
they still abstract away from concrete machine states.

### Delay-aware common surface

The operational layer also exposes:

- `op_delay_source`
- `cumulative_delay_budget`

This is the common delay-aware accounting boundary. It gives a shared
classification vocabulary and cumulative budget accounting over labeled
executions without turning `Operational/Common` into a full timer or interrupt
semantics.

### Projection boundary from concrete states

The common projection interfaces are:

- `OSProjection`
- `OSLabeledProjection`
- `os_to_op_trace`
- `osl_to_op_trace`
- `osl_to_op_event_trace`

`OSProjection` maps concrete machine state into `OpState`. `OSLabeledProjection`
extends that boundary with a projected `OpEvent` for each concrete transition.

The concrete trace carriers used by this boundary are:

- `concrete_trace`
- `concrete_execution`

These package concrete state streams and their projected operational views.
They are still common interfaces, not Awkernel-specific runtime formats.

### Adapter-local trace semantics

Some downstream adapters use emitted trace artifacts to drive acceptance and
refinement. For Awkernel, the relevant artifacts are `sched_trace` and
`task_trace`.

Their role is intentionally adapter-local:

- `sched_trace` is an emitted scheduler-facing trace artifact, not a common
  `OpTrace`,
- `task_trace` is an emitted task-family summary artifact, not a common event
  interface,
- a leading `event_id`, when present in emitted rows, is a runtime ordering key
  used by the adapter checker to align task-side blocked intervals with
  scheduler-side observations; it is not part of `OpState` or `OpEvent`,
- and any reconstruction from `sched_trace` into a logical worker schedule
  belongs to the adapter layer, not to `Operational/Common`.

This distinction matters for multiple-worker support. The common layer already
supports generic single-CPU and top-`m` scheduler-relation packages. An
adapter may therefore widen its local `sched_trace` semantics from a
single-worker interpretation to a capacity-`m` logical worker schedule without
changing `OpState`, `OpEvent`, `OSProjection`, or `OSLabeledProjection`.

The intended layering is:

- common layer: generic operational state, events, executions, and theorem
  packages,
- adapter layer: interpretation of emitted `sched_trace` into worker-slot
  occupancy, dispatch intervals, and scheduler-facing witnesses,
- runtime layer: concrete tracepoint placement, buffering, serialization, and
  other mechanics used to emit those artifacts.

This same split applies to blocking-aware eligibility. The common layer fixes
that blocking may make released work ineligible. Adapters must explain which
concrete states or events realize that abstract effect. The runtime only emits
the evidence used by that adapter proof. Concrete `Block` or `Unblock` records
are therefore adapter evidence until an adapter grammar maps them into the
common event vocabulary; they do not widen the common blocked boundary.

### Projection back into semantic schedules

The key bridge back into the semantic layer is:

```coq
project_schedule : OpTrace -> Schedule
```

with the derived notion:

- `projected_running`

`project_schedule` forgets everything except `op_current` and interprets an
operational trace as a semantic `Schedule`. This is the point where
`Operational` hands control back to `Semantics`.

## Major theorem groups

### Projection to schedules

The first theorem boundary explains when a projected operational trace is
semantically meaningful.

Important definitions and theorems are:

- `projectable_trace`
- `execution_projection_sound`
- `labeled_execution_projection_sound`
- `execution_projection_sound_implies_projectable`
- `execution_projection_sound_implies_valid_schedule`
- `projectable_trace_implies_valid_schedule`
- `labeled_execution_projection_sound_implies_projectable`
- `labeled_execution_projection_sound_implies_valid_schedule`

The intended reading is:

- `projectable_trace` states the trace-level conditions needed for projection,
- `execution_projection_sound` and
  `labeled_execution_projection_sound` package the corresponding execution-level
  obligations,
- and the `*_implies_valid_schedule` lemmas show that projected executions
  recover semantic `valid_schedule`.

This is the current common validity bridge. It says that projected operational
behavior can justify semantic schedule validity when the projection obligations
hold.

### Multicore validity and placement

The next theorem group strengthens plain schedule validity with multicore facts
that depend on range and placement invariants.

Important definitions and theorems are:

- `op_idle_outside_range`
- `op_respects_admissibility`
- `op_multicore_projection_inv`
- `projectable_trace_with_range_implies_multicore_semantic_validity`
- `projectable_trace_with_multicore_inv_implies_multicore_semantic_validity`
- `execution_multicore_projection_sound`
- `labeled_execution_multicore_projection_sound`
- `execution_multicore_projection_sound_implies_semantic_validity`
- `execution_multicore_projection_sound_implies_placement`
- `labeled_execution_multicore_projection_sound_implies_semantic_validity`
- `labeled_execution_multicore_projection_sound_implies_placement`

The intended reading is:

- projection soundness alone gives `valid_schedule`,
- adding range-idleness and admissibility-aware placement yields
  `multicore_semantic_validity`,
- and the bundled `*_multicore_projection_sound` records package those stronger
  obligations for downstream adapters.

This is the current multicore bridge from operational traces to the
multicore-common semantic layer.

### Adapter-local contract ladder

Above raw projection soundness, the operational layer exposes a ladder of
adapter-facing contracts. These records are where concrete runtimes discharge
common obligations using their own projected executions.

Important contract definitions are:

- `local_labeled_concrete_projection_sound`
- `local_labeled_concrete_multicore_projection_sound`
- `os_local_multicore_adapter_contract`
- `op_job_visible`
- `labeled_concrete_scheduler_view_contract`
- `labeled_concrete_candidate_source_contract`
- `os_local_candidate_source_adapter_contract`
- `labeled_concrete_admissible_candidate_source_contract`
- `labeled_concrete_strong_admissible_candidate_source_contract`
- `labeled_concrete_single_cpu_scheduler_relation_contract`
- `labeled_concrete_top_m_scheduler_relation_contract`

The intended progression is:

1. project concrete behavior into `OpState` and `OpEvent`,
2. prove local projection soundness,
3. package it as an OS-local adapter contract,
4. expose stronger scheduler-visible or candidate-visible witnesses,
5. then consume those witnesses through scheduler-relation theorem wrappers.

This contract ladder is common. Concrete OS-specific witness construction still
belongs to downstream adapters.

For adapters that rely on emitted trace artifacts, the worker-capacity choice
also belongs here. The common layer proves the generic top-`m` theorem
families, but the adapter decides how its emitted `sched_trace` justifies a
logical worker schedule of capacity `m`, and how that interpretation connects
to scheduler-facing or candidate-source witnesses.

### Delay-aware operational surface

The delay-aware theorem surface is intentionally smaller than the projection
and scheduler-view surfaces.

Its important public names are:

- `op_delay_source`
- `cumulative_delay_budget`

The intended reading is that the common layer exposes only the minimum
accounting vocabulary needed to classify projected delay sources and sum delay
budgets over a labeled execution. It does not yet provide a full interrupt,
timer, or migration semantics.

### Candidate-source reuse over accepted workload families

The current Awkernel minimal stack now includes an adapter-local
candidate-source bridge over the accepted finite-task workload family.

Important definitions and theorems are:

- `accepted_workload_sched_trace_family`
- `accepted_workload_global_fifo_sched_trace_family`
- `accepted_workload_global_fifo_scheduler_relation_family`
- `first_non_scheduler_relation_sched_trace_index`
- `awk_workload_accepts_global_fifo_scheduler_relation_sched_trace`
- `workload_candidate_table_contract`
- `candidate_source_of_table`
- `accepted_workload_candidate_source_family`
- `accepted_workload_candidate_source_sound`
- `accepted_workload_candidate_source_adapter_contract`
- `workload_scheduler_facing_execution_matches_sched_trace`
- `workload_global_fifo_table_witness`
- `accepted_workload_scheduler_facing_family`
- `accepted_workload_scheduler_facing_sound_from_contract`
- `accepted_workload_scheduler_facing_adapter_contract`

The intended progression is:

1. `accepted_workload_sched_trace_family` identifies the accepted
   `task_trace + sched_trace` family,
2. `accepted_workload_global_fifo_sched_trace_family` adds the current
   trace-local `GlobalFIFO` choose-order diagnostic used by the extracted
   Haskell checker over adapter-local choose rows corresponding to projected
   `EvChoose` labels,
3. `accepted_workload_global_fifo_scheduler_relation_family` and
   `awk_workload_accepts_global_fifo_scheduler_relation_sched_trace` add the
   extracted full `GlobalFIFO` scheduler-relation check over the accepted
   emitted `sched_trace`; `first_non_scheduler_relation_sched_trace_index`
   localizes the first failing row,
4. `workload_candidate_table_contract` and `candidate_source_of_table` define
   a proof-side candidate witness over accepted `sched_trace`,
5. `accepted_workload_candidate_source_sound` shows that the accepted family
   plus the candidate-table contract yield
   `labeled_concrete_candidate_source_contract`,
6. `accepted_workload_candidate_source_adapter_contract` packages the result as
   `os_local_candidate_source_adapter_contract`,
7. `workload_scheduler_facing_execution_matches_sched_trace` and
   `workload_global_fifo_table_witness` introduce a proof-side
   scheduler-facing witness over the accepted family,
8. `accepted_workload_scheduler_facing_sound_from_contract` lifts that witness
   to a scheduler-relation contract for `GlobalFIFO` over the adapter-local
   logical worker schedule with capacity `m`; the current Awkernel workload
   path uses the `m = 1` instantiation,
9. `accepted_workload_scheduler_facing_adapter_contract` packages the result
   as the corresponding OS-local scheduler-relation adapter contract,
10. `accepted_workload_scheduler_facing_scheduler_rel` and
    `accepted_workload_scheduler_facing_respects_fifo_policy_at_with`
    consume that package through the common scheduler-relation theorem layer,
    so the current Minimal `m = 1` path already reaches a downstream
    algorithm-facing statement.

This is an adapter-local bridge built on top of the common contract ladder. It
does not widen `Operational/Common`.

Implemented in the current Awkernel minimal accepted-workload path:

- the candidate-source bridge from accepted `task_trace + sched_trace` evidence
  to `labeled_concrete_candidate_source_contract`,
- the scheduler-facing witness bridge from accepted `sched_trace` evidence to
  the common top-`m` scheduler-relation contract,
- and the downstream algorithm-facing `m = 1` scheduler-relation path for
  `GlobalFIFO`.

Still future for this path:

- lifting the accepted-workload bridge to `CandidateSourceSpec`,
- admissibility-aware and strong-admissibility variants,
- multiple-worker (`m > 1`) scheduler-relation reuse as an accepted Awkernel
  workload theorem,
- and bounded-delay or deadline guarantees over the accepted traces.

### Constructor-packaging rule in `Operational/Awkernel/Minimal`

The Awkernel minimal stack uses two intentionally different constructor
families.

Common-layer proof-carrying records use the canonical `mk...` packaging
constructors from `Operational/Common`. Typical examples are:

- `mkOSProjection`
- `mkOSLabeledProjection`
- `mkOSLocalMulticoreAdapterContract`
- `mkLabeledConcreteCandidateSourceContract`
- `mkOSLocalCandidateSourceAdapterContract`
- `mkLabeledConcreteTopMSchedulerRelationContract`
- `mkOSLocalTopMSchedulerRelationAdapterContract`

These are the points where the Awkernel adapter explicitly packages local
proof obligations into the common operational contract ladder.

By contrast, Awkernel-local `mkAwkernel...` constructors remain intentional
direct data constructors. Typical examples are:

- `mkAwkernelState`
- `mkAwkernelSchedTraceEntry`
- `mkAwkernelTaskTraceEntry`
- `mkAwkernelTaskTraceSummary`
- `mkAwkernelSchedTraceAcceptanceState`
- `mkAwkExecution`

These constructors build local syntax, trace entries, summaries, or internal
acceptance state. They do not by themselves establish common operational
contracts.

## Public entry points

The stable public entry point for the OS-neutral operational layer is:

- `theories/Operational/Common/OperationalEntryPoints.v`

Important supporting entry points are grouped by responsibility below.

### Core operational objects

- `theories/Operational/Common/State.v`
- `theories/Operational/Common/Trace.v`
- `theories/Operational/Common/Step.v`
- `theories/Operational/Common/StepLemmas.v`
- `theories/Operational/Common/Execution.v`
- `theories/Operational/Common/LabeledExecution.v`

### Projection and invariants

- `theories/Operational/Common/Projection.v`
- `theories/Operational/Common/ProjectionLemmas.v`
- `theories/Operational/Common/ProjectionInvariants.v`
- `theories/Operational/Common/ProjectionMulticoreValidity.v`

### Delay-aware surface

- `theories/Operational/Common/DelayModel.v`
- `theories/Operational/Common/DelayBudget.v`

### Adapter interfaces and contracts

- `theories/Operational/Common/OSProjectionInterface.v`
- `theories/Operational/Common/ConcreteExecution.v`
- `theories/Operational/Common/OSLocalAdapterContract.v`
- `theories/Operational/Common/OSSchedulerViewContract.v`
- `theories/Operational/Common/OSCandidateSourceContract.v`
- `theories/Operational/Common/OSAdmissibleCandidateSourceContract.v`
- `theories/Operational/Common/OSSchedulerRelationContract.v`

### Awkernel minimal adapter examples

- `theories/Operational/Awkernel/Minimal/MinimalProjection.v`
- `theories/Operational/Awkernel/Minimal/CapturedTraceSyntax.v`
- `theories/Operational/Awkernel/Minimal/WorkloadAcceptance.v`
- `theories/Operational/Awkernel/Minimal/WorkloadAcceptanceExtraction.v`
- `theories/Operational/Awkernel/Minimal/WorkloadCandidateTable.v`
- `theories/Operational/Awkernel/Minimal/WorkloadCandidateSource.v`
- `theories/Operational/Awkernel/Minimal/WorkloadSchedulerFacing.v`
- `theories/Operational/Awkernel/Minimal/MulticoreProjection.v`
- `theories/Operational/Awkernel/Minimal/OperationalMulticoreProjectionExamples.v`

## Design boundaries

### Common layer

The common operational layer defines:

- `OpState`, `OpTrace`, and `OpEvent`,
- common small-step executions and labeled executions,
- projection into semantic schedules,
- projection invariants and multicore-validity bridges,
- and common adapter-facing contract families.

It does not define:

- concrete kernel states,
- concrete emitted traces such as Awkernel `sched_trace` or `task_trace`,
- candidate tables,
- concrete runtime hooks,
- or scheduler-specific implementation logic.

### Adapter layer

The adapter layer connects a concrete runtime to the common operational
vocabulary.

Its responsibilities are:

- instantiate `OSProjection` / `OSLabeledProjection`,
- discharge local projection and multicore obligations,
- construct scheduler-view and candidate-source witnesses from concrete
  observables,
- and package those witnesses into the common adapter contract records.

The current Awkernel minimal modules live here. Their emitted `sched_trace` and
`task_trace` artifacts are adapter-local observables, not common-layer APIs.
Within this layer, explicit common `mk...Contract` constructors are the
canonical packaging points; Awkernel-local `mkAwkernel...` constructors remain
plain data constructors for local emitted artifacts and proof-side state.

### Concrete runtime layer

The concrete runtime layer contains the actual implementation structure:

- task systems,
- queues,
- dispatch paths,
- interrupts,
- timers,
- migration logic,
- trace hooks,
- and extracted acceptance tooling.

This layer may emit runtime observables that adapters later consume, but it
does not define common operational semantics by itself.

## Extension points

The current operational layer is prepared for:

- additional event structures beyond the current payload-carrying `OpEvent`
  vocabulary,
- stronger projection invariants,
- more explicit delay, wakeup, timer, and migration modeling,
- stronger adapter-local bridges beyond the current accepted-workload
  candidate-source, scheduler-facing witness, and `m = 1` scheduler-relation
  path,
- `CandidateSourceSpec` and admissibility-aware accepted-workload packages,
- multiple-worker (`m > 1`) accepted-workload scheduler-relation reuse,
- and bounded-delay or deadline guarantees.

These extensions should preserve the role of `Operational` as the
implementation-facing projection layer rather than redefine schedule meaning
locally.

## File map

### Core state, trace, and step

- `theories/Operational/Common/State.v`
  Core proof-facing scheduler state.
- `theories/Operational/Common/Trace.v`
  Operational traces.
- `theories/Operational/Common/Step.v`
  Common small-step operational relation.
- `theories/Operational/Common/StepLemmas.v`
  Supporting lemmas for the step relation.
- `theories/Operational/Common/Invariants.v`
  Structural invariants over `OpState`.

### Execution and labeled execution

- `theories/Operational/Common/Execution.v`
  Packaged stepwise operational executions.
- `theories/Operational/Common/LabeledExecution.v`
  Executions with per-step observable events.

### Delay model and budget

- `theories/Operational/Common/DelayModel.v`
  Common delay-source vocabulary and default event classification.
- `theories/Operational/Common/DelayBudget.v`
  Cumulative delay-budget accounting lemmas over delay-source traces.

### Projection and soundness

- `theories/Operational/Common/OSProjectionInterface.v`
  OS-neutral projection from concrete machine state to `OpState`.
- `theories/Operational/Common/ConcreteExecution.v`
  Wrapper that packages projected concrete traces as common operational
  executions.
- `theories/Operational/Common/Projection.v`
  Projection from operational traces to semantic schedules.
- `theories/Operational/Common/ProjectionLemmas.v`
  Projection soundness lemmas linking operational traces to semantic validity.

### Multicore bridge and adapter contracts

- `theories/Operational/Common/ProjectionInvariants.v`
  Operational range and placement invariants used by the multicore bridge.
- `theories/Operational/Common/ProjectionMulticoreValidity.v`
  Bridge lemmas from operational projection to `Multicore/Common`.
- `theories/Operational/Common/OSLocalAdapterContract.v`
  Local projection and multicore adapter contracts over concrete executions.
- `theories/Operational/Common/OSSchedulerViewContract.v`
  Scheduler-visible job contracts over projected executions.
- `theories/Operational/Common/OSCandidateSourceContract.v`
  Candidate-source contracts over projected executions.
- `theories/Operational/Common/OSAdmissibleCandidateSourceContract.v`
  Admissibility-aware candidate-source contract refinements.
- `theories/Operational/Common/OSSchedulerRelationContract.v`
  Scheduler-relation contracts from projected executions to generic
  algorithms.

### Awkernel minimal adapter boundary

- `theories/Operational/Awkernel/Minimal/MinimalProjection.v`
  Reusable Awkernel adapter boundary over the common projection slice.
- `theories/Operational/Awkernel/Minimal/CapturedTraceSyntax.v`
  Captured-entry syntax used by the Awkernel minimal-example stack; this module
  intentionally defines local data constructors rather than common contract
  packaging.
- `theories/Operational/Awkernel/Minimal/WorkloadAcceptance.v`
  Adapter-local accepted workload-family checker.
- `theories/Operational/Awkernel/Minimal/WorkloadAcceptanceExtraction.v`
  Extraction entry point for the workload checker.
- `theories/Operational/Awkernel/Minimal/WorkloadCandidateTable.v`
  Proof-side candidate-table contract for accepted `sched_trace`.
- `theories/Operational/Awkernel/Minimal/WorkloadCandidateSource.v`
  Adapter-local candidate-source reuse bridge over the accepted workload
  family; this is one of the canonical examples of explicit
  `mk...Contract`/`mk...AdapterContract` packaging in the Awkernel minimal
  layer.
- `theories/Operational/Awkernel/Minimal/WorkloadSchedulerFacing.v`
  Adapter-local scheduler-facing witness bridge from the accepted workload
  family to the common top-`m` scheduler-relation contract; this also uses the
  explicit common packaging constructors.
- `theories/Operational/Awkernel/Minimal/MulticoreProjection.v`
  Thin 2-CPU Awkernel-facing entry point for the multicore projection bridge.
- `theories/Operational/Awkernel/Minimal/OperationalMulticoreProjectionExamples.v`
  Worked 2-CPU examples layered on top of the minimal Awkernel boundary.

## Summary

The operational layer is the implementation-facing projection layer of the
repository.

Its current guarantee boundary is:

- common operational scheduler views and traces,
- projection into semantic schedules,
- multicore validity and placement recovery from explicit invariants,
- the common adapter contract ladder for projection, scheduler visibility,
  candidate visibility, handoff, admissibility, scheduler relations, algorithm
  adapters, and delay adapters,
- and adapter-local Awkernel minimal accepted-workload bridges up through
  candidate-source reuse, scheduler-facing witnesses, and the current `m = 1`
  scheduler-relation path.

It should still be documented as an OS-neutral projection layer, not as a full
concrete OS semantics or a complete refinement closure.
