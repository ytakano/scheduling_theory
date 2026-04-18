# Uniprocessor

## Scope

This document describes the uniprocessor specialization layer.

Its scope is:

- `theories/Uniprocessor/Core/*`
- `theories/Uniprocessor/Generic/*`
- `theories/Uniprocessor/Policies/*`

This layer specializes the generic scheduler abstractions to the single-CPU case and organizes the reusable finite-horizon optimality pipeline together with the concrete policy families built on top of it.

## Purpose of the Uniprocessor layer

The uniprocessor layer explains how single-CPU scheduling theory is structured in the repository.

Its responsibilities are:

- packaging a verified single-CPU scheduler from a concrete choose function and an abstract policy spec,
- exposing generic finite-prefix witness construction,
- defining canonicality, normalization, truncation, and finite optimality infrastructure for single-CPU policies,
- organizing policy modules such as EDF, LLF, FIFO, and RR without collapsing them into the abstraction layer.

The layer is constructive-first. Its generic normalization interfaces rely on explicit decidability and local repair obligations rather than classical choice.

## Core organization

The layer is organized into three parts.

`Uniprocessor/Core`
- bundle and bridge layer that packages concrete choose functions, candidate sources, and abstract policy specs into verified single-CPU schedulers

`Uniprocessor/Generic`
- finite-prefix witness construction
- canonicality predicates and finite deadline horizons
- generic repair/normalization interface
- truncation preservation and finite optimality skeleton

`Uniprocessor/Policies`
- concrete policies and their policy-facing invariants
- EDF and LLF canonicality/repair/optimality instantiations
- FIFO and RR wrapper-style policies
- thin uniprocessor-facing re-export wrappers for the metric chooser layer

For the detailed mechanics of horizon, canonicality, repair, and normalization, the primary supplemental note remains:

- `design/GenericUniprocessorOptimality.md`

This document summarizes the current public surface of that pipeline rather than duplicating its full derivation.

## Core layer

### `UniSchedulerInterface.v`

The core interface is built around:

```coq
Class HasGenericSchedulingAlgorithm (Spec : Type)
Record UniSchedulerBundle
```

`HasGenericSchedulingAlgorithm` is a projection typeclass from a scheduler-specific spec type to `GenericSchedulingAlgorithm`.

`UniSchedulerBundle J Spec` packages:

- `usb_candidates : CandidateSource`
- `usb_spec : Spec`
- `usb_candidates_ok : CandidateSourceSpec J usb_candidates`
- `usb_alg_spec : SchedulingAlgorithmSpec`
- `usb_alg_spec_sane : SchedulingAlgorithmSpecSanity usb_alg_spec`
- `usb_algorithm_refines : algorithm_refines_spec (to_generic_scheduling_algorithm usb_spec) usb_alg_spec`

So the bundle is the minimal verified package needed to turn a concrete chooser plus candidate-source discipline into a verified single-CPU scheduler.

### `UniSchedulerLemmas.v`

This file provides the standard derived entry points:

```coq
uni_scheduler_on : ... -> Scheduler
uni_policy_scheduler_on : ... -> Scheduler
```

and the main bridge lemmas:

- `uni_scheduler_on_valid`
- `uni_scheduler_on_refines_policy`
- `uni_scheduler_on_schedulable_by_on_intro`

The role of the core layer is therefore not just "single-CPU interfaces", but specifically the bridge from bundled concrete algorithms to valid and schedulable single-CPU schedulers.

## Generic layer

### `FinitePrefixScheduleWitness.v`

This file constructs the canonical generated schedule induced by a scheduling algorithm and candidate source.

Its main definitions are:

```coq
generated_schedule_prefix :
  GenericSchedulingAlgorithm -> CandidateSource -> (JobId -> Job) -> Time -> Schedule
generated_schedule :
  GenericSchedulingAlgorithm -> CandidateSource -> (JobId -> Job) -> Schedule
```

The prefix schedule explicitly builds the first `H` slots; the full generated schedule is the pointwise wrapper around it.

Key lemmas and theorems include:

- `generated_schedule_prefix_stable`
- `generated_schedule_prefix_agrees_before`
- `generated_schedule_eq_cpu0_with_prefix`
- `generated_schedule_other_cpu_idle`
- `generated_schedule_scheduler_rel`
- `scheduler_rel_agrees_with_generated_schedule_prefix`
- `scheduler_rel_agrees_with_generated_schedule_before`
- `schedulable_by_on_implies_generated_schedule_feasible`

So this file is the finite-prefix witness construction layer used when turning an abstract scheduler relation into an explicit generated schedule.

### `SchedulingAlgorithmCanonicalBridge.v`

This file defines the generic notion of canonicality with respect to a scheduling algorithm:

```coq
matches_choose_at_with :
  GenericSchedulingAlgorithm ->
  (JobId -> Job) ->
  CandidateSource ->
  Schedule ->
  Time -> Prop

matches_choose_before :
  GenericSchedulingAlgorithm ->
  (JobId -> Job) ->
  CandidateSource ->
  Schedule ->
  Time -> Prop
```

It also defines the finite horizon used by the generic pipeline:

```coq
deadline_horizon : (JobId -> Job) -> list JobId -> nat
```

and proves the main horizon lemmas:

- `in_enum_implies_deadline_lt_horizon`
- `J_implies_deadline_lt_horizon`
- `J_implies_deadline_le_horizon`
- `J_jobs_complete_at_or_after_deadline`
- `J_jobs_not_eligible_at_horizon`

The main bridge theorem is:

- `canonical_and_idle_implies_scheduler_rel_generic`

This theorem is the generic step that turns a finite-horizon canonical schedule, plus idleness after the horizon, into a `scheduler_rel` witness.

### `SchedulingAlgorithmNormalization.v`

This file defines the generic constructive repair interface:

```coq
Record CanonicalRepairSpec ...
Definition ChooseAgreesBefore ...
```

`CanonicalRepairSpec` packages:

- a policy-specific `canonical_at`
- a policy-specific `canonical_before`
- equivalence with generic `matches_choose_*`
- a decidability proof for one-step canonicality
- a one-step local repair lemma that preserves validity, feasibility, J-only execution, single-CPU shape, and prefix agreement

`ChooseAgreesBefore` is the prefix-extensionality condition for the scheduling algorithm:

- if two schedules agree before `t`, then the algorithm makes the same choice at `t`

The main generic lemmas are:

- `repair_pushes_forward_generic`
- `normalize_to_canonical_generic`

This is the central reusable normalization layer. Policy files instantiate it by supplying only the canonicality predicate, its decider, the local repair theorem, and the choose-prefix-agreement lemma.

### `ScheduleTruncationPreservation.v`

This file packages the one-CPU preservation facts needed after normalization:

- `trunc_sched_single_cpu_only`
- `trunc_sched_valid`
- `trunc_sched_feasible`
- `trunc_sched_preserves_canonical_before`

Its role is to support the finite-horizon pipeline after a schedule has been normalized on the relevant prefix.

### `SchedulingAlgorithmOptimalitySkeleton.v`

This file packages the generic finite optimality pipeline into explicit stages.

The main lemmas are:

- `finite_J_restricted_schedule`
- `finite_normalized_schedule`
- `finite_truncated_schedule`
- `finite_canonical_schedule_yields_scheduler_rel`

and the final theorem is:

- `finite_optimality_via_normalization`

The pipeline structure is:

1. extract a valid single-CPU witness schedule restricted to the target job set `J`
2. normalize that witness so it matches the scheduling algorithm on the finite prefix
3. truncate at the deadline horizon
4. convert the canonical truncated schedule into `scheduler_rel`
5. derive `schedulable_by_on`

This is the generic uniprocessor finite-optimality skeleton reused by EDF and LLF.

## Policy layer

### Metric chooser wrappers

`theories/Uniprocessor/Policies/Common/MetricChooser.v` and `MetricChooserLemmas.v` are currently thin re-export wrappers:

- `MetricChooser.v` re-exports `Abstractions.SchedulingAlgorithm.Common.MetricChooser`
- `MetricChooserLemmas.v` re-exports `Abstractions.SchedulingAlgorithm.Common.MetricChooserLemmas`

So this directory is not an independent implementation layer; it is the uniprocessor-facing entry point for the common metric chooser infrastructure used by EDF and LLF.

### EDF

`EDF.v` defines the static metric and chooser:

- `edf_metric`
- `choose_edf`
- `edf_generic_spec`

It also defines the EDF-specific richer spec:

```coq
Record EDFSchedulerSpec
```

carrying the minimum-deadline invariant, and packages:

- `edf_scheduler_spec`
- `edf_policy`
- `edf_policy_sane`
- `choose_edf_refines_edf_policy`
- `edf_bundle`
- `edf_scheduler_on`
- `edf_policy_scheduler_on`
- `edf_scheduler`

`EDFLemmas.v` adds policy-facing canonicality and violation structure:

- `matches_choose_edf_at`, `matches_choose_edf_at_with`, `matches_choose_edf_before`
- `respects_edf_priority_at`, `respects_edf_priority_at_on`
- `edf_violation_at`, `edf_violation_at_in`, `edf_violation_at_with`
- boolean violation detectors `edf_violationb_in`, `edf_violationb_at_with`
- prefix agreement lemmas such as `choose_edf_agrees_before`, `edf_choose_agrees_before`
- canonicality consequences such as `matches_choose_edf_at_with_no_earlier_eligible_job`

`EDFTransform.v` contains EDF-specific local repair helpers:

- `first_violation_has_repair_witness`
- `first_violation_yields_canonical_repair_job`
- `repair_first_violation`

`EDFOptimality.v` packages EDF into the generic repair interface:

- `is_canonical_at_b`
- `edf_canonical_at_dec`
- `repair_non_canonical_at`
- `EDFCanonicalRepairSpec`
- `edf_normalize_to_canonical`
- `edf_optimality_on_finite_jobs`

So EDF is not just a chooser plus wrapper theorem. It is a full finite-optimality-ready policy with dedicated canonicality, violation, and one-step repair layers.

### LLF

`LLF.v` defines the dynamic metric and chooser:

- `llf_metric`
- `choose_llf`
- `llf_generic_spec`

The metric is schedule-dependent:

- `llf_metric jobs m sched t j := laxity jobs m sched j t`

The file also defines:

- `choose_llf_min_laxity`
- `llf_policy`
- `llf_policy_sane`
- `choose_llf_refines_llf_policy`
- `LLFSchedulerSpec`
- `llf_scheduler_spec`
- `llf_bundle`
- `llf_scheduler_on`
- `llf_policy_scheduler_on`
- `llf_scheduler`

`LLFLemmas.v` provides the LLF canonicality and violation layer:

- `matches_choose_llf_at`, `matches_choose_llf_at_with`, `matches_choose_llf_before`
- `is_llf_canonical_at_b`
- `choose_llf_agrees_before`, `llf_choose_agrees_before`
- `respects_llf_priority_at_on`
- `llf_violation_at_in`, `llf_violation_at_with`
- `matches_choose_llf_at_with_no_lower_laxity_eligible_job`
- `matches_choose_llf_at_with_implies_respects_llf_priority_at_on`
- `canonical_non_llf_step_has_other_min_or_better_eligible_job`

`LLFTransform.v` contains the LLF-specific repair layer. It is more laxity-aware than EDF and includes:

- `llf_candidate_runs_before_both_deadlines`
- `swap_at_preserves_feasible_schedule_on_before_both_deadlines`
- `repair_non_canonical_at_llf_common`
- `repair_non_canonical_at_llf_tie`
- `repair_non_canonical_at_llf_strict`
- `repair_non_canonical_at_llf`

`LLFOptimality.v` then packages LLF into the generic normalization interface:

- `llf_canonical_at_dec`
- `LLFCanonicalRepairSpec`
- `llf_normalize_to_canonical`
- `llf_optimality_on_finite_jobs`

So LLF is also finite-optimality-ready, but unlike EDF its policy-specific repair logic depends on schedule-sensitive laxity arguments.

### FIFO

`FIFO.v` defines:

- `choose_fifo`
- `fifo_generic_spec`
- `choose_fifo_first_eligible`
- `fifo_policy`
- `fifo_policy_sane`
- `choose_fifo_refines_fifo_policy`
- `fifo_bundle`
- `fifo_scheduler`
- `fifo_scheduler_on`
- `fifo_policy_scheduler_on`

The chooser simply returns the first eligible job in candidate order.

So FIFO is currently a wrapper-style policy: the candidate list order carries the intended FIFO discipline, and the file packages that discipline into the standard bundle and policy-refinement interfaces. It is not currently instantiated into the generic finite-optimality pipeline.

### Round Robin

`RoundRobin.v` has the same first-eligible chooser shape as FIFO:

- `choose_rr`
- `rr_generic_spec`
- `choose_rr_first_eligible`
- `rr_policy`
- `rr_policy_sane`
- `choose_rr_refines_rr_policy`
- `rr_bundle`
- `rr_scheduler`
- `rr_scheduler_on`
- `rr_policy_scheduler_on`

The important design note is that Round Robin queue rotation is not implemented inside the chooser. Instead:

- the candidate list order supplied by `CandidateSource` already encodes the current RR wheel state
- the chooser only selects the first eligible job in that supplied order
- unit quantum (`q = 1`) is assumed by the surrounding design note

So RR is intentionally a wrapper-style policy whose semantics live primarily in the `CandidateSource`, not in additional repair or optimality machinery.

## Public entry points

The stable public entry points for this layer are:

- `theories/Uniprocessor/Core/UniSchedulerInterface.v`
- `theories/Uniprocessor/Core/UniSchedulerLemmas.v`
- `theories/Uniprocessor/Generic/FinitePrefixScheduleWitness.v`
- `theories/Uniprocessor/Generic/SchedulingAlgorithmCanonicalBridge.v`
- `theories/Uniprocessor/Generic/SchedulingAlgorithmNormalization.v`
- `theories/Uniprocessor/Generic/ScheduleTruncationPreservation.v`
- `theories/Uniprocessor/Generic/SchedulingAlgorithmOptimalitySkeleton.v`
- `theories/Uniprocessor/Policies/EDF.v`
- `theories/Uniprocessor/Policies/EDFLemmas.v`
- `theories/Uniprocessor/Policies/EDFTransform.v`
- `theories/Uniprocessor/Policies/EDFOptimality.v`
- `theories/Uniprocessor/Policies/LLF.v`
- `theories/Uniprocessor/Policies/LLFLemmas.v`
- `theories/Uniprocessor/Policies/LLFTransform.v`
- `theories/Uniprocessor/Policies/LLFOptimality.v`
- `theories/Uniprocessor/Policies/FIFO.v`
- `theories/Uniprocessor/Policies/RoundRobin.v`
- `theories/Uniprocessor/Policies/Common/MetricChooser.v`
- `theories/Uniprocessor/Policies/Common/MetricChooserLemmas.v`

In practice:

- downstream generic work should import the `Generic/*` modules directly
- downstream policy work should import the relevant policy file plus its lemma/optimality wrappers when needed
- `MetricChooser*.v` should be treated as re-export convenience entry points rather than standalone implementations

## Design boundaries

This layer includes:

- single-CPU specialization of scheduler/algorithm abstractions,
- bundle-based construction of verified uniprocessor schedulers,
- generic canonicalization, normalization, truncation, and finite-optimality infrastructure,
- concrete single-CPU policy modules and their local theorem layers.

This layer does not include:

- the core semantic meaning of schedules,
- the most general scheduler and algorithm interfaces,
- task-generation semantics,
- analysis-specific theorem layers as the primary concern,
- operational or implementation-facing scheduler traces.

Those belong respectively to:

- `design/Semantics.md`
- `design/Abstractions.md`
- `design/TaskModels.md`
- `design/Analysis.md`
- `design/Operational.md`

## Extension points

The current design is intended to support:

- new single-CPU policies that reuse `CanonicalRepairSpec` and `finite_optimality_via_normalization`,
- richer metric-based chooser clients,
- additional finite-optimality-ready policy instantiations beyond EDF and LLF,
- stronger public theorem inventories with stable naming across task-model lifts.

New policy work should prefer plugging into the generic repair/normalization pipeline rather than reproducing horizon, truncation, or schedulability packaging arguments inside each policy file.

## File map

- `theories/Uniprocessor/Core/UniSchedulerInterface.v`
  Typeclass projection plus `UniSchedulerBundle`, the core package for verified single-CPU schedulers.
- `theories/Uniprocessor/Core/UniSchedulerLemmas.v`
  Derived scheduler and policy wrappers plus validity, refinement, and `schedulable_by_on` introduction lemmas.
- `theories/Uniprocessor/Generic/FinitePrefixScheduleWitness.v`
  Explicit generated-schedule construction and finite-prefix witness theorems.
- `theories/Uniprocessor/Generic/SchedulingAlgorithmCanonicalBridge.v`
  Canonicality predicates, deadline horizon, and the generic "canonical plus idle implies scheduler relation" bridge.
- `theories/Uniprocessor/Generic/SchedulingAlgorithmNormalization.v`
  Constructive repair interface and generic finite-horizon normalization theorem.
- `theories/Uniprocessor/Generic/ScheduleTruncationPreservation.v`
  One-CPU truncation preservation lemmas used by the optimality pipeline.
- `theories/Uniprocessor/Generic/SchedulingAlgorithmOptimalitySkeleton.v`
  Generic finite-optimality pipeline from feasible witness to `schedulable_by_on`.
- `theories/Uniprocessor/Policies/Common/MetricChooser.v`
  Re-export wrapper for the common metric chooser definitions.
- `theories/Uniprocessor/Policies/Common/MetricChooserLemmas.v`
  Re-export wrapper for the common metric chooser lemmas.
- `theories/Uniprocessor/Policies/EDF*.v`
  EDF chooser, EDF-specific scheduler spec, canonicality/violation layer, repair lemmas, and finite optimality wrapper.
- `theories/Uniprocessor/Policies/LLF*.v`
  LLF chooser, LLF-specific scheduler spec, canonicality/violation layer, laxity-aware repair lemmas, and finite optimality wrapper.
- `theories/Uniprocessor/Policies/FIFO.v`
  First-eligible-in-order wrapper policy for FIFO-style candidate ordering.
- `theories/Uniprocessor/Policies/RoundRobin.v`
  First-eligible-in-order wrapper policy for RR-ordered candidate sources, with queue rotation encoded outside the chooser.

## Summary

The uniprocessor layer is the bridge from generic scheduler abstractions to concrete verified single-CPU policy results.

Its main architectural rule is to keep bundle construction, canonicalization, normalization, truncation, and finite-optimality packaging in `Core/*` and `Generic/*`, while policy files contribute only the policy-specific chooser invariants, canonicality predicates, and local repair arguments they need. In the current implementation, EDF and LLF are finite-optimality-ready policies, while FIFO and RR remain intentionally wrapper-style policies built around candidate ordering.
