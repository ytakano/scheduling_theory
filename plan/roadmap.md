# New Roadmap

## 0. Current Position

This project is not merely a schedulability-analysis library.
Its core is a Rocq formalization centered on:

- executable scheduler semantics
- scheduling-algorithm refinement
- reusable uniprocessor theory
- extension toward multicore and OS-level semantics
- analysis layered on top of those semantics

### Already implemented

- common schedule / service / feasibility / scheduler interface
- generic scheduling-algorithm abstraction
- generic canonical bridge
- generic normalization skeleton
- generic finite optimality skeleton
- uniprocessor policies:
  - FIFO
  - Round Robin
  - EDF
  - LLF
- EDF finite optimality
- LLF finite optimality pipeline
- partitioned scheduling core
- partitioned EDF / FIFO / RR / LLF wrappers
- partitioned finite-job optimality lift
- initial periodic-task layer
- initial multicore-common layer
- initial global EDF layer
- initial global LLF layer

### Interpretation of the current state

The project is no longer in the phase of “building the first uniprocessor core.”
That part is mostly done.

The next work is mainly:

1. stabilize and document the reusable uniprocessor core
2. turn partitioned multicore into a mature theorem layer
3. grow multicore-common semantics beyond the current base layer
4. strengthen the initial global theorem layers
5. introduce delay-aware operational and analysis layers without polluting the core schedule semantics
6. add standard real-time analysis foundations such as busy windows, demand/supply abstractions, and policy comparison metrics

### Design principle for delay modeling

Delay should not be baked into the core `Schedule` semantics.

Instead:

- the abstract schedule remains the clean semantic core
- task-generation layers model release-side variability such as jitter
- OS-operational layers model timer / wakeup / dispatch / migration delays
- refinement theorems connect operational behavior to abstract schedules
- analysis theorems consume explicit delay bounds as parameters
- the idealized zero-delay model remains available as a special case

### Design principle for analysis growth

Analysis should be introduced in layers.

- first, define semantic invariants and reusable counting/service lemmas
- next, define analysis foundations such as busy intervals and demand/supply functions
- then, prove idealized schedulability and response-time theorems
- finally, add blocking, suspension, limited preemption, and operational overheads

This keeps the semantic core reusable while still allowing standard scheduling-theory results to be mechanized.

### Practical validation strategy

The project should separate two goals clearly:

- **refinement completion on a designable OS**
- **external applicability demonstration on existing OSes**

Awkernel is designable together with the formal model, so it is the right place to complete
the end-to-end refinement story:

- scheduling algorithm
- scheduler semantics
- OS-operational semantics
- refinement from implementation-oriented behavior to abstract schedule semantics

For **Linux**, the near-term goal should be different.
Rather than attempting full refinement first, the project should use **trace-based validation**
to show that the abstract theory and delay-aware models can be applied externally to a real,
existing OS whose full internal design is not controlled by this project.

This yields a two-track validation strategy:

1. **Awkernel** as the primary target for completed refinement verification
2. **Linux** as the primary target for trace-based external validation

---

## 1. Phase A: Stabilize the reusable uniprocessor core
**Status: In progress, but largely implemented**

This phase is mostly about turning the existing EDF/LLF/FIFO/RR development into
a clearly reusable theory core.

### A-1. Generic canonicalization layer
**Status: Mostly done**

Implemented core:

- `SchedulingAlgorithmCanonicalBridge.v`
- `SchedulingAlgorithmNormalization.v`
- `SchedulingAlgorithmOptimalitySkeleton.v`

What is already done:

- generic canonical bridge exists
- generic normalization skeleton exists
- finite optimality skeleton exists
- EDF and LLF both instantiate the pipeline

What remains:

- make the generic/policy-specific boundary more explicit
- document `CanonicalRepairSpec`
- document `ChooseAgreesBefore`
- keep design documents synchronized with the code

### A-2. Metric-based chooser layer
**Status: Partially done**

Implemented core:

- `Uniprocessor/Policies/Common/MetricChooser.v`
- `Uniprocessor/Policies/Common/MetricChooserLemmas.v`
- EDF / LLF chooser-related files

What is already done:

- practical chooser infrastructure exists
- EDF and LLF already serve as static/dynamic metric examples

What remains:

- clearly separate static metric vs dynamic metric
- make the interface-level story cleaner
- prepare the path for future metric-based policies

### A-3. Inventory of uniprocessor results
**Status: Not yet finished**

What remains:

- rewrite `what_to_prove.md`
- classify results into:
  - definition
  - local properties
  - local repair
  - normalization
  - optimality
- clearly mark:
  - done
  - partially done
  - not started

---

## 2. Phase B: Task-generation layer
**Status: Partially done**

This phase should come earlier than in the old roadmap, because the current code
already contains task/job structure and an initial periodic layer.

### B-1. Periodic tasks
**Status: Finite-horizon bridge, partitioned lift, and workload hooks done**

Implemented core:

- `Base.v` already contains task-related fields
- `PeriodicTasks.v`: expected release, expected deadline,
  generated-by-periodic-task predicate, periodic-job-model predicates,
  implicit-deadline task predicate, basic consistency lemmas
- `PeriodicFiniteHorizon.v`: `periodic_jobset_upto` with bool reflection
- `PeriodicEnumeration.v`: `PeriodicFiniteHorizonCodec`, `enum_periodic_jobs_upto`
  — sound and complete codec-based job enumeration for finite horizons
- `PeriodicFiniteOptimalityLift.v` (new): generic uniprocessor periodic
  finite-optimality theorem; abstracts over any policy satisfying the
  standard `finite-optimality` contract
- `PeriodicEDFBridge.v`: thin EDF wrapper over `PeriodicFiniteOptimalityLift`
- `PeriodicLLFBridge.v`: thin LLF wrapper over `PeriodicFiniteOptimalityLift`
- `PeriodicPartitionedFiniteOptimalityLift.v` (new): connects periodic
  task generation to `partitioned_scheduler` via `partitioned_finite_optimality_lift`
- `PeriodicWorkload.v`: finite-horizon per-task count/workload bounds for
  explicit job lists, intended as analysis hooks on top of the periodic model

What remains:

- sporadic task-generation layer
- utilization / Liu & Layland style theorems
- release-pattern foundation now lives in `PeriodicReleaseLemmas.v`
  and should be reused by sporadic/jitter extensions

### B-2. Sporadic tasks
**Status: Finite-horizon witness layer and workload hooks implemented**

Implemented:

- `SporadicTasks.v`: `unique_task_index_on`, `sporadic_separation_on`,
  `sporadic_job_model_on`, `earliest_sporadic_release`,
  `generated_by_sporadic_task`, `generated_by_sporadic_task_b`
- `TaskModels/Common/FiniteHorizonWitness.v`,
  `TaskModels/Common/WitnessCandidates.v`,
  `TaskModels/Common/WitnessFiniteOptimalityLift.v`: shared witness API for
  manual finite-horizon enumeration and scheduler lifting
- `SporadicFiniteHorizon.v`: `sporadic_jobset_upto` updated to use
  `generated_by_sporadic_task`; boolean reflection updated;
  finite-horizon release/index bound lemmas added
- `SporadicWorkload.v`: finite-horizon per-task job-count / cumulative-workload
  bounds for explicit job lists under uniqueness and separation assumptions
- `SporadicEnumeration.v`: specialization of the shared witness API to
  `sporadic_jobset_upto`; intentionally not an automatic codec
- `SporadicPeriodicBridge.v`: `generated_by_periodic_implies_sporadic`,
  `periodic_model_satisfies_separation`, `periodic_model_implies_sporadic_model`
- EDF / LLF / partitioned lift bridges: witness-based entry points for the
  sporadic finite-horizon API

What remains:

- utilization / Liu & Layland style theorems
- stronger analysis results beyond the finite-horizon witness pipeline

Design note:

- sporadic still has no automatic codec because releases are not determined by
  `(task, index)` alone
- the intended finite-horizon abstraction is a manual witness record carrying
  `enumJ` plus soundness/completeness proofs
- the witness pipeline and the analysis-hook layer are intentionally separate:
  witnesses enumerate concrete finite horizons, while workload lemmas give
  reusable count / WCET bounds over explicit finite job lists

### B-3. Release jitter / arrival offsets
**Status: Initial jittered-periodic layer implemented**

Implemented:

- `TaskModels/Jitter/ReleaseJitter.v`: reusable `within_jitter` predicate,
  boolean reflection, lower/upper-bound lemmas
- `JitteredPeriodicTasks.v`: bounded-release periodic generation predicate,
  boolean reflection, local deadline/cost lemmas, periodic-to-jitter inclusion
- `JitteredPeriodicSporadicBridge.v`: per-job bridge to sporadic generation,
  model-level bridge when task scope, uniqueness, and separation are supplied
- `JitteredPeriodicFiniteHorizon.v` and `JitteredPeriodicEnumeration.v`:
  witness-based finite-horizon jobset API specialized from the shared witness
  abstraction
- `JitteredPeriodicFiniteOptimalityLift.v`: wrapper over the shared
  finite-horizon witness lift
- `JitteredPeriodicEDFBridge.v`, `JitteredPeriodicLLFBridge.v`,
  `JitteredPeriodicPartitionedFiniteOptimalityLift.v`: EDF / LLF /
  partitioned theorem wrappers
- `Examples/JitteredPeriodicExamples.v`: manual witness example with delayed
  releases and schedulability proofs

Design note:

- jitter is kept in the task-generation layer and does not modify `Schedule`
- no automatic codec is introduced, because actual releases are not recovered
  from `(task, index)` alone
- promotion to the full sporadic model still requires an explicit
  `sporadic_separation_on` assumption; bounded delay jitter alone does not
  imply actual-release separation

### B-4. Why this phase is early
**Status: Design decision**

Task-generation models that preserve the job-level semantic core should be added
before deeper multicore extensions.
This matches the current implementation better than pushing them to a very late phase.

---

## 3. Phase C: Partitioned multicore as a mature theorem layer
**Status: Core theorem layer implemented; stabilization and documentation in progress**

Implemented core:

- `Partitioned.v`
- `PartitionedCompose.v`
- `Multicore/Partitioned/Policies/PartitionedEDF.v`
- `Multicore/Partitioned/Policies/PartitionedFIFO.v`
- `Multicore/Partitioned/Policies/PartitionedRR.v`
- `Multicore/Partitioned/Policies/PartitionedLLF.v`
- `Multicore/Partitioned/Policies/PartitionedFiniteOptimalityLift.v`

### C-1. Partitioned construction and compose layer
**Status: Done as a reusable generic entry-point layer**

What is already done:

- partitioned scheduler construction exists
- local-to-global schedule gluing exists
- local witness -> partitioned schedulable-by lifting exists
- policy-specific partitioned wrappers exist

What remains:

- better separate:
  - assignment-respect
  - local scheduler validity
  - global schedule validity
  in documentation and public-inventory terms

### C-2. Partitioned policy lifting
**Status: Done for EDF / FIFO / RR / LLF, with light cleanup remaining**

What is already done:

- EDF / FIFO / RR / LLF wrappers all exist

What remains:

- keep the wrapper files thin and explicit about their role
- document that EDF / LLF include finite-optimality-based entry theorems
- document that FIFO / RR are intentionally wrapper-only for now

### C-3. Partitioned schedulability lifting
**Status: Done for EDF / LLF finite-optimality lifting**

What is already done:

- the main entry points for lifting local schedulability already exist
- `PartitionedFiniteOptimalityLift.v` provides a reusable finite-job lift
  instantiated today by partitioned EDF and partitioned LLF
- existing examples already demonstrate partitioned major results for the
  generic, periodic, sporadic, and jittered-periodic paths

What remains:

- make the intended reusable theorem inventory explicit in the roadmap and docs
- prepare the interface for later delay-aware partitioned analysis

---

## 4. Phase D: Multicore-common semantics
**Status: Affinity layer added**

Implemented core:

- `MultiCoreBase.v`
- `Admissibility.v`
- `AffinityFacts.v`
- `AdmissibleCandidateSource.v`
- `TopMAdmissibilityBridge.v`

What is already done:

- per-CPU view of global schedule
- no-duplication aliasing / bridge
- idle / busy predicates
- globally-runnable notions
- bridge lemmas connecting multicore notions to the existing schedule model
- `all_cpus_admissible` and `singleton_admissibility` concrete instances
- general `cpu_affinity` / `affinity_admissibility` / `job_has_admissible_cpu` layer
- equational embedding: both concrete instances are special cases of `affinity_admissibility`
- `AdmissibleCandidateSourceSpec`: admissibility-aware completeness spec
- `StrongAdmissibleCandidateSourceSpec`: stronger variant requiring every candidate to be admissible somewhere
- `TopMAdmissibilityBridge`: policy-generic admissibility theorem layer

What remains:

- multicore validity beyond the current minimal base
- stronger service / completion lemmas under migration beyond the initial
  common bridge layer
- abstractions for top-m and non-partitioned selection
- API stabilization: clarify public API vs helper lemma boundary in the bridge
- richer affinity/candidate-source instantiation examples

Newly implemented in the initial common bridge layer:

- `Multicore/Common/ServiceFacts.v`: migration-aware decomposition of
  `service_job` into the sum of per-CPU projected services
- `Multicore/Common/CompletionFacts.v`: completion and eligibility bridges
  stated in terms of the decomposed multicore service

---

## 5. Phase E: Global / clustered scheduling
**Status: Initial global layer started**

### E-1. Global scheduling
**Status: Initial global EDF/LLF theorem layers done**

What is already done:

- `TopMSchedulerBridge.v` provides the generic top-`m` scheduler bridge
- `TopMAdmissibilityBridge.v` provides policy-generic admissibility lemmas
- `GlobalEDF.v` provides:
  - `global_edf_scheduler`
  - `global_edf_valid`
  - `global_edf_idle_outside_range`
  - `global_edf_no_duplication`
  - subset-aware theorem entry points
  - admissibility-aware wrappers
- `GlobalLLF.v` provides:
  - `global_llf_scheduler`
  - `global_llf_valid`
  - `global_llf_idle_outside_range`
  - `global_llf_no_duplication`
  - subset-aware theorem entry points
  - admissibility-aware wrappers

What remains:

- connect the global theorem layer to later analysis results
- tighten theorem inventory documentation for downstream analysis use
- identify which global EDF / LLF facts should be lifted to policy-generic layers
- richer candidate-source instantiation examples

### E-2. Clustered scheduling
**Status: Not started**

Planned:

- cluster-local global semantics
- bridge between partitioned and fully global scheduling

### E-3. Global dynamic-metric policies
**Status: Initial layer exists**

Planned:

- strengthen global LLF theorem inventory
- prepare migration-aware dynamic-metric reasoning

---

## 6. Phase F: DAG / structured-parallel task semantics
**Status: Not started**

DAG tasks should not be treated as just another release-pattern extension.
They change the internal execution structure of a job.

Planned:

- node-level readiness
- precedence constraints
- node-level service / completion
- connection back to job-level scheduling semantics

This phase should come after multicore-common semantics and after the first
global-scheduling layer, not alongside periodic tasks.

---

## 7. Phase G: Analysis foundations
**Status: In progress**

This phase collects standard abstractions from scheduling theory that should be reusable
across idealized, delay-aware, uniprocessor, and multicore analyses.

### G-1. Busy-window / busy-interval theory
**Status: Search-space reduction layer implemented**

Implemented:

- `Analysis/Uniprocessor/BusyInterval.v`
- `Analysis/Uniprocessor/BusyIntervalLemmas.v`
- `Examples/BusyIntervalExamples.v`
- policy-independent busy interval definitions on top of `Schedule`
- prefix / suffix / no-idle-slot lemmas
- maximal interval boundary decomposition lemmas
- interval processor-supply aggregation for the single-CPU case
- `Analysis/Uniprocessor/BusyWindowSearch.v`: busy-window search-space reduction layer
  (`busy_window_candidate`, `busy_window_witness`, overload/deadline lemmas)
- `Analysis/Uniprocessor/ResponseTimeSearch.v`: response-time search-space reduction layer
  (`response_time_candidate`, `response_time_search_witness`)

Remaining:

- Busy-interval existence at a busy time point: constructive extraction of maximal
  busy interval from any busy slot (discrete-time last-idle-slot argument)
- policy-generic busy-window interfaces

### G-2. Demand-bound / request-bound theory
**Status: Aggregate processor-demand hook layer implemented**

Implemented:

- `Analysis/Common/WorkloadAggregation.v`: `total_job_cost`, `total_job_cost_le_length_mul`,
  `nat_mul_lt_ceil_div`, `ceil_div_mono` — shared workload-aggregation helpers
- `Analysis/Uniprocessor/RequestBound.v`: `periodic_rbf`, `sporadic_rbf_bound`,
  monotonicity lemmas, `periodic_rbf_zero`, `periodic_rbf_le_coarse_bound`
- `PeriodicFiniteHorizon.v` / `SporadicFiniteHorizon.v`: `*_implies_index_lt_tight`
  tight ceiling-division count bounds replacing the coarse `< H` bound
- `PeriodicWorkload.v` / `SporadicWorkload.v` / `JitteredPeriodicWorkload.v`:
  period-aware `⌈H/period⌉ × wcet` workload bounds; bridge lemmas to RBF
- `Examples/RequestBoundExamples.v`: concrete RBF computations, monotonicity examples,
  sporadic = periodic RBF example, coarse bound comparison, jitter→sporadic bound
- `Analysis/Uniprocessor/DemandBound.v`: `periodic_dbf`, `sporadic_dbf_bound`,
  `jittered_periodic_dbf_bound`; zero-before-deadline, at-deadline, monotonicity,
  and `periodic_dbf_le_periodic_rbf` lemmas
- `Analysis/Uniprocessor/ProcessorDemand.v`: `taskset_periodic_dbf`,
  `taskset_sporadic_dbf_bound`, `taskset_jittered_periodic_dbf_bound`,
  append / monotonicity / NoDup-stability lemmas, and a busy-interval
  contradiction hook for processor-demand style arguments
- `TaskModels/Periodic/PeriodicDemandBound.v`: `periodic_jobset_deadline_upto`,
  index count bound, `periodic_demand_le_dbf`,
  `periodic_total_demand_le_taskset_dbf`
- `TaskModels/Periodic/PeriodicWindowDemandBound.v`:
  `periodic_jobset_deadline_between`, finite window-DBF definitions,
  and explicit-window-demand to aggregate-window-DBF bridge lemmas
- `TaskModels/Sporadic/SporadicDemandBound.v`: `sporadic_jobset_deadline_upto`,
  count bound, `sporadic_demand_le_dbf`,
  `sporadic_total_demand_le_taskset_dbf`
- `TaskModels/Jitter/JitteredPeriodicDemandBound.v`: `jittered_periodic_jobset_deadline_upto`,
  bridge to sporadic, `jittered_periodic_demand_le_dbf`,
  `jittered_periodic_total_demand_le_taskset_dbf`
- `Examples/DemandBoundExamples.v`: concrete DBF computations, periodic/sporadic demand
  bound examples
- `Examples/ProcessorDemandExamples.v`: aggregate DBF computations and
  processor-demand hook examples
- `Analysis/Uniprocessor/EDFProcessorDemand.v`: EDF-facing busy-window wrappers,
  window-overload contradiction core, and
  EDF-specific theorem interfaces
  `periodic_window_dbf_implies_no_deadline_miss_under_edf` and
  `periodic_window_dbf_implies_edf_feasible_on_finite_horizon`
  (both now proven at stronger interfaces that require an explicit EDF
  schedule witness; the no-miss theorem also requires a busy-window/no-carry-in
  bridge, and the finite-horizon feasibility theorem packages that witness
  into `feasible_on`)
- `TaskModels/Periodic/PeriodicEDFBridge.v`: window-DBF bridge theorems
  `periodic_edf_schedulable_by_window_dbf_on_finite_horizon` and
  `periodic_edf_schedulable_by_window_dbf_on_finite_horizon_auto` now close
  without `feasible_on` as a hypothesis
- `Examples/PeriodicProcessorDemandExamples.v`: periodic window-DBF computations
  and bridge-theorem usage examples (no longer requires explicit `feasible_on`)

Remaining:

- construct a generic EDF witness schedule to recover the original weak
  window-DBF APIs without requiring an explicit schedule witness
- deeper schedulability / response-time theorems consuming the new busy-window search hook

### G-3. Supply-bound / interface theory
**Status: Not started**

Planned:

- supply bound function (sbf)
- service curves / lower supply abstractions
- interface-based analysis hooks
- future compatibility with hierarchical scheduling

### G-4. Analysis-ready workload abstractions
**Status: In progress**

Planned:

- periodic / sporadic / jittered-periodic finite-horizon workload bounds
- workload bounds on intervals
- interference templates
- reusable counting lemmas for idealized and delay-aware response-time analyses

---

## 8. Phase H: OS-level operational semantics
**Status: Not started**

Planned:

- per-CPU current
- runqueues
- wakeup / block / completion
- timer event
- preemption point
- migration / IPI / reschedule request
- trace semantics
- schedule projection

### H-1. Explicit delay sources
**Status: Not started**

Planned:

- dispatch / context-switch overhead
- timer latency
- wakeup latency
- migration latency
- remote reschedule / IPI latency
- bounded non-preemptive windows if needed

These delays should live in the operational layer, not in the core abstract schedule.

### H-2. Projection discipline
**Status: Not started**

Planned:

- define how an operational trace projects to an abstract schedule
- define what it means for the projection to lag behind ideal decisions
- isolate machine/OS delay from policy semantics

---

## 9. Phase I: Shared resources, suspension, and preemption models
**Status: Not started**

This phase adds standard real-time complications that strongly affect response-time analysis.

### I-1. Blocking and shared-resource models
**Status: Not started**

Planned:

- abstract blocking terms
- critical-section model
- lock/resource ownership model
- interfaces suitable for PCP / SRP style protocols
- later extension hooks for multiprocessor locking protocols

### I-2. Self-suspension and segmented execution
**Status: Not started**

Planned:

- self-suspending jobs/tasks
- segmented execution models
- separation between execution demand and suspension delay
- sufficient conditions for safe upper bounds

### I-3. Limited preemption / non-preemptive regions
**Status: Not started**

Planned:

- bounded non-preemptive chunks
- preemption-point model
- relation to blocking and dispatch overhead
- zero-non-preemptive special case

---

## 10. Phase J: Refinement strengthening
**Status: Partially done at the abstract uniprocessor level**

Implemented core:

- `SchedulingAlgorithmRefinement.v`
- abstract-policy / executable-algorithm connection for current single-CPU developments

What is already done:

- abstract policy -> executable chooser pipeline exists in the current single-CPU theory

What remains:

- executable algorithm -> operational scheduler refinement
- operational scheduler -> OS-level model refinement
- multicore refinement path
- bounded-delay refinement theorems connecting operational delay to abstract schedules

### J-1. Awkernel-first refinement completion
**Status: Not started**

Planned:

- define the Awkernel-facing operational scheduler model
- identify the concrete Awkernel state needed for projection:
  - current task / thread
  - runnable state
  - wakeup / block / completion events
  - timer / reschedule / migration events
- define projection from Awkernel operational traces to abstract schedules
- prove refinement from Awkernel-oriented scheduler behavior to the abstract scheduling semantics
- complete the refinement chain end-to-end on Awkernel before attempting the same standard on Linux

Rationale:

- Awkernel is co-designable with the formalization
- missing interfaces and invariants can be adjusted in the OS and the model together
- this makes it the right target for completing “refinement verification for a designable OS”

### J-2. Refinement-oriented implementation discipline
**Status: Not started**

Planned:

- make explicit which scheduler invariants must be preserved by implementation hooks
- define proof-oriented interfaces for:
  - enqueue / dequeue
  - wakeup
  - block
  - timer-triggered reschedule
  - migration / IPI handling
- isolate proof-relevant scheduler state from engineering details
- keep the abstract schedule model stable while refining the operational layer underneath

---

## 11. Phase K: Analysis on top of semantics
**Status: Not started**

Planned:

- partitioned schedulability / response-time analysis
- global EDF analysis
- multicore interference reasoning
- dynamic-metric analysis
- speedup bounds / policy comparison

### K-1. Idealized analysis
**Status: Not started**

Planned:

- zero-overhead, zero-jitter, zero-blocking baseline theorems
- clean reuse of the existing abstract semantic core

### K-2. Delay-aware analysis
**Status: Not started**

Planned:

- response-time analysis with explicit parameters for:
  - release jitter
  - blocking
  - scheduler overhead
  - timer / wakeup / migration latency
- separation of:
  - execution demand
  - interference
  - delay budget
- zero-delay specialization as a corollary of the general theorem

### K-3. Sustainability / monotonicity results
**Status: Not started**

Planned:

- “things get no worse when parameters improve” theorems
- monotonicity with respect to lower execution costs
- monotonicity with respect to smaller delays/blocking/jitter
- reusable theorem shapes for later policy-specific analyses

### K-4. Speedup / resource augmentation
**Status: Not started**

Planned:

- speedup-factor statements
- capacity augmentation style comparisons
- policy comparison under bounded extra speed/resources
- global vs partitioned comparison hooks

### K-5. Placement principle
**Status: Design decision**

Response-time analysis should be built on top of explicit delay and blocking assumptions.
The project should avoid hard-wiring these effects into the core schedule semantics.

### K-6. Trace-based validation on existing OSes
**Status: Not started**

Planned:

- define a trace schema for externally observed scheduler behavior
- instantiate the schema for Linux traces
- relate observed trace events to the abstract schedule / delay-aware model
- validate whether theoretical invariants and analysis assumptions are reflected in observed executions
- use Linux as an external applicability case, not as the first full refinement target

Rationale:

- Linux is not fully designable by this project
- the immediate value is to show external applicability of the formal framework
- trace-based validation is a realistic bridge between theory and production OS behavior

### K-7. Linux as external applicability benchmark
**Status: Not started**

Planned:

- select representative Linux scheduling scenarios
- compare abstract predictions against measured traces
- identify which discrepancies are explained by:
  - scheduler overhead
  - wakeup / timer latency
  - migration effects
  - implementation-specific heuristics
- use the results to justify the framework’s relevance beyond Awkernel

---

## 12. Phase L: Hierarchical scheduling and compositional interfaces
**Status: Not started**

This phase is a natural extension once demand/supply abstractions exist.

Planned:

- server/reservation abstractions
- compositional interfaces
- component-level schedulability contracts
- relation to supply-bound functions
- hooks for virtualized or partitioned subsystems

---

## 13. Phase M: Future advanced extensions
**Status: Not started**

These are worthwhile, but should remain clearly downstream of the core semantic and analysis pipeline.

### M-1. Mixed-criticality scheduling
**Status: Not started**

Planned:

- multi-budget or multi-assumption task models
- mode-change semantics
- degraded-service guarantees
- integration with delay-aware analysis

### M-2. Parallel real-time scheduling beyond static DAG structure
**Status: Not started**

Planned:

- stronger parallel workload models
- work/span style abstractions if useful
- scheduling guarantees for parallel real-time computations

---

## 14. Practical priority order from the current implementation

### Priority 1
Stabilize and document the reusable uniprocessor core.

### Priority 2
Finish the partitioned theorem layer and clean up policy lifting.

### Priority 3
Promote periodic/sporadic task-generation models earlier in the roadmap, including release jitter / offsets.

### Priority 4
Strengthen multicore-common semantics.

### Priority 5
Strengthen the existing global EDF/LLF theorem layers.

### Priority 6
Complete **Awkernel-first refinement verification** for a designable OS.

### Priority 7
Introduce analysis foundations: busy intervals, dbf/rbf, and sbf/interface abstractions.

### Priority 8
Introduce OS-level delay sources and projection discipline.

### Priority 9
Use **Linux trace-based validation** to demonstrate external applicability.

### Priority 10
Add shared-resource, suspension, and limited-preemption models.

### Priority 11
Strengthen refinement with bounded-delay statements.

### Priority 12
Build idealized and delay-aware schedulability/response-time analysis on top.

### Priority 13
Add hierarchical scheduling / compositional interfaces.

### Priority 14
Add DAG/parallel and mixed-criticality extensions.

---

## 15. One-line summary

The project should complete **refinement verification on Awkernel as a designable OS first**,
and then use **Linux trace-based validation** to demonstrate that the framework also applies
externally to real existing operating systems.
