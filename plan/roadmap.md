# Roadmap

## 0. Current Position

This project is not merely a schedulability-analysis library.
Its core is a Rocq formalization centered on:

- executable scheduler semantics
- scheduling-algorithm refinement
- reusable uniprocessor theory
- extension toward multicore and OS-level semantics
- analysis layered on top of those semantics
- a bridge from theory to implementation-oriented scheduler behavior

### Main research direction

The main research direction is **mechanized multicore scheduler refinement**, not only
the re-proof of classical uniprocessor theorems.

The intended contribution is to connect, in one reusable framework:

- abstract policy semantics
- executable scheduler constructions
- schedule / service / feasibility semantics
- witness / bridge layers for finite horizons and analysis
- multicore and OS-level operational semantics
- refinement and trace-based validation

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
- periodic-task layer
- sporadic-task layer
- jittered-periodic layer
- initial multicore-common layer
- initial global EDF layer
- initial global LLF layer
- busy-interval / busy-window search foundations
- request-bound / demand-bound / processor-demand foundations
- periodic EDF processor-demand bridge layer with explicit busy-prefix / witness interfaces
- minimal operational projection slice:
  - operational state / trace skeleton
  - trace-to-schedule projection
  - initial projection soundness lemmas
  - Awkernel-facing thin wrapper

### Interpretation of the current state

The project is no longer in the phase of “building the first uniprocessor core.”
That base is already substantial.

The next work is mainly:

1. close the current periodic EDF window-DBF layer with zero-offset classical corollaries
2. add an analytical LLF theorem layer via laxity / feasibility bridges
3. stabilize and document the multicore theorem-layer public APIs
4. turn partitioned multicore into a mature theorem layer
5. strengthen multicore-common semantics and the reusable global theorem layers
6. introduce OS-level operational semantics and projection discipline
7. complete refinement on a designable OS and validate external applicability on Linux

### Research gap and intended novelty frontier

Existing mechanization is relatively strong in:

- uniprocessor scheduling semantics
- local schedulability / optimality arguments
- bridges between analysis and implementation in restricted settings

The weaker and more research-significant frontier is:

- partitioned/global multicore synthesis
- policy-generic top-`m` reasoning
- fairness / bounded waiting / starvation-freedom
- interference / busy-window / tardiness reasoning on multicore
- migration-aware service and completion reasoning
- OS-like operational semantics with timer / wakeup / migration / IPI
- end-to-end bridges from scheduling theory to concrete scheduler behavior

This roadmap therefore treats those multicore and refinement-facing items as the
main long-term research contributions.

### Proof discipline for roadmap growth

The project should follow these proof-discipline rules.

- Prefer **explicit witness / bridge records** over hidden axioms.
- When an exact public statement does not yet close, prefer **statement strengthening**
  over leaving an unprovable API in place.
- Treat helper lemmas, bridge lemmas, and witness-packaging records as
  **first-class milestones**, not as disposable temporary work.
- Treat the current **Periodic EDF** public bridge/API as largely stabilized:
  the next uniprocessor step is to derive zero-offset classical corollaries
  from the existing window-DBF bridge, then widen to other policy-specific
  analytical layers such as LLF.

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

- first, define semantic invariants and reusable counting / service lemmas
- next, define analysis foundations such as busy intervals and demand / supply functions
- then, prove idealized schedulability and response-time theorems
- finally, add blocking, suspension, limited preemption, and operational overheads

This keeps the semantic core reusable while still allowing standard
scheduling-theory results to be mechanized.

### Practical validation strategy

The project should separate two goals clearly:

- **refinement completion on a designable OS**
- **external applicability demonstration on existing OSes**

Awkernel is designable together with the formal model, so it is the right place
to complete the end-to-end refinement story:

- scheduling algorithm
- scheduler semantics
- OS-operational semantics
- refinement from implementation-oriented behavior to abstract schedule semantics

For **Linux**, the near-term goal should be different.
Rather than attempting full refinement first, the project should use
**trace-based validation** to show that the abstract theory and delay-aware
models can be applied externally to a real, existing OS whose internal design
is not controlled by this project.

This yields a two-track validation strategy:

1. **Awkernel** as the primary target for completed refinement verification
2. **Linux** as the primary target for trace-based external validation

### Documentation synchronization policy

Whenever the roadmap changes in a proof-relevant way, keep the following
documents synchronized:

- `roadmap.md`
- `what_to_prove.md`
- `design/ArchitecturalLayering.md`

In addition, representative example files should be kept aligned with the
public theorem inventory and naming conventions.

---

## 1. Phase A: Stabilize the reusable uniprocessor core
**Status: In progress, but largely implemented**

This phase is mostly about turning the existing EDF / LLF / FIFO / RR
development into a clearly reusable theory core.

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

- make the generic / policy-specific boundary more explicit
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
- EDF and LLF already serve as static / dynamic metric examples

What remains:

- clearly separate static metric vs dynamic metric
- make the interface-level story cleaner
- prepare the path for future metric-based policies

### A-3. Inventory of uniprocessor results
**Status: In progress**

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

### A-4. Public theorem inventory and naming
**Status: Not started as a dedicated cleanup task**

Planned:

- separate public entry points from helper lemmas
- make theorem naming parallel across:
  - generic
  - periodic
  - sporadic
  - jittered-periodic
  - partitioned
  - global
- document which theorems are intended as stable downstream APIs

---

## 2. Phase B: Task-generation layer
**Status: Partially done**

This phase comes early because the current code already contains substantial
task/job structure together with periodic, sporadic, and jittered variants.

### B-1. Periodic tasks
**Status: Finite-horizon bridge, enumeration, lifts, and analysis hooks implemented**

Implemented core:

- `Base.v` contains task-related fields
- `PeriodicTasks.v`
- `PeriodicFiniteHorizon.v`
- `PeriodicEnumeration.v`
- `PeriodicFiniteOptimalityLift.v`
- `PeriodicEDFBridge.v`
- `PeriodicLLFBridge.v`
- `PeriodicPartitionedFiniteOptimalityLift.v`
- `PeriodicWorkload.v`
- `PeriodicDemandBound.v`
- `PeriodicWindowDemandBound.v`

What is already done:

- periodic task/job generation predicates and consistency lemmas exist
- finite-horizon periodic enumeration exists with codec-based soundness/completeness
- generic periodic finite-optimality lift exists
- EDF / LLF wrappers exist
- periodic partitioned lift exists
- periodic workload and demand-bound hooks exist

What remains:

- utilization / Liu & Layland style theorems
- stronger periodic analysis beyond the current finite-horizon / witness pipeline
- automation for routine finite-horizon bridge construction where structurally obvious

### B-2. Sporadic tasks
**Status: Finite-horizon witness layer and workload hooks implemented**

Implemented:

- `SporadicTasks.v`
- `TaskModels/Common/FiniteHorizonWitness.v`
- `TaskModels/Common/WitnessCandidates.v`
- `TaskModels/Common/WitnessFiniteOptimalityLift.v`
- `SporadicFiniteHorizon.v`
- `SporadicWorkload.v`
- `SporadicEnumeration.v`
- `SporadicPeriodicBridge.v`
- EDF / LLF / partitioned witness-based lift bridges
- `SporadicDemandBound.v`

What is already done:

- sporadic generation predicates and separation-based model exist
- shared finite-horizon witness API exists
- witness-based finite-horizon scheduling lifts exist
- periodic-to-sporadic bridge exists
- sporadic workload and demand-bound hooks exist

What remains:

- utilization / Liu & Layland style theorems where appropriate
- stronger analysis results beyond the finite-horizon witness pipeline

Design note:

- sporadic has no automatic codec because releases are not determined by
  `(task, index)` alone
- the intended finite-horizon abstraction is a manual witness record carrying
  `enumJ` plus soundness / completeness proofs

### B-3. Release jitter / arrival offsets
**Status: Initial jittered-periodic layer implemented**

Implemented:

- `TaskModels/Jitter/ReleaseJitter.v`
- `JitteredPeriodicTasks.v`
- `JitteredPeriodicSporadicBridge.v`
- `JitteredPeriodicFiniteHorizon.v`
- `JitteredPeriodicEnumeration.v`
- `JitteredPeriodicFiniteOptimalityLift.v`
- `JitteredPeriodicEDFBridge.v`
- `JitteredPeriodicLLFBridge.v`
- `JitteredPeriodicPartitionedFiniteOptimalityLift.v`
- `JitteredPeriodicWorkload.v`
- `JitteredPeriodicDemandBound.v`
- `Examples/JitteredPeriodicExamples.v`

Design note:

- jitter is kept in the task-generation layer and does not modify `Schedule`
- no automatic codec is introduced, because actual releases are not recovered
  from `(task, index)` alone
- promotion to the full sporadic model still requires an explicit
  `sporadic_separation_on` assumption

### B-4. Utilization-based classical theory
**Status: Not started**

Planned:

- utilization and density definitions
- Liu & Layland style sufficient tests
- classical EDF / RM-facing theorem interfaces where meaningful
- clear separation between classical sufficient conditions and exact
  busy-window / demand-bound results

### B-5. Why this phase is early
**Status: Design decision**

Task-generation models that preserve the job-level semantic core should be added
before deeper multicore extensions.
This matches the current implementation better than pushing them to a very late phase.

---

## 3. Phase C: Partitioned multicore as a mature theorem layer
**Status: Core theorem layer implemented; public inventory stabilized**

Implemented core:

- `Partitioned.v`
- `PartitionedCompose.v`
- `PartitionedEntryPoints.v`
- `Multicore/Partitioned/Policies/PartitionedEDF.v`
- `Multicore/Partitioned/Policies/PartitionedFIFO.v`
- `Multicore/Partitioned/Policies/PartitionedRR.v`
- `Multicore/Partitioned/Policies/PartitionedLLF.v`
- `Multicore/Partitioned/Policies/PartitionedFiniteOptimalityLift.v`
- `Examples/PartitionedExamples.v`

### C-1. Partitioned construction and compose layer
**Status: Done as a reusable generic entry-point layer**

What is already done:

- partitioned scheduler construction exists
- local-to-global schedule gluing exists
- local witness -> partitioned schedulable-by lifting exists
- policy-specific partitioned wrappers exist

What is already done:

- assignment-respect, local scheduler validity, and global validity now have a
  documented public boundary
- `PartitionedEntryPoints.v` provides the canonical downstream import path

### C-2. Partitioned policy lifting
**Status: Done for EDF / FIFO / RR / LLF, with light cleanup remaining**

What is already done:

- EDF / FIFO / RR / LLF wrappers all exist

What is already done:

- wrapper files stay thin and explicit about their role
- EDF / LLF are documented as finite-optimality-ready
- FIFO / RR are documented as intentionally wrapper-only for now

### C-3. Partitioned schedulability lifting
**Status: Done for EDF / LLF finite-optimality lifting**

What is already done:

- the main entry points for lifting local schedulability already exist
- `PartitionedFiniteOptimalityLift.v` provides a reusable finite-job lift
- examples already demonstrate partitioned major results for:
  - generic
  - periodic
  - sporadic
  - jittered-periodic
  paths

What is already done:

- the intended reusable theorem inventory is exposed via
  `PartitionedEntryPoints.v`
- representative examples are curated in `Examples/PartitionedExamples.v`

What remains:

- prepare the interface for later delay-aware partitioned analysis

### C-4. Partitioned analysis-facing cleanup
**Status: Not started**

Planned:

- isolate theorem families intended for later response-time / delay-aware analyses
- decide whether FIFO / RR should later gain finite-optimality-ready lifts

---

## 4. Phase D: Multicore-common semantics
**Status: Affinity layer, migration-aware service/completion/remaining-cost/laxity bridges, and top-m busy bridge strengthening implemented**

Implemented core:

- `MultiCoreBase.v`
- `Admissibility.v`
- `AffinityFacts.v`
- `AdmissibleCandidateSource.v`
- `TopMAdmissibilityBridge.v`
- `Multicore/Common/ServiceFacts.v`
- `Multicore/Common/CompletionFacts.v`
- `Multicore/Common/RemainingCostFacts.v`
- `Multicore/Common/LaxityFacts.v`

What is already done:

- per-CPU view of global schedule
- no-duplication aliasing / bridge
- idle / busy predicates
- globally-runnable notions
- bridge lemmas connecting multicore notions to the existing schedule model
- `all_cpus_admissible` and `singleton_admissibility` concrete instances
- general `cpu_affinity` / `affinity_admissibility` / `job_has_admissible_cpu` layer
- admissibility-aware candidate-source specs
- top-`m` bridge lemmas that turn a non-running eligible/admissible job into
  an all-CPUs-busy consequence
- migration-aware decomposition of `service_job` into projected per-CPU service
- completion / eligibility bridges over the decomposed service view
- remaining-cost / laxity bridges over migration-aware service accounting
- one-step change lemmas for `remaining_cost` and `laxity` under `no_duplication`

What remains:

- multicore validity beyond the current minimal base
- stronger fairness / interference-facing lemmas under migration
- abstractions for top-`m` and non-partitioned selection beyond admissibility
- API stabilization: clarify public API vs helper lemma boundary
- richer affinity / candidate-source instantiation examples
- foundations for fairness / interference reasoning on top of the current bridge layer

---

## 5. Phase E: Global / clustered scheduling
**Status: E-1 largely stable; thin interval supply hooks now exist and next work shifts toward richer analysis clients**

### E-1. Global scheduling
**Status: Initial global EDF / LLF theorem layers done; stable entry-point layer largely in place**

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
- `GlobalLLF.v` provides analogous theorem families
- `TopMMetricFacts.v` provides reusable top-`m` metric-order facts for
  dynamic-metric policies
- `GlobalLLF.v` now also exposes LLF-facing wrappers that connect
  non-running admissible jobs to:
  - running-job laxity comparisons
  - machine-full consequences
- `GlobalEDF.v` and `GlobalLLF.v` expose thin interval full-supply wrappers for
  non-running eligible/admissible jobs
- `GlobalEntryPoints.v` provides the canonical downstream import path for the
  stable global theorem inventory
- `Examples/GlobalExamples.v` curates representative downstream clients in one
  place

What remains:

- connect the global theorem layer to later analysis results
- identify which global EDF / LLF facts should be lifted to policy-generic layers
- richer candidate-source / affinity instantiation examples
- prepare analysis / fairness / migration-aware interference hooks

### E-2. Clustered scheduling
**Status: Not started**

Planned:

- cluster-local global semantics
- bridge between partitioned and fully global scheduling

### E-3. Global dynamic-metric policies
**Status: Theorem inventory strengthened; analysis-facing growth remains**

Planned:

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
global-scheduling layer.

---

## 7. Phase G: Analysis foundations
**Status: In progress**

This phase collects standard abstractions from scheduling theory that should be
reusable across idealized, delay-aware, uniprocessor, and multicore analyses.

### G-1. Busy-window / busy-interval theory
**Status: Search-space reduction layer implemented**

Implemented:

- `Analysis/Uniprocessor/BusyInterval.v`
- `Analysis/Uniprocessor/BusyIntervalLemmas.v`
- `Examples/BusyIntervalExamples.v`
- `Analysis/Uniprocessor/BusyWindowSearch.v`
- `Analysis/Uniprocessor/ResponseTimeSearch.v`

What is already done:

- policy-independent busy-interval definitions on top of `Schedule`
- prefix / suffix / no-idle-slot lemmas
- maximal interval boundary decomposition lemmas
- interval processor-supply aggregation for the single-CPU case
- busy-window search witnesses
- response-time search witnesses

Remaining:

- constructive extraction of maximal busy intervals from busy slots
- policy-generic busy-window interfaces
- tighter integration with downstream analysis-facing theorem inventories

### G-2. Demand-bound / request-bound theory
**Status: Aggregate processor-demand layer implemented; EDF bridge stabilization completed**

Implemented core:

- `Analysis/Common/WorkloadAggregation.v`
- `Analysis/Uniprocessor/RequestBound.v`
- `Analysis/Uniprocessor/DemandBound.v`
- `Analysis/Uniprocessor/ProcessorDemand.v`
- periodic / sporadic / jittered-periodic demand-bound bridge files
- `Examples/RequestBoundExamples.v`
- `Examples/DemandBoundExamples.v`
- `Examples/ProcessorDemandExamples.v`
- `Analysis/Uniprocessor/EDFProcessorDemand.v`
- `Examples/PeriodicProcessorDemandExamples.v`

What is already done:

- shared workload aggregation lemmas exist
- periodic / sporadic / jittered-periodic RBF / DBF interfaces exist
- aggregate taskset DBF interfaces exist
- explicit finite-window demand bridges exist
- busy-window contradiction hooks exist for processor-demand style arguments
- EDF-facing theorem interfaces exist for:
  - no deadline miss under explicit schedule witness assumptions
  - finite-horizon feasibility under explicit witness assumptions
- `PeriodicEDFBridge.v` now exposes public theorem families that no longer require
  `feasible_on` as an input hypothesis
- bridge-first busy-prefix public wrappers exist in `PeriodicEDFBridge.v`
- compatibility wrappers are isolated in `PeriodicEDFBridgeCompat.v`
- packaged bridge records exist for the periodic EDF busy-prefix assumptions

Remaining:

- automate routine bridge construction where it is structurally obvious
- decide which witness / bridge records should become policy-generic public APIs
- add deeper schedulability / response-time theorems on top of the new hooks

### G-2a. EDF processor-demand bridge stabilization
**Status: Done**

This is a completed bridge-closure milestone in the roadmap.

- keep the packaged busy-prefix bridge as the default public interface
- keep bridge-based theorems as the canonical public statements
- finished client/example migration and compatibility-wrapper cleanup across:
  - generated-jobset views
  - finite-horizon views
  - busy-prefix views
- treat bridge packaging and client migration as an explicit milestone, not as
  incidental cleanup
- only after this closes, widen the same style to other bridges and theorem families

### G-2b. Periodic EDF analysis inventory packaging
**Status: Implemented**

This is the immediate follow-up packaging step after G-2a.

- `PeriodicEDFAnalysisEntryPoints.v` now packages the stable downstream import
  for the periodic EDF idealized-analysis inventory
- `PeriodicEDFBridge.v` remains the canonical bridge-first theorem layer
- `PeriodicEDFBridgeCompat.v` remains isolated as a legacy-only wrapper layer
- `PeriodicProcessorDemandExamples.v` is the stable client of the packaged
  import boundary
- `PeriodicProcessorDemandCompatExamples.v` remains the legacy client for the
  unpackaged APIs

### G-2c. Periodic EDF classical corollary closure
**Status: Implemented as a bridge-first public layer**

- `PeriodicClassicDBF.v` closes the zero-offset special case from window-DBF to
  scalar DBF
- `PeriodicEDFClassicalBridge.v` exposes the canonical public corollaries only
  in bridge-first form
- do not treat generated EDF alone as enough to derive `no_carry_in`
- any future attempt to auto-supply `periodic_edf_busy_prefix_bridge` should be
  planned as a separate theorem family with additional backlog / prefix
  assumptions

### G-3. Supply-bound / interface theory
**Status: Initial multicore full-supply equality layer implemented; stable analysis entry-point packaging added**

Implemented:

- `Analysis/Multicore/ProcessorSupply.v` now exposes:
  - pointwise full-machine supply equality
  - interval full-machine supply equality
- `Analysis/Multicore/GlobalAnalysisEntryPoints.v` now packages the stable
  downstream import path for multicore global analysis
- `Examples/GlobalInterferenceExamples.v` now validates that the representative
  downstream client closes over the packaged import boundary

Planned:

- supply bound function (`sbf`)
- service curves / lower supply abstractions
- interface-based analysis hooks
- future compatibility with hierarchical scheduling

### G-4. Analysis-ready workload abstractions
**Status: Finite-horizon workload hook layer and initial multicore interval/interference bridge layer implemented**

Implemented:

- periodic finite-horizon workload bounds
- sporadic finite-horizon workload bounds
- jittered-periodic finite-horizon workload bounds

Remaining:

- workload bounds on intervals
- reusable interference templates beyond the current machine-full / covering-list hooks
- service / delay decomposition hooks for later response-time analyses
- multicore-aware workload / interference abstractions built on Phase D and E

### G-4a. Multicore global analysis packaging
**Status: Implemented as the pre-fairness stabilization step**

Implemented:

- stable downstream import boundary for multicore global analysis via
  `Analysis/Multicore/GlobalAnalysisEntryPoints.v`
- representative example migration to the packaged boundary in
  `Examples/GlobalInterferenceExamples.v`
- public inventory split between packaged downstream theorems and
  file-local helper lemmas

Next:

- fairness / tardiness hooks should build on the packaged entry point rather
  than importing `ProcessorSupply`, `Interference`, and `GlobalEntryPoints`
  separately

### G-4b. Multicore workload absorption hooks
**Status: Implemented**

Implemented:

- `Analysis/Multicore/GlobalWorkloadAbsorption.v` as the analysis-facing hook
  layer above processor supply, interference, and the global theorem layer
- multicore list-service upper bounds built from `valid_schedule` and
  `no_duplication`
- capacity-recovery theorem that turns
  full-supply + covering-list assumptions into list-service = machine-capacity
- strict workload-gap wrappers for global EDF / LLF when a job stays
  eligible/admissible but non-running across an interval
- packaged re-export through `Analysis/Multicore/GlobalAnalysisEntryPoints.v`
  and a representative downstream example

Next:

- build fairness / tardiness / bounded-waiting analyses on top of the
  workload-absorption API rather than re-deriving interval supply arguments
- decide which parts of the EDF / LLF wrappers should later move into a more
  policy-generic top-`m` analysis layer

### G-4c. First global fairness client layer
**Status: Implemented as the first post-absorption client slice**

Implemented:

- `Analysis/Multicore/GlobalFairness.v` as the first client layer above
  `GlobalWorkloadAbsorption.v`
- contradiction wrappers that close the strict workload-gap lemmas against an
  explicit interval workload upper bound
- first EDF / LLF fairness corollaries showing that a persistently
  eligible/admissible job must run somewhere in the interval once the
  non-running case would force a workload contradiction
- packaged re-export through `Analysis/Multicore/GlobalAnalysisEntryPoints.v`
  and curated downstream examples

Next:

- lift the EDF / LLF fairness clients toward a policy-generic top-`m`
  analysis layer where the admissibility interface is stable enough
- connect the fairness client layer to bounded waiting / bounded tardiness
  statements for concrete task models

---

## 8. Phase H: OS-level operational semantics
**Status: In progress at the execution-first projection-discipline level**

Implemented core:

- `Operational/Common/State.v`
- `Operational/Common/Trace.v`
- `Operational/Common/Projection.v`
- `Operational/Common/Step.v`
- `Operational/Common/Invariants.v`
- `Operational/Common/StepLemmas.v`
- `Operational/Common/Execution.v`
- `Operational/Common/ProjectionLemmas.v`
- `Operational/Awkernel/MinimalProjection.v`

What is already done:

- per-CPU current
- runnable-job view
- pending reschedule requests
- wakeup / block / completion / dispatch / tick event skeleton
- trace semantics
- structural operational invariants separated from trace-level soundness
- step-preservation lemmas for the structural invariant layer
- public `trace_stepwise` plus packaged `execution` record
- schedule projection
- execution-first bridge lemmas from operational soundness to `valid_schedule`
- Awkernel-facing thin projection wrapper over the execution-first bridge

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
**Status: In progress**

Implemented core:

- define how an operational trace projects to an abstract schedule
- isolate machine / OS state from policy semantics with a dedicated projection layer
- separate structural invariants from release/completion trace obligations
- package the public operational interface around `trace_stepwise` and `execution`

What remains:

- define what it means for the projection to lag behind ideal decisions
- isolate machine / OS delay from policy semantics
- extend the current execution-first bridge with richer delay and refinement obligations

---

## 9. Phase I: Shared resources, suspension, and preemption models
**Status: Not started**

This phase adds standard real-time complications that strongly affect response-time analysis.

### I-1. Blocking and shared-resource models
**Status: Not started**

Planned:

- abstract blocking terms
- critical-section model
- lock / resource ownership model
- interfaces suitable for PCP / SRP style protocols
- later extension hooks for multiprocessor locking protocols

### I-2. Self-suspension and segmented execution
**Status: Not started**

Planned:

- self-suspending jobs / tasks
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
**Status: Partially done at the abstract uniprocessor level, with an operational projection skeleton now available**

Implemented core:

- `SchedulingAlgorithmRefinement.v`

What is already done:

- abstract policy -> executable chooser pipeline exists in the current
  single-CPU theory
- operational trace -> abstract schedule projection skeleton exists
- Awkernel-facing naming wrapper exists for the first projection slice

What remains:

- executable algorithm -> operational scheduler refinement
- operational scheduler -> OS-level model refinement
- multicore refinement path
- bounded-delay refinement theorems connecting operational delay to abstract schedules

### J-1. Awkernel-first refinement completion
**Status: In progress at the projection-wrapper level**

Implemented core:

- define a minimal Awkernel-facing operational scheduler state
- define projection from Awkernel operational traces to abstract schedules

What remains:

- identify the concrete Awkernel state needed for projection:
  - current task / thread
  - runnable state
  - wakeup / block / completion events
  - timer / reschedule / migration events
- define projection from Awkernel operational traces to abstract schedules
- prove refinement from Awkernel-oriented scheduler behavior to the abstract
  scheduling semantics
- complete the refinement chain end-to-end on Awkernel before attempting the
  same standard on Linux

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

### J-3. Analysis-to-implementation bridge
**Status: Not started**

Planned:

- identify which assumptions from analysis are exported by implementation-facing layers
- connect witness / bridge layers to operational traces and projections
- reuse the same bridge discipline for:
  - Awkernel refinement
  - Linux trace-based validation
- make analysis-relevant invariants explicit rather than implicit in later proofs

---

## 11. Phase K: Analysis on top of semantics
**Status: Not started as a full theorem layer; foundations exist in Phase G**

Planned:

- partitioned schedulability / response-time analysis
- global EDF analysis
- multicore interference reasoning
- dynamic-metric analysis
- speedup bounds / policy comparison

### K-1. Idealized analysis
**Status: Initial EDF processor-demand entry points exist**

Planned:

- package current periodic EDF results into a stable idealized-analysis inventory
- add response-time theorems consuming busy-window / DBF / RBF abstractions
- extend from the current periodic EDF path to broader policy / task-model combinations

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
- monotonicity with respect to smaller delays / blocking / jitter
- reusable theorem shapes for later policy-specific analyses

### K-4. Speedup / resource augmentation
**Status: Not started**

Planned:

- speedup-factor statements
- capacity augmentation style comparisons
- policy comparison under bounded extra speed / resources
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
- validate whether theoretical invariants and analysis assumptions are reflected
  in observed executions
- use Linux as an external applicability case, not as the first full refinement target

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

This phase is a natural extension once demand / supply abstractions exist.

Planned:

- server / reservation abstractions
- compositional interfaces
- component-level schedulability contracts
- relation to supply-bound functions
- hooks for virtualized or partitioned subsystems

---

## 13. Phase M: Future advanced extensions
**Status: Not started**

These are worthwhile, but should remain clearly downstream of the core semantic
and analysis pipeline.

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
- work / span style abstractions if useful
- scheduling guarantees for parallel real-time computations

---

## 14. Immediate milestones from the current implementation

### Immediate milestone 1
Synchronize theorem inventory and design documents with the current multicore
code.

This means:

- update `what_to_prove.md`
- update `design/ArchitecturalLayering.md`
- update `roadmap.md`
- align representative examples with the intended public APIs

### Immediate milestone 2
Stabilize the reusable global theorem layer and its public inventory.

This means:

- add a canonical downstream import for the global theorem layer
- add a canonical example inventory for downstream global clients
- keep the policy-generic vs policy-specific boundary explicit

### Immediate milestone 3
Strengthen multicore-common semantics toward later interference and fairness work.

This means:

- richer service / completion facts
- interval-level machine-supply accounting
- reusable running-set coverage lemmas for interference arguments
- clearer top-`m` abstraction boundaries
- better admissibility / candidate-source instantiations

### Immediate milestone 4
Define the first Awkernel-facing operational projection slice.

This means:

- pick a minimal operational scheduler state
- define trace-to-schedule projection
- prepare the first refinement-facing interface

---

## 15. Practical priority order from the current implementation

### Priority 1
Synchronize **roadmap / theorem inventory / architectural layering** documents.

### Priority 2
Stabilize the reusable **global theorem layer** and its public inventory.

### Priority 3
Strengthen **multicore-common semantics** and top-`m`-facing abstractions.

### Priority 4
Strengthen the existing **partitioned theorem layer** where later analysis
needs clearer public boundaries.

### Priority 5
Deepen the new **Awkernel-first operational semantics and projection discipline**.

### Priority 6
Deepen **idealized analysis** on top of the busy-window / DBF / RBF foundations.

### Priority 7
Introduce **OS-level delay sources** and bounded-delay projection discipline.

### Priority 8
Use **Linux trace-based validation** to demonstrate external applicability.

### Priority 9
Add **shared-resource, suspension, and limited-preemption models**.

### Priority 10
Strengthen **refinement with bounded-delay statements**.

### Priority 11
Build fuller **partitioned / global / delay-aware analysis** on top.

### Priority 12
Add **hierarchical scheduling / compositional interfaces**.

### Priority 13
Add **DAG / parallel and mixed-criticality extensions**.

---

## 16. One-line summary

The project should first close the current **documentation sync and global multicore theorem-layer stabilization work**,
then complete **refinement verification on Awkernel as a designable OS**,
and finally use **Linux trace-based validation** to demonstrate external applicability.
