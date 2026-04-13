# New Roadmap

## 0. Current Position

This project is not merely a schedulability-analysis library.
Its core is a Rocq formalization centered on:

- executable scheduler semantics
- scheduling-algorithm refinement
- reusable uniprocessor theory
- extension toward multicore and OS-level semantics

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
- EDF optimality
- LLF finite optimality pipeline
- partitioned scheduling core
- partitioned EDF / FIFO / RR / LLF wrappers
- partitioned finite-job optimality lift
- initial periodic-task layer
- initial multicore-common layer
- initial global EDF layer

### Interpretation of the current state

The project is no longer in the phase of “building the first uniprocessor core.”
That part is mostly done.

The next work is mainly:

1. stabilize and document the reusable uniprocessor core
2. turn partitioned multicore into a mature theorem layer
3. grow multicore-common semantics beyond the current base layer
4. strengthen the initial global EDF layer and then move to clustered / OS-operational semantics

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
- keep `Design.md` synchronized with the code

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
**Status: Initial layer done**

Implemented core:

- `Base.v` already contains task-related fields
- `PeriodicTasks.v` already contains:
  - expected release
  - expected deadline
  - generated-by-periodic-task predicate
  - periodic-job-model predicates
  - implicit-deadline task predicate
  - basic consistency lemmas

What remains:

- connect the periodic model more systematically to feasibility/schedulability
- add stronger release-pattern lemmas
- add horizon / finite-job extraction lemmas where needed

### B-2. Sporadic tasks
**Status: Not started**

Planned:

- minimum inter-arrival constraint
- sporadic job-generation layer
- relation to periodic as a special case or simpler instance

### B-3. Why this phase is early
**Status: Design decision**

Task-generation models that preserve the job-level semantic core should be added
before deeper multicore extensions.
This matches the current implementation better than pushing them to a very late phase.

---

## 3. Phase C: Partitioned multicore as a mature theorem layer
**Status: In progress, with substantial implementation already done**

Implemented core:

- `Partitioned.v`
- `PartitionedCompose.v`
- `PartitionedPolicies/PartitionedEDF.v`
- `PartitionedPolicies/PartitionedFIFO.v`
- `PartitionedPolicies/PartitionedRR.v`
- `PartitionedPolicies/PartitionedLLF.v`

### C-1. Partitioned construction and compose layer
**Status: Largely done at the definition/entry-point level**

What is already done:

- partitioned scheduler construction exists
- local-to-global schedule gluing exists
- local witness -> partitioned schedulable-by lifting exists
- policy-specific partitioned wrappers exist

What remains:

- enrich the theorem layer
- make the standard lifting lemmas easier to reuse
- better separate:
  - assignment-respect
  - local scheduler validity
  - global schedule validity

### C-2. Partitioned policy lifting
**Status: Mostly done, but still needs cleanup**

What is already done:

- EDF / FIFO / RR / LLF wrappers all exist

What remains:

- unify their common pattern
- reduce duplication in policy-specific wrapper files
- standardize the “local reasoning -> partitioned reasoning” template

### C-3. Partitioned schedulability lifting
**Status: Initial core done**

What is already done:

- the main entry points for lifting local schedulability already exist
- `PartitionedFiniteOptimalityLift.v` provides a reusable finite-job lift for partitioned EDF

What remains:

- strengthen and organize the theorem layer
- make the intended reusable theorem inventory explicit in the roadmap and docs

---

## 4. Phase D: Multicore-common semantics
**Status: Affinity layer added**

Implemented core:

- `MultiCoreBase.v`
- `Admissibility.v`
- `AffinityFacts.v` (new)
- `AdmissibleCandidateSource.v` (new)
- `TopMAdmissibilityBridge.v` (new)

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
- `StrongAdmissibleCandidateSourceSpec`: stronger variant requiring every candidate to be
  admissible somewhere; needed for the generic idle-if-none theorem
- `TopMAdmissibilityBridge`: policy-generic admissibility theorem layer with two tiers:
  - Tier 1 (`all_cpus_admissible`): three `all_cpus_admissible`-specific lemmas
    (extracted from EDF/LLF duplication; EDF/LLF now delegate to these)
  - Tier 2 (generic `adm`, `_gen` suffix): three lemmas for arbitrary admissibility:
    - `top_m_algorithm_some_cpu_busy_if_subset_admissible_somewhere_gen`
    - `top_m_algorithm_running_if_some_cpu_idle_and_subset_admissible_somewhere_gen`
    - `top_m_algorithm_all_cpus_idle_if_no_subset_admissible_somewhere_gen`

What remains:

- multicore validity beyond the current minimal base
- stronger service / completion lemmas under migration
- abstractions for top-m and non-partitioned selection
- API stabilization: clarify public API vs helper lemma boundary in the bridge
- richer affinity/candidate-source instantiation examples

---

## 5. Phase E: Global / clustered scheduling
**Status: Initial global layer started**

### E-1. Global scheduling
**Status: Initial global EDF theorem layer done; admissibility lemmas extracted to common bridge**

What is already done:

- `TopMSchedulerBridge.v` provides the generic top-`m` scheduler bridge
- `TopMAdmissibilityBridge.v` provides policy-generic admissibility lemmas (two tiers):
  - Tier 1 (`all_cpus_admissible`):
    - `top_m_algorithm_all_cpus_idle_if_no_subset_admissible_somewhere`
    - `top_m_algorithm_some_cpu_busy_if_subset_admissible_somewhere`
    - `top_m_algorithm_running_if_some_cpu_idle_and_subset_admissible_somewhere`
  - Tier 2 (generic `adm`, `_gen` suffix):
    - `top_m_algorithm_some_cpu_busy_if_subset_admissible_somewhere_gen`
    - `top_m_algorithm_running_if_some_cpu_idle_and_subset_admissible_somewhere_gen`
    - `top_m_algorithm_all_cpus_idle_if_no_subset_admissible_somewhere_gen`
- `GlobalEDF.v` provides:
  - `global_edf_scheduler`
  - `global_edf_valid`
  - `global_edf_idle_outside_range`
  - `global_edf_no_duplication`
  - subset-aware theorem entry points on top of the bridge
  - admissibility-aware wrappers for both Tier 1 and Tier 2 (delegating to `TopMAdmissibilityBridge`)

What remains:

- connect the global theorem layer to later analysis results
- tighten theorem inventory documentation for downstream analysis use
- richer candidate-source instantiation examples connecting affinity predicates to spec

Note:

- the current bridge from `running` to `admissible_somewhere` is available with a `valid_schedule` premise, not as an unconditional theorem

### E-2. Clustered scheduling
**Status: Not started**

Planned:

- cluster-local global semantics
- bridge between partitioned and fully global scheduling

### E-3. Global LLF
**Status: Initial theorem layer done; admissibility lemmas extracted to common bridge**

What is already done:

- `GlobalLLF.v` provides (structure mirrors GlobalEDF.v):
  - `global_llf_scheduler`
  - `global_llf_valid`
  - `global_llf_idle_outside_range`
  - `global_llf_no_duplication`
  - subset-aware theorem entry points on top of the bridge
  - admissibility-aware wrappers for both Tier 1 and Tier 2 (delegating to `TopMAdmissibilityBridge`)

What remains:

- connect LLF-specific theorem inventory to later dynamic-metric analysis
- identify which global EDF / LLF facts should be lifted to policy-generic layers

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

## 7. Phase G: OS-level operational semantics
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

---

## 8. Phase H: Refinement strengthening
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

---

## 9. Phase I: Analysis on top of semantics
**Status: Not started**

Planned:

- partitioned schedulability / response-time analysis
- global EDF analysis
- multicore interference reasoning
- dynamic-metric analysis
- speedup bounds / policy comparison

This remains intentionally late.

---

## 10. Practical priority order from the current implementation

### Priority 1
Stabilize and document the reusable uniprocessor core.

### Priority 2
Finish the partitioned theorem layer and clean up policy lifting.

### Priority 3
Promote periodic/sporadic task-generation models earlier in the roadmap.

### Priority 4
Strengthen multicore-common semantics.

### Priority 5
Strengthen the existing global EDF theorem layer and use it as the entry point for global LLF.

### Priority 6
Add DAG semantics as a distinct structured-parallel phase.

### Priority 7
Move to OS operational semantics and stronger refinement.

### Priority 8
Build schedulability/response-time analysis on top.
