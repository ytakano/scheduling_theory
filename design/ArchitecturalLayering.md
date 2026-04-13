# Architectural Layering and Directory Structure

The project is organized so that the directory structure directly reflects the conceptual layering of the formalization.

The central design principle is to separate **what a schedule means**, **what kind of abstract scheduler or scheduling algorithm is allowed to produce such a schedule**, and **how an executable or operational implementation is shown to satisfy the abstract specification**. On top of this core, the development is extended in two orthogonal directions: toward richer scheduling platforms (from uniprocessor to multicore and OS-level semantics), and toward richer workload models (such as periodic, sporadic, and DAG-based tasks).

## 1. `Semantics/`: schedule-first foundation

The foundational layer of the project is the semantic model of schedules.

A schedule is introduced first, as the primary mathematical object that describes which job executes on which CPU at which time. Basic notions such as service, completion, readiness, pending status, and deadline satisfaction are defined at this level. In other words, this layer answers the question:

> What does it mean for a schedule to be valid, and what properties can be derived from it?

This choice is intentional. Rather than starting from a concrete scheduler implementation, the development begins with the semantics of execution itself. This makes the later theory independent of any particular algorithm or runtime mechanism.

## 2. `Abstractions/`: abstract schedulers and scheduling algorithms

On top of schedule semantics, the project introduces abstract interfaces for schedulers and scheduling algorithms.

This layer separates two related but distinct notions:

- a **scheduler**, viewed extensionally as an object that admits valid schedules for a job set; and
- a **scheduling algorithm**, viewed intensionally as a rule or chooser that selects jobs according to some policy.

This distinction is important because many scheduling results are naturally stated at the level of abstract schedule existence, while others depend on the structure of a concrete decision rule such as EDF, LLF, FIFO, or Round Robin. By making both notions explicit, the development can support both styles of reasoning without conflating them.

## 3. `Refinement/`: connecting implementations to specifications

The refinement layer connects executable or algorithmic constructions to the abstract specifications defined above.

Its role is to prove statements of the form:

> this implementation realizes that abstract scheduling specification.

This bridge is essential for the long-term goal of the project. The aim is not only to prove theorems about idealized schedules, but also to connect those theorems to schedulers that are executable, implementable, and eventually compatible with OS-level operational models.

Thus, refinement serves as the formal link between abstract theory and concrete realization.

## 4. `Uniprocessor/`: the first major theory layer

The uniprocessor layer is the first major instantiation of the general framework.

It contains reusable single-CPU scheduling theory, generic proof skeletons, and policy-specific developments. In particular, this layer is where results such as canonicalization, normalization, and finite optimality are developed for single-CPU policies.

The uniprocessor layer is deliberately placed above the semantic and abstraction layers, because it should reuse the common schedule model and the common scheduler/algorithm interfaces rather than redefining them. This structure makes uniprocessor results modular and prepares them to be lifted later to richer platforms.

## 5. `Multicore/`: extensions to partitioned, global, and clustered scheduling

The multicore layer extends the single-CPU theory to systems with multiple processors.

This extension is not treated as a completely separate formalization. Instead, it is built on top of the same semantic core. The multicore hierarchy is expected to include several progressively richer models:

- **partitioned scheduling**, where each job is assigned to a fixed CPU;
- **global scheduling**, where jobs may compete for a shared multiprocessor platform; and
- **clustered scheduling**, which sits between the partitioned and fully global extremes.

Structuring the development in this way makes the relationship between these models explicit. Partitioned scheduling can be understood as the first multicore extension, while global and clustered models are introduced only after the common multicore semantic obligations are clarified.

### Multicore admissibility theorem layer

Within the Multicore hierarchy, two sub-layers handle admissibility reasoning:

- **`Multicore/Common/TopMAdmissibilityBridge.v`** is the *policy-independent* theorem layer.
  It proves busy/idle/running lemmas parameterised by an arbitrary admissibility
  predicate `adm` and either `AdmissibleCandidateSourceSpec` or
  `StrongAdmissibleCandidateSourceSpec`.
  It also provides `all_cpus_admissible`-specific lemmas as a special case (Tier 1).

- **`Multicore/Global/GlobalEDF.v`** and **`GlobalLLF.v`** are *policy-specific wrapper layers*.
  Their admissibility lemmas are thin wrappers that instantiate the bridge with the
  EDF or LLF top-m spec and re-export the results under policy-prefixed names.
  The only EDF/LLF-specific elements are the priority metric and the spec construction.

The `AdmissibleCandidateSourceSpec` record captures:

- *soundness*: every candidate belongs to the job subset J;
- *completeness*: every eligible and admissible-somewhere job in J is a candidate;
- *prefix extensionality*: the candidate list depends only on the schedule prefix.

`StrongAdmissibleCandidateSourceSpec` additionally requires every candidate to be
admissible somewhere.  This stronger obligation is needed to prove the general
idle-if-none theorem (`top_m_algorithm_all_cpus_idle_if_no_subset_admissible_somewhere_gen`)
without assuming `0 < m`.

`all_cpus_admissible` is a special case of generic `adm`: for this predicate every
eligible job is already admissible somewhere (given `0 < m`), so
`AdmissibleCandidateSourceSpec` collapses to the standard `CandidateSourceSpec`.
The Tier 1 lemmas in `TopMAdmissibilityBridge.v` are the corresponding entry points
that accept `CandidateSourceSpec` directly.

## 6. `Operational/`: OS-level scheduler semantics

The operational layer is intended to capture scheduler behavior as an evolving machine or system state rather than as a schedule viewed purely extensionally.

This is the layer where concepts such as run queues, current jobs, wakeups, blocking, preemption points, migration requests, and timer-driven rescheduling can be introduced. The purpose of this layer is to model how an operating-system scheduler produces executions over time, and then to relate that operational behavior back to the abstract schedule semantics.

In this sense, the operational layer is not a replacement for the schedule model; it is a more concrete semantics whose observable behavior should refine or project to the abstract schedules studied in the earlier layers.

## 7. `TaskModels/`: workload structure on top of the semantic core

Task models are organized as a separate dimension of extension.

This layer contains models such as:

- **periodic tasks**
- **sporadic tasks**
- **DAG-based tasks**

These are not merely alternative schedulers; they enrich the structure of the workload itself. For this reason, they are separated from both the scheduler abstraction and the platform hierarchy.

Periodic and sporadic task models primarily constrain how jobs are generated over time. DAG task models go further and enrich the internal structure of a job or workload by introducing precedence and node-level execution structure. Despite these differences, all such workload models are attached to the same semantic foundation, so that scheduling results can be stated uniformly whenever possible.

## Why this structure matters

This architecture is designed to make the dependency direction visible in the repository itself.

A reader should be able to understand, simply from the directory structure, that the project proceeds in the following order:

1. define the meaning of schedules;
2. define abstract schedulers and scheduling algorithms on top of that meaning;
3. prove refinement results that connect executable constructions to abstract specifications;
4. build reusable uniprocessor theory;
5. extend the theory to multicore platforms;
6. introduce OS-level operational semantics; and
7. enrich the workload model with periodic, sporadic, and DAG-style task structures.

This separation is intended to improve both proof engineering and conceptual clarity. It avoids mixing semantic foundations with policy-specific proofs, avoids conflating abstract specifications with implementations, and makes future extensions easier to place within a clear architectural framework.
