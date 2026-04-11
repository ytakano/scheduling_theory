## Design Principles

This project aims to provide a shared foundation for **executable scheduler semantics** and **scheduling-algorithm refinement**. Its central concern is not only whether scheduling theory can be stated abstractly, but also whether it can be connected to concrete scheduling choices, executable decision procedures, and implementation-oriented semantics. From this foundation, the project is intended to scale from **single-CPU scheduling**, to **multicore scheduling**, and eventually to **OS-level operational semantics**.

### 1. Executable semantics first

The project treats scheduler semantics as a primary object of formalization. The goal is to define what a scheduler means, what it means for a schedule to satisfy a policy, and how concrete scheduling decisions can be represented in a mechanized and executable way.

### 2. Refinement as a core design objective

Refinement is a first-class goal. The framework is designed to connect abstract scheduling policies with concrete scheduling algorithms through explicit refinement statements, so that correctness can be established not only at the level of abstract specifications, but also at the level of executable decision procedures.

### 3. Clear separation between policy, validity, and scheduling algorithm

A key design principle is to separate the abstract scheduling policy, the validity conditions for schedules, the concrete scheduling algorithm that makes choices, and the refinement argument that connects the algorithm to the policy. This separation keeps specifications modular and reusable while preserving a clear path from theory to implementation.

### 4. End-to-end mechanization of scheduling algorithms

For concrete algorithms, the objective is not merely to restate classical results, but to mechanize the full path from policy to executable choice. This includes finite candidate reasoning, tie handling, schedule transformations, swap lemmas, and proofs that an executable chooser implements the intended scheduling discipline.

### 5. Multicore as an early semantic target

Multicore scheduling is treated as an early semantic concern rather than a late extension. The project is structured to support partitioned, global, clustered, affinity-aware, and migration-aware scheduling within a common schedule-level framework, so that multicore semantics can be developed systematically rather than retrofitted afterward.

### 6. Toward OS-level operational models

The long-term direction is to move beyond abstract scheduling models toward operational semantics that are closer to actual systems. This includes concepts such as runqueues, the current task, wakeup and blocking events, dispatch and preemption points, migration events, and timer- or IPI-driven scheduling behavior.

### 7. Task models as extensions over a semantic core

Periodic and sporadic task models remain important, but they are treated as higher-level layers that connect to the semantic core rather than define it. This keeps the framework centered on scheduler meaning and correctness, while still supporting later development of workload models and analysis results.

### 8. Analysis built on top of semantics

Schedulability analysis is an important outcome, but it is not the organizing principle of the framework. The intended architecture is to place analysis on top of a precise account of scheduler semantics, executable scheduling algorithms, and refinement, rather than to make analysis artifacts the primary structure of the development.

### 9. Related Work

A natural point of comparison is **Prosa**, a mechanized framework for real-time scheduling theory. Prosa places verified schedulability analysis at the center of its design and provides substantial libraries for priority models, schedule models, interference reasoning, response-time analysis, and classical results such as EDF-related optimality and schedulability theorems. By contrast, this project takes **executable scheduler semantics** and **scheduling-algorithm refinement** as its organizing principles. The difference is therefore not whether familiar scheduling algorithms are formalized, but how far the mechanization is intended to proceed: from abstract policy, to executable chooser, to multicore semantics, and ultimately to OS-facing operational models.
