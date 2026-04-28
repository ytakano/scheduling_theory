# RocqSched: Bridging Scheduling Theory and OS-Level Scheduler Semantics in Rocq

**RocqSched** is a Rocq library for scheduling theory, executable scheduler
models, scheduler semantic layers, and refinement theories.

The library is organized around scheduler semantic layers.

- **Schedule semantics** is the mathematical schedule model used by policy
  specifications and schedulability analysis.
- **Trace semantics** describes observable scheduling events and connects
  execution logs to schedule-level reasoning.
- **OS-level scheduler operational semantics** models implementation-facing
  scheduler mechanisms as state transitions that produce traces.

RocqSched also separates semantic objects from reasoning theories.

- **Analysis theory** proves timing and schedulability properties over schedule
  semantics.
- **Refinement theory** connects executable algorithms, operational executions,
  traces, schedules, and abstract policy specifications.
- **Executable scheduler models** provide decision procedures whose behavior can
  be related back to declarative scheduling specifications.

This structure supports reusable developments across scheduler policies, task
models, uniprocessor and multicore settings, trace-based validation, and
OS-level scheduler modeling.

The long-term goal of RocqSched is to provide a reusable formal foundation that
connects scheduling theory, executable scheduler models, trace semantics,
OS-level operational semantics, and schedulability analysis in a single Rocq
development.

# Design Principles and Design

- Design principles are detailed in [DesignPrinciples.md](DesignPrinciples.md).
- Design documents are in [Design.md](Design.md).

# Plan

- Roadmap: [plan/roadmap.md](plan/roadmap.md)
- What to Prove: [plan/what_to_prove.md](plan/what_to_prove.md)


# Adding a New File

To add a new file to the project, follow these steps:

1. Create a new `NewFile.v` in the `theories` directory.
2. Add the new file to the `_CoqProject` file.
3. Create a new Makefile by `rocq makefile -f _CoqProject -o Makefile`.

# Compilation

```text
rocq makefile -f _CoqProject -o Makefile
make clean && make
```
