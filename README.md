# RocqSched: Bridging Scheduling Theory and Executable Scheduler Semantics in Rocq

**RocqSched** is a Rocq library for scheduling theory, executable scheduler semantics, and refinement between abstract scheduling specifications and concrete scheduling algorithms.

The library is built around a layered view of scheduling.

- A **schedule** is treated as the semantic object: an execution timeline that describes which job runs on which CPU at each time.
- A **scheduling algorithm** is treated as an executable decision procedure that selects jobs based on the current system state.
- A **scheduler** connects algorithmic decisions with semantic validity conditions and system-level constraints.
- **Refinement** is used to relate executable scheduling rules to abstract scheduling specifications.

This structure is intended to support both foundational scheduling theory and extensible system modeling. RocqSched is designed to grow from uniprocessor models to multicore scheduling, and further toward OS-level semantics. It also aims to support richer task models, including periodic and DAG-based workloads, within the same overall framework.

The long-term goal of RocqSched is not only to verify isolated scheduling results, but to provide a reusable formal foundation that connects scheduling theory, executable schedulers, and system semantics in a single Rocq development.

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

# Rocq Compiler

```text
rocq makefile -f _CoqProject -o Makefile
make
```

Compilation is the test mechanism in this repository.

```
rocq makefile -f _CoqProject -o Makefile
make clean && make
```
