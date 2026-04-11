# Scheduling Theory

This project is focused on the formalization of scheduling theory using the Rocq proof assistant.

# Design Principles

This project aims to provide a shared foundation for **executable scheduler semantics** and **scheduling-algorithm refinement**. Its central concern is not only whether scheduling theory can be stated abstractly, but also whether it can be connected to concrete scheduling choices, executable decision procedures, and implementation-oriented semantics. From this foundation, the project is intended to scale from **single-CPU scheduling**, to **multicore scheduling**, and eventually to **OS-level operational semantics**.

Desing principles are detailed in [DesignPrinciples.md](DesignPrinciples.md).

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
