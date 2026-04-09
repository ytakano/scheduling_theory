# Scheduling Theory

This project is focused on the formalization of scheduling theory using the Rocq proof assistant.

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
