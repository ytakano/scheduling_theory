# Repository Guidelines

## Project Structure & Module Organization
This repository formalizes scheduling theory in Rocq. Core proof files live at the repository root. Follow the dependency flow when adding definitions or lemmas: `Base.v` -> `ScheduleModel.v` -> `SchedulerInterface.v` -> `SchedulingAlgorithmInterface.v` -> policy files such as `UniPolicies/EDF.v`, `UniPolicies/FIFO.v`, and `Partitioned.v`. Example and proof-consumer files include `FeasibleExamples.v`, `FIFOExamples.v`, and `SchedulableExamples.v`.

Planning and proof notes belong in [`plan/`](./plan) and [`progress/`](./progress). Docker helper scripts live in [`docker/`](./docker). Generated build artifacts such as `*.vo`, `*.vos`, `*.vok`, `*.glob`, and `*.aux` should not be committed.

## Build, Test, and Development Commands
Use `make` to compile the main targets listed in `Makefile`. Use `make clean` to remove generated Rocq artifacts.

Compile a single file with Rocq when iterating locally:

```bash
rocq compile Base.v
rocq compile ScheduleModel.v
rocq compile Partitioned.v
```

Rocq compilation is the test mechanism here: a file passes when it compiles with all dependencies satisfied. For containerized work, use `sh docker/build.sh`, `sh docker/up_docker.sh`, and `sh docker/exec_zsh.sh`.

## Coding Style & Naming Conventions
Use spaces for indentation and keep record fields and proof scripts vertically aligned when it improves readability. Prefer descriptive PascalCase filenames for major modules and example files, matching current names such as `ScheduleModel.v` and `FIFOExamples.v`.

Use clear identifier names that reflect proof intent: `eligible`, `dispatch_in_candidates`, `valid_partitioned_schedule`. Keep constructive results separate from classical ones; classical lemmas belong in files like `SchedulingAlgorithmClassicalLemmas.v`.

## Testing Guidelines
There is no separate test framework or coverage gate. Validate every change by compiling the edited file and any impacted dependents. For cross-cutting changes, run `make` before opening a PR.

When adding examples, keep them in dedicated `*Examples.v` files and name lemmas consistently with the property being demonstrated.

## Commit & Pull Request Guidelines
Recent history favors short imperative subjects, often with a scope prefix, for example `refactor: replace ready with eligible in dispatch interface` or `phase 3: rewrite Partitioned.v to local-view dispatch`. Keep the first line specific and under control; explain proof strategy or refactor impact in the body when needed.

Pull requests should summarize the theorem, model change, or refactor, list affected modules, and note the exact compile commands you ran. Include links to relevant `plan/` or `progress/` documents when the change follows an existing proof plan.

## External Libraries

### rocq-stdpp (version 1.13.0)

[rocq-stdpp](https://plv.mpi-sws.org/coqdoc/stdpp/) is installed and available. Prefer stdpp over the Rocq standard library when it offers a more convenient interface — in particular for decidability, finite maps, sets, and list automation.

**Import syntax:**

```coq
From stdpp Require Import base.        (* general automation: done, by, ... *)
From stdpp Require Import decidable.   (* Decision typeclass *)
From stdpp Require Import fin_maps.    (* FinMap interface *)
From stdpp Require Import gmap.        (* generic finite map (hash-map) *)
From stdpp Require Import list.        (* list lemmas and tactics *)
From stdpp Require Import sets.        (* set typeclass hierarchy *)
From stdpp Require Import sorting.     (* merge_sort, Sorted *)
From stdpp Require Import relations.   (* rtc, tc, ... *)
From stdpp Require Import numbers.     (* Z/N utilities *)
```

Or import the full prelude at once:

```coq
From stdpp Require Import prelude.
```

**Key modules and when to use them:**

| Module | Use case |
|--------|----------|
| `base` | General-purpose automation (`done`, `by`, `naive_solver`, `set_solver`); typeclass infrastructure |
| `decidable` | `Decision` typeclass; `decide` tactic for decidable propositions |
| `list` | Rich list lemmas (`Forall`, `NoDup`, lookup, `elem_of`, `filter`) and the `list_simplifier` tactic |
| `fin_maps` / `gmap` | Finite maps with `lookup`, `insert`, `delete`; prefer over `Stdlib` `FMap` |
| `sets` / `fin_sets` | Set typeclasses (`∈`, `∪`, `∩`, `⊆`); `set_solver` tactic |
| `sorting` | `Sorted`, `StronglySorted`, `merge_sort` with permutation lemmas |
| `relations` | Reflexive-transitive closure (`rtc`), transitive closure (`tc`) |
| `numbers` | Extra lemmas for `nat` and `Z` |

**Notes:**
- stdpp uses `∈`, `∪`, `∩`, `⊆` notation — ensure `From stdpp Require Import sets.` (or `prelude`) is imported before using these.
- The `done`, `naive_solver`, and `set_solver` tactics from `base` replace many manual `tauto`/`auto`/`firstorder` calls.
- stdpp's `list` shadows some `Stdlib.List` names; import order matters when mixing both.
