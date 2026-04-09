# Copilot Instructions

## Project Overview

This project formalizes real-time scheduling theory in Rocq. The core model covers multiprocessor schedules, job eligibility/readiness, feasibility, and dispatch policies (EDF, FIFO, partitioned multiprocessor). The long-term goal includes periodic task theory, utilization bounds, and DAG-job extensions.

- Proof roadmap: `plan/what_to_prove.md`
- Development roadmap: `plan/roadmap.md`
- Accumulated proof notes: `proof_knowledge_base.md`

### Supporting files

- `progress/` — canonical directory for proof planning and progress tracking:
  - `progress/<theorem>_plan.md` — proof strategy and sub-lemma proposals
  - `progress/<theorem>_progress.md` — completed sub-lemmas and remaining TODOs
- `generator_order.md`, `generator_order_progress.md` (root) — legacy files, superseded by `progress/` versions; ignore these.
- `docker/` — excluded from Copilot's context

## Proof Workflow

**IMPORTANT**: Always invoke the `/rocq-prover` skill **before writing any Rocq code**, even after Plan mode. Do not implement proofs directly without going through the skill.

Use the `/rocq-prover` skill (`.github/skills/ROCQ/SKILL.md`) when proving theorems. The skill automates the three-step workflow:

1. **Plan** (`progress/<theorem>_plan.md`): Decompose the theorem into sub-lemmas and record the proof strategy before writing any Rocq.
2. **Sub-lemmas** (`progress/<theorem>_progress.md`): Prove one sub-lemma at a time; update the progress file after each. Use `Admitted` for not-yet-proven steps to keep the file compiling.
3. **Assemble**: Once all sub-lemmas are proven, prove the top-level theorem and record completion.

If a sub-lemma repeatedly fails, classify the cause (script/tactic issue, missing intermediate lemma, or wrong/too-strong statement). After 2-3 failed attempts with the same strategy, revise the plan instead of retrying unchanged. For likely false or out-of-scope statements, record diagnostics in `progress/<theorem>_progress.md` and remove/replace them in `progress/<theorem>_plan.md`.

Verify each step with `rocq compile <file>.v` (no compilation errors = proof accepted).

**Token management**: Use `/clear` between sub-lemma proofs to avoid hitting context limits. The progress file persists state across sessions.

## Build

```bash
make          # compile all targets
make clean    # remove *.vo *.glob *.vok *.vos *.aux
```

Compile a single file (must compile dependencies first):

```bash
rocq compile Base.v
rocq compile ScheduleModel.v
rocq compile SchedulerInterface.v
rocq compile DispatchInterface.v
rocq compile DispatchSchedulerBridge.v
rocq compile EDF.v
rocq compile FIFO.v
rocq compile Partitioned.v
```

For containerized work: `sh docker/build.sh`, `sh docker/up_docker.sh`, `sh docker/exec_zsh.sh`.

## Module Architecture

```text
Base.v
  -> ScheduleModel.v
  -> SchedulerInterface.v
  -> DispatchInterface.v
  -> DispatchSchedulerBridge.v
  -> EDF.v / FIFO.v / Partitioned.v
  -> SchedulableExamples.v / FeasibleExamples.v / FIFOExamples.v
```

| File | Key definitions |
|------|-----------------|
| `Base.v` | `JobId`, `TaskId`, `CPU`, `Time`, `Job`, `Task`, `Schedule` (= `Time -> CPU -> option JobId`), `released`, `valid_jobs`, `valid_job_of_task` |
| `ScheduleModel.v` | `runs_on`, `cpu_count`, `service_job`, `completed`, `running`, `eligible`, `ready`, `readyb`/`eligibleb`, `sequential_jobs`, `valid_schedule`, `feasible_schedule`, `feasible_schedule_on` |
| `SchedulerInterface.v` | `Scheduler` record (`scheduler_rel`); `schedulable_by`, `schedulable_by_on` |
| `DispatchInterface.v` | `GenericDispatchSpec` record with 4 fields: `dispatch_eligible`, `dispatch_some_if_eligible_candidate`, `dispatch_none_if_no_eligible_candidate`, `dispatch_in_candidates` |
| `DispatchSchedulerBridge.v` | Single-CPU dispatch→scheduler bridge; `CandidateSourceSpec`; subset schedulability helpers |
| `DispatchLemmas.v` | Policy-independent dispatch lemmas (constructive) |
| `DispatchClassicalLemmas.v` | Classical (excluded-middle) dispatch lemmas |
| `EDF.v` | EDF dispatcher, `edf_generic_spec`, `edf_scheduler` |
| `FIFO.v` | FIFO dispatcher, `fifo_generic_spec`, `fifo_scheduler` |
| `Partitioned.v` | Partitioned multiprocessor scheduler; validity/feasibility lifting from per-CPU to global |
| `PeriodicTasks.v` | Periodic task model (skeleton; not yet used in proofs) |

**Separation of concerns**: schedule semantics → `ScheduleModel.v`; abstract scheduler reasoning → `SchedulerInterface.v`; policy-independent dispatch → `DispatchInterface.v` / `DispatchSchedulerBridge.v`; policy-specific lemmas → `EDF.v`, `FIFO.v`; multiprocessor lifting → `Partitioned.v`; classical results → `DispatchClassicalLemmas.v`.

## Key Conventions

### `eligible` vs `ready`
- `eligible j t` = released AND NOT completed. Running jobs satisfy `eligible`.
- `ready j t` = eligible AND NOT running. Classical "ready queue" state.
- `valid_schedule` is stated with `eligible` (not `ready`) because running jobs are eligible but not ready.
- `readyb` / `eligibleb` are boolean versions for use in `filter` (e.g., building candidate lists).

### Rocq 9 tactic pitfalls
- Use `injection H as Heq; subst` — **not** `injection H as ->` (syntax error in Rocq 9).
- When applying `proj1`/`proj2` of an IH in inductive proofs where a variable with the same name is already in scope, apply on the **goal** (`apply (proj1 (IH ...) H)`) rather than using `apply ... in H` — the latter causes "Unable to find an instance" errors.

### Proof structure
- Use `Admitted` to keep files compiling while sub-lemmas are in progress.
- Constructive results go in the main policy file or `DispatchLemmas.v`; classical results (those requiring `Classical_Prop`) go in `DispatchClassicalLemmas.v`.
- New lemmas are catalogued in `proof_knowledge_base.md` with statement, strategy, key tactics, dependencies, and known pitfalls.

### Historical names to ignore
Files in `plan/` and `progress/` may reference superseded identifiers (`run_scheduler`, `dispatch_ready`, `local_to_global_validity`). The current `.v` files are the source of truth.

## Reasoning Policy

Before responding to any request, first assess the required reasoning depth:

- **Simple** (e.g., factual lookup, single-file edit): Respond directly.
- **Moderate** (e.g., multi-file refactor, debugging): Think through the approach briefly before acting.
- **Complex** (e.g., architecture design, algorithm design, proof): Use extended reasoning — break the problem into sub-problems, consider trade-offs, then proceed step by step.

Always make your reasoning depth assessment explicit before responding:
> "This is a [simple/moderate/complex] task because ..."

## External Resources

- Rocq Standard Library
  - <https://rocq-prover.org/doc/V9.1.0/refman-stdlib/index.html>
  - <https://rocq-prover.org/doc/V9.1.0/stdlib/index.html>
