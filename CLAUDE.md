# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This project formalizes real-time scheduling theory using the Rocq proof assistant.

The proof difficulty roadmap is in `plan/what_to_prove.md` (Lv.0–Lv.14: basic model integrity → EDF optimality → multiprocessor). The development methodology is in `plan/roadmap.md`.

### Supporting files

- `progress/` — canonical directory for proof planning and progress tracking:
  - `progress/<theorem>_plan.md` — proof strategy and sub-lemma proposals
  - `progress/<theorem>_progress.md` — completed sub-lemmas and remaining TODOs
- `proof_knowledge_base.md` (root) — accumulated lemma/tactic knowledge across sessions; read at the start of every proof session, update after every lemma attempt.
- `lessons_learned/`, `docker/` — excluded from Claude's context (denied in `.claude/settings.local.json`); do not attempt to read.

## Build

```bash
make          # compile all targets (EDF.vo, example_feasible.vo, example_schedulable.vo)
make clean    # remove .vo .glob .vok .vos .aux files
```

To compile a single file and its dependencies:

```bash
rocq compile Base.v
rocq compile Schedule.v     # requires Base.vo
rocq compile UniSchedulerInterface.v  # requires Schedule.vo Base.vo
rocq compile EDF.v          # requires UniSchedulerInterface.vo
rocq compile FIFO.v         # requires UniSchedulerInterface.vo
rocq compile Partitioned.v  # requires UniSchedulerInterface.vo
```

> **Note**: There is no `scheduling.v` file. Each file imports its dependencies explicitly.

## Module Architecture

Files are ordered by dependency:

```
Base.v
  └── Schedule.v
        └── UniSchedulerInterface.v
              ├── UniSchedulerLemmas.v   (policy-independent GenericSchedulerDecisionSpec lemmas)
              ├── EDF.v                  (EDF dispatcher + EDFSchedulerSpec)
              ├── FIFO.v                 (FIFO dispatcher + fifo_generic_spec)
              └── Partitioned.v          (Lv.5 multicore: static assignment lifting)
  └── PeriodicTasks.v                    (periodic task → job generation model)
```

| File | Contents |
|------|----------|
| `Base.v` | `JobId`, `TaskId`, `CPU`, `Time`; `Task`/`Job` records; `Schedule` type; `released`, `valid_jobs`, `valid_job_of_task` |
| `Schedule.v` | `runs_on`, `cpu_count`, `service_job`, `completed`, `eligible`, `ready`, `sequential_jobs`, `valid_schedule`, `missed_deadline`, `feasible_schedule`, `feasible`, `schedulable`; all Lv.0 lemmas |
| `UniSchedulerInterface.v` | `GenericSchedulerDecisionSpec` record: `choose_g` function + 4 specs (`choose_g_ready`, `choose_g_some_if_ready`, `choose_g_none_if_no_ready`, `choose_g_in_candidates`) |
| `UniSchedulerLemmas.v` | Policy-independent lemmas derived from `GenericSchedulerDecisionSpec` (soundness, coverage) |
| `EDF.v` | `choose_edf`, `edf_scheduler_spec : EDFSchedulerSpec`, EDF-specific lemmas |
| `FIFO.v` | `choose_fifo`, `fifo_generic_spec : GenericSchedulerDecisionSpec`, FIFO-specific lemmas |
| `Partitioned.v` | `assign`, `cpu_schedule`, `respects_assignment`, `valid_partitioned_schedule`; theorems: `service_decomposition`, `completed_iff_on_assigned_cpu`, `local_to_global_validity`, `missed_deadline_iff_on_assigned_cpu`, `local_feasible_implies_global_feasible_schedule`, `local_valid_feasible_implies_global` |
| `PeriodicTasks.v` | `generated_by_periodic_task` predicate, `expected_release`, `expected_abs_deadline` |

### Where new proofs go

- **Lv.0 (schedule-dependent definitions/lemmas)** → `Schedule.v`
- **Base types/schedule-independent notions** → `Base.v`
- **Policy-independent single-CPU results** → `UniSchedulerLemmas.v`
- **EDF-specific** → `EDF.v`; **FIFO-specific** → `FIFO.v`
- **Partitioned multicore (Lv.5+)** → `Partitioned.v`
- **Periodic task model** → `PeriodicTasks.v`

## Proof Workflow

**IMPORTANT**: Always invoke the `/rocq-prover` skill **before writing any Rocq code**, even after Plan mode. Do not implement proofs directly without going through the skill.

Use the `/rocq-prover` skill (`.claude/skills/ROCQ.md`) when proving theorems. The skill automates the three-step workflow:

1. **Plan** (`progress/<theorem>_plan.md`): Decompose the theorem into sub-lemmas and record the proof strategy before writing any Rocq.
2. **Sub-lemmas** (`progress/<theorem>_progress.md`): Prove one sub-lemma at a time; update the progress file after each. Use `Admitted` for not-yet-proven steps to keep the file compiling.
3. **Assemble**: Once all sub-lemmas are proven, prove the top-level theorem and record completion.

If a sub-lemma repeatedly fails, classify the cause (script/tactic issue, missing intermediate lemma, or wrong/too-strong statement). After 2-3 failed attempts with the same strategy, revise the plan instead of retrying unchanged. For likely false or out-of-scope statements, record diagnostics in `progress/<theorem>_progress.md` and remove/replace them in `progress/<theorem>_plan.md`.

Verify each step by compiling the relevant file (no errors = proof accepted). For example, after editing `Partitioned.v`:

```bash
rocq compile Base.v && rocq compile Schedule.v && rocq compile UniSchedulerInterface.v && rocq compile Partitioned.v
```

**Token management**: Use `/clear` between sub-lemma proofs to avoid hitting context limits. The progress file persists state across sessions.

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
