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

## Proof Workflow

**IMPORTANT**: Always invoke the `/rocq-prover` skill **before writing any Rocq code**, even after Plan mode. Do not implement proofs directly without going through the skill.

Use the `/rocq-prover` skill (`.claude/skills/ROCQ.md`) when proving theorems. The skill automates the three-step workflow:

1. **Plan** (`progress/<theorem>_plan.md`): Decompose the theorem into sub-lemmas and record the proof strategy before writing any Rocq.
2. **Sub-lemmas** (`progress/<theorem>_progress.md`): Prove one sub-lemma at a time; update the progress file after each. Use `Admitted` for not-yet-proven steps to keep the file compiling.
3. **Assemble**: Once all sub-lemmas are proven, prove the top-level theorem and record completion.

If a sub-lemma repeatedly fails, classify the cause (script/tactic issue, missing intermediate lemma, or wrong/too-strong statement). After 2-3 failed attempts with the same strategy, revise the plan instead of retrying unchanged. For likely false or out-of-scope statements, record diagnostics in `progress/<theorem>_progress.md` and remove/replace them in `progress/<theorem>_plan.md`.

Verify each step with `rocq compile scheduling.v` (no compilation errors = proof accepted). All proofs live in the single file `scheduling.v` at the project root.

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

