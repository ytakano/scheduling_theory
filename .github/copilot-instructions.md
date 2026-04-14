# Repository Guidelines

## Purpose

This repository contains Rocq developments for scheduling theory, refinement,
and OS-oriented verification.

This file is the entry point for agent behavior in the repository.
It does not contain all detailed proof guidance itself.
Instead, it tells the agent:
- which documents to consult,
- which rules always apply,
- and how to choose the right abstraction layer before editing.

The repository values:
- semantic clarity,
- clean architectural layering,
- reusable lemmas and interfaces,
- constructive proof development when possible,
- and maintainable proof scripts.

---

## Scope of this file

This file defines repository-wide rules only.

Use this file for:
- document precedence,
- repository priorities,
- file-selection workflow,
- architecture and roadmap alignment,
- and output expectations.

Do not treat this file as a substitute for specialized guidance.

Specialized guidance lives in:
- `ROCQ_AGENT.md`
- `STDPP_AGENT.md`
- `design/` documents
- `plan/roadmap.md`
- `plan/what_to_prove.md`

---

## Document precedence

When working in this repository, use the following precedence order:

1. repository-wide architectural constraints and safety rules
2. specialized guidance files for the touched subsystem or library
3. local file conventions near the edited development
4. local proof tactics and helper lemmas

When documents overlap, prefer the more specific one within its scope.

---

## What to read before editing

Before making nontrivial changes, consult the relevant documents below.

### Always relevant for nontrivial work
- `plan/roadmap.md`
- `plan/what_to_prove.md`
- `design/` documents when architecture or abstraction boundaries matter

### For any Rocq proof development
- `ROCQ_AGENT.md`

### For files using stdpp
- `STDPP_AGENT.md`

Do not start patching proofs before checking whether a guidance file already
covers the area.

---

## Mandatory trigger for `ROCQ_AGENT.md`

Read `ROCQ_AGENT.md` before editing when:
- the target file is a `.v` file,
- theorem statements are being added or changed,
- definitions are being added or changed,
- an induction, inversion, or helper-lemma refactor is likely,
- constructive vs classical style may matter,
- or proof maintainability is part of the task.

For Rocq developments, `ROCQ_AGENT.md` is the default specialized guide.

---

## Mandatory trigger for `STDPP_AGENT.md`

Read `STDPP_AGENT.md` before editing when a file does any of the following:
- imports `stdpp`
- uses `gmap`, `gset`, `mapset`, or `dom`
- uses lookup notation such as `!!`
- uses set notation such as `∈`, `∉`, `⊆`, `∪`, `∩`, `∖`
- uses stdpp tactics such as:
  - `set_solver`
  - `simplify_map_eq`
  - `simplify_eq`
  - `done`
  - `naive_solver`
  - `tc_solve`

When in doubt, consult `STDPP_AGENT.md`.

---

## Repository-level priorities

Unless the task explicitly says otherwise, prioritize work in this order:

1. semantic clarity
2. abstraction layering
3. refinement structure
4. reusable interfaces and helper lemmas
5. proof maintainability
6. extension to richer task models
7. proof automation polish

Do not optimize for isolated theorem count.
Optimize for structure that makes later theorems easier to state and prove.

---

## Architectural layering policy

Preserve conceptual boundaries between layers such as:
- schedule semantics,
- scheduling algorithm interfaces,
- scheduler or execution mechanisms,
- invariants,
- refinement theorems,
- task models,
- and analysis-specific results.

Do not collapse these layers merely to simplify one local proof.

When a proof is difficult because boundaries are blurred, prefer:
- a better intermediate lemma,
- a cleaner interface,
- or a clarified invariant,

rather than bypassing the architecture.

---

## Definition-change policy

When changing or adding definitions:
- preserve the semantic role of the file,
- use only assumptions actually needed,
- avoid proof-specific encodings in core definitions,
- do not duplicate existing concepts under slightly different names,
- and keep executable and semantic notions conceptually distinct unless the file
  is explicitly about their connection.

If a definition changes architectural boundaries, update design documents.

---

## Theorem-change policy

When changing theorem statements:
- first ask whether the original statement was at the correct abstraction layer,
- prefer interface lemmas when a theorem crosses layers,
- prefer reusable statements over overly local ones,
- and avoid names tied to the current proof trick.

Do not strengthen assumptions merely because the current proof would become
shorter.

---

## Helper-lemma policy

Add a helper lemma when it:
- captures a recurring argument,
- isolates an invariant or normalization step,
- clarifies a layer boundary,
- or significantly simplifies later theorems.

Do not add helper lemmas that only rename a trivial local proof step.

Place helper lemmas at the abstraction level where they naturally belong.

---

## Documentation-update policy

Update design documentation when:
- a new abstraction layer is introduced,
- responsibility moves between layers,
- a core interface changes meaning,
- a new refinement boundary is established,
- or a new task-model family is added in a structurally important way.

Do not update design documents for purely local proof cleanup.

A good rule:
- implementation-only cleanup -> no design update required
- semantic, interface, or layering change -> design update required

---

## Roadmap alignment policy

When choosing what to implement next, prefer work that:
- matches the current roadmap ordering,
- unblocks later proof dependencies,
- stabilizes architecture,
- or increases reuse across scheduler or task-model variants.

Do not choose tasks only because they are easy to finish in isolation.

---

## Import policy

Keep imports minimal and intentional.

Do not:
- add broad imports without need,
- rely on accidental transitive imports when clarity matters,
- or mix import styles randomly across nearby files.

For stdpp-specific import discipline, use `STDPP_AGENT.md`.

For constructive and classical import discipline, use `ROCQ_AGENT.md`.

---

## Naming policy

Choose names that are:
- semantically meaningful,
- stable under proof refactoring,
- consistent with neighboring files,
- and explicit about abstraction level when needed.

Avoid:
- vague helper names,
- temporary-sounding names,
- names tied only to proof order,
- or names that describe only the proof method.

---

## Comments and documentation style

Comments should explain:
- semantic intent,
- why a lemma matters,
- which interface or layer it serves,
- or why a decomposition is architecturally important.

Do not add comments that merely narrate obvious tactic steps.

For central definitions and theorems, prefer comments that explain how they fit
into semantics, refinement, or task-model structure.

---

## Map and set policy

For finite maps, sets, and domains:
- follow `STDPP_AGENT.md`,
- normalize goals early,
- prefer lookup-based reasoning for maps,
- convert `dom` facts into lookup-existence facts early,
- and use standard stdpp automation for routine obligations.

Do not re-encode stdpp proof discipline inside `AGENTS.md`.

---

## Constructive development policy

This repository prefers constructive developments whenever practical.

For constructive-vs-classical proof policy, consult `ROCQ_AGENT.md`.

Do not introduce classical reasoning casually.
Do not assume that shorter classical proofs are automatically preferable.

---

## Expected workflow before editing

Before editing a nontrivial Rocq file, the agent should:
1. identify the abstraction layer,
2. read nearby definitions and theorem statements,
3. check roadmap and design intent,
4. consult `ROCQ_AGENT.md`,
5. consult `STDPP_AGENT.md` if stdpp is involved,
6. identify existing invariants and reusable lemmas,
7. only then implement changes.

For architectural edits, also check whether documentation must be updated.

---

## Preferred behavior when stuck

If progress is blocked, do not immediately escalate tactical complexity.

Try, in order:
1. restating the goal at the correct layer,
2. checking whether an existing canonical lemma already solves the shape,
3. introducing a reusable helper lemma,
4. strengthening or clarifying an invariant,
5. splitting a theorem into interface lemma plus final theorem,
6. then reconsidering automation.

Prefer structural cleanup over brute-force proof scripting.

---

## Output expectations

When proposing or making nontrivial changes, clearly state:
- which files were changed,
- which abstraction layer is affected,
- whether the change is semantic, structural, or proof-local,
- whether design documents should also be updated,
- which main idea, invariant, or standard tactic pattern was used,
- and what remains unresolved, if anything.

Do not describe work as complete if proof obligations remain open.

---

## Final rule

Favor structure over patching.

A good change in this repository should make the next theorem,
the next refinement step, or the next task-model extension easier to understand,
reuse, and maintain.
