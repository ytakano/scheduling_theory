---
name: rocq-prover
description: Use this skill when the user wants to prove theorems, lemmas, definitions, or propositions in Rocq/Coq. Activated when the user mentions proving, verifying, or formalizing mathematical statements in Rocq or Coq.
---

# Rocq/Coq Prover

This skill guides you through proving theorems and lemmas in Rocq/Coq by proposing auxiliary lemmas, proof strategies, and tracking progress across sessions.

## Key Files and Directories

| Path | Purpose |
|------|---------|
| `progress/` | Directory for storing all proof progress and planning files |
| `progress/<name>_plan.md` | Proof strategy and proposed lemmas for a given theorem/lemma |
| `progress/<name>_progress.md` | Completed proofs and remaining TODOs for a given theorem/lemma |

Replace `<name>` with the theorem or lemma name (e.g., `nat_add_comm_plan.md`).

---

## Workflow

### Step 1: Plan — Propose a Proof Strategy

When the user presents a theorem or lemma to prove:

> **MANDATORY**: Before doing anything else, read `proof_knowledge_base.md` (if it exists) to check for relevant proven results, reusable tactics patterns, and known pitfalls from previous sessions. If the file does not exist, proceed without it — it will be created when the first lemma is proven.

1. Check whether `progress/<name>_plan.md` already exists.
   - If it **does not exist**, create it and proceed to step 2.
   - If it **exists**, read it and skip to Step 2.
2. Analyze the goal and propose:
   - A high-level proof strategy
   - A list of auxiliary lemmas needed
   - The recommended order in which to prove them
3. Write the proposal to `progress/<name>_plan.md` using the template below.
4. Proceed to Step 2.

**`<name>_plan.md` template:**
```markdown
# Proof Plan: <Theorem/Lemma Name>

## Goal
<State the theorem or lemma to be proved>

## Proof Strategy
<Describe the overall approach>

## Proposed Lemmas
- [ ] `lemma_1`: <description>
- [ ] `lemma_2`: <description>
...

## Proof Order
1. `lemma_1`
2. `lemma_2`
...
N. `<name>` (main goal)
```

---

### Step 2: Prove — Work Through Lemmas One at a Time

> **BLOCKING REQUIREMENT**: After completing or abandoning each lemma attempt — whether compilation succeeds or fails — you **MUST** update `progress/<name>_progress.md` **before** moving on to the next lemma. Skipping this update is a workflow violation and must not occur under any circumstances.

1. Read `progress/<name>_plan.md` to review the strategy and lemma list.
   - If the file does not exist, return to Step 1.
2. Read `progress/<name>_progress.md` if it exists, to check what has already been proved and what TODOs remain.
3. Select **one** unproved lemma and attempt to prove it.
4. Verify the proof by running:
   ```
   rocq compile <filename>
   ```
   - If compilation fails, classify the failure before retrying:
     - **Syntax/Tactic failure**: revise proof script and retry.
     - **Missing dependency**: add required lemmas to `progress/<name>_plan.md` and prove them first.
     - **Potentially false statement / insufficient assumptions**: escalate to plan revision (see "Handling Failed and Unprovable Statements").
   - Do not repeat the same strategy indefinitely. If the same approach fails after 2-3 attempts, revise the plan instead of continuing blind retries.
5. **MANDATORY — Update `progress/<name>_progress.md` immediately**, regardless of whether compilation succeeded or failed:
   - On success: add the completed lemma under `## Completed Lemmas` with its proof code, and remove it from `## TODO`.
   - On failure / `Admitted`: record status and diagnosis under `## Proof Attempts & Diagnostics`, then update `## TODO`.
6. **Verify the update**: read back `progress/<name>_progress.md` to confirm the file reflects the latest state.
7. **MANDATORY — Update `proof_knowledge_base.md` immediately** after step 6:
   - On **success**: add or update an entry for the lemma using the template in the "Proof Knowledge Base" section. Include the statement, proof strategy, key tactics used, and any notable pitfalls encountered.
   - On **failure / abandoned**: add a note about the failed approach under the lemma's `Notes` field so future sessions avoid repeating the same dead end. If no entry exists yet, create a minimal entry with the failure diagnosis.
8. **Verify the update**: read back `proof_knowledge_base.md` to confirm the entry was written correctly.
9. **CHECKPOINT**: Confirm that both `progress/<name>_progress.md` and `proof_knowledge_base.md` are up to date before selecting the next lemma. Do not proceed until this checkpoint passes.
10. Repeat from step 3 until all lemmas are proved, then proceed to Step 3.

**`<name>_progress.md` template:**
~~~markdown
# Proof Progress: <Theorem/Lemma Name>

## Status Overview
- Overall: [In Progress | Blocked | Complete | Abandoned]
- Complete Lemmas: <n>/<m>
- Unproven (`Admitted`): <list or none>
- Failed/Abandoned Items: <list or none>

## Completed Lemmas
### `lemma_1`

```coq
<proof code>
```

## Proof Attempts & Diagnostics
### `lemma_2` — Status: [Blocked | Admitted | Abandoned]

- Attempt 1 (<YYYY-MM-DD>):
   - Error: <rocq error or concise failure description>
   - Diagnosis: <root cause>
   - Next action: <retry with change / add lemma / revise plan>

## TODO
- [ ] `lemma_2`
- [ ] `<name>` (main goal)
~~~

---

### Step 3: Conclude — Prove the Main Theorem or Lemma

1. Read `progress/<name>_plan.md` to recall the overall strategy.
2. Read `progress/<name>_progress.md` to confirm all required lemmas are proved.
3. Using the completed lemmas, write and verify the proof of the main theorem or lemma.
4. Verify with:
   ```
   rocq compile <filename>
   ```
   - If compilation succeeds:
     1. Record the final proof in `progress/<name>_progress.md` and mark the goal as complete.
     2. **MANDATORY — Update `proof_knowledge_base.md`** with an entry for the main theorem (statement, proof strategy, key lemmas used, date).
     3. Verify the update: read back `proof_knowledge_base.md` to confirm the entry was written.
   - If compilation fails, analyze the failure, revise the strategy or add new lemmas as needed, update `progress/<name>_plan.md`, and return to Step 2.

---

## Proof Verification

All proofs must be verified by successful compilation:

```bash
rocq compile <filename>
```

A proof is considered complete only when there are **no compilation errors**. If errors occur, treat them as evidence of an incorrect or incomplete proof and revise accordingly.

---

## Handling Failed and Unprovable Statements

Not every attempted statement is true or derivable from the current assumptions. When repeated failures suggest this, use the workflow below.

### 1) Classify the Failure

- **Implementation issue**: tactics, term construction, or local script mistakes.
- **Dependency issue**: missing intermediate lemmas or missing reusable facts.
- **Statement issue**: the statement is false, too strong, or missing assumptions.

### 2) Escalate After Bounded Retries

- After 2-3 failed attempts using the same strategy, stop and revise the plan.
- Update `progress/<name>_progress.md` immediately with diagnosis before switching tasks.

### 3) If the Statement Appears False or Unprovable

1. Record the reason in `progress/<name>_progress.md` under `## Proof Attempts & Diagnostics`.
2. Update `progress/<name>_plan.md` to either:
   - replace the statement with a corrected one, or
   - add the missing assumptions explicitly, or
   - remove the statement from the active proof path if it is outside scope.
3. Keep the workflow explicit:
   - Use `Admitted` only as a temporary marker for potentially true but unfinished goals.
   - Do **not** keep permanently false statements as `Admitted` placeholders.

### 4) Final Goal States

- **Complete**: all required lemmas and the main goal compile without `Admitted`.
- **In Progress**: work is active and remaining gaps are tracked.
- **Blocked**: currently stuck, with diagnostics and next action recorded.
- **Abandoned**: goal removed from active scope because it is false in the current formalization context or requires assumptions outside the accepted context; reason must be documented in plan/progress files.

---

## Proof Knowledge Base

Maintain a persistent record of proven results in `proof_knowledge_base.md` at the project root. This file accumulates reusable knowledge across all proof sessions.

### Rules

- **MANDATORY**: Read `proof_knowledge_base.md` at the very start of Step 1 (before planning) to leverage prior results and avoid dead ends.
- **MANDATORY**: Update `proof_knowledge_base.md` after every lemma compilation attempt (Step 2, step 7) and after the main theorem is proven (Step 3).
- If the file does not exist, create it the first time a lemma is successfully compiled. Use the template below.

### `proof_knowledge_base.md` Template

~~~markdown
# Proof Knowledge Base

## Lemmas and Theorems

### `lemma_name`
- **Type**: Lemma / Theorem / Definition / Instance
- **Statement**:
  ```coq
  <Rocq statement>
  ```
- **Proof Strategy**: <brief description of the overall approach>
- **Key Tactics**: <comma-separated list, e.g., `omega`, `induction n`, `apply gpow_add`, `rewrite`>
- **Dependencies**: <lemmas/theorems this proof relies on>
- **Notes**: <pitfalls, important observations, or failed approaches to avoid>
- **Date**: YYYY-MM-DD
~~~

### What to Record

| Situation | What to write |
|-----------|--------------|
| Lemma compiled successfully | Full entry using the template above |
| Lemma failed / `Admitted` | Minimal entry with failure diagnosis in `Notes` to warn future sessions |
| Failed approach to avoid | Add a bullet in `Notes` starting with "⚠️ Dead end:" |

## Notes

- Although this skill uses "theorem" and "lemma" throughout, the same workflow applies to **any provable Rocq/Coq construct**: definitions, propositions, instances, etc.
- Name your progress files after the specific construct being proved (e.g., `progress/myDef_plan.md` for a definition named `myDef`).
- Keep each `_plan.md` and `_progress.md` pair focused on a single named goal to avoid confusion across related proofs.
- For abandoned goals, leave a short rationale in both plan/progress files so future sessions do not retry the same invalid path.