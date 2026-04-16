# ROCQ_AGENT.md

Guidelines for AI coding agents working on Rocq developments in this repository.

This document covers general Rocq proof engineering:
- definitions,
- theorem statements,
- proof scripts,
- induction structure,
- imports,
- naming,
- and constructive-vs-classical policy.

This is not the place for library-specific detail.
For stdpp, consult `STDPP_AGENT.md`.

There is no `coqc`, but there is `rocq`. Use `rocq` or `make <file>.vo` for compiliation.

---

## Purpose

The goal of this repository is not merely to make individual proofs pass.

The goal is to build a Rocq development that is:
- semantically clear,
- structurally layered,
- reusable,
- maintainable,
- and aligned with the roadmap and design documents.

Agents should therefore optimize for long-term proof architecture,
not only short-term theorem completion.

---

## Core principles

### Prefer structure over local proof success

Do not optimize only for “the current theorem compiles”.

Prefer changes that make later theorems easier to:
- state,
- reuse,
- strengthen,
- refactor,
- and maintain.

A short brute-force proof is not automatically better than a slightly longer
proof organized around the right interface lemma.

### Preserve abstraction boundaries

Always identify which layer a file or theorem belongs to.

Typical layers include:
- semantic definitions,
- executable or algorithmic interfaces,
- invariants,
- refinement statements,
- task-model-specific assumptions,
- analysis-specific properties.

Do not mix these layers without a clear reason.

In particular:
- do not bake proof artifacts into core semantics,
- do not encode implementation choices into abstract definitions,
- do not move assumptions across layers casually.

### Prefer reusable statements

When proving something nontrivial, first ask:
- Is this really a one-off fact?
- Should this be a reusable helper lemma?
- Should this be an interface lemma?
- Should this be stated in a more general form?

Prefer reusable lemmas, but only at the correct abstraction level.

Do not over-generalize prematurely.

### Keep proofs readable

Proof scripts should be understandable by a future maintainer.

Prefer:
- short blocks,
- explicit proof structure,
- stable proof patterns,
- small helper lemmas,
- and local comments only when they clarify semantic intent.

Avoid:
- giant monolithic scripts,
- fragile repetition,
- unnecessary proof search,
- and opaque tactical noise.

---

## Constructive-first policy

### Default to constructive development

This repository should be developed in a constructive-first style.

Agents must:
- avoid `Classical` whenever possible,
- avoid importing classical axioms by default,
- avoid proof patterns that require excluded middle unless genuinely necessary,
- prefer computationally meaningful witnesses and evidence,
- and preserve constructive content in interfaces and definitions.

Constructive proofs are preferred because they tend to:
- preserve computational meaning,
- expose actual dependencies,
- support executable interpretations,
- and fit refinement-oriented developments better.

### Do not import classical libraries casually

Do not add imports such as:
- `Classical`
- `Classical_Prop`
- `ClassicalChoice`
- `FunctionalExtensionality`
- `ProofIrrelevance`

unless there is a clear and explicit need.

In particular, do not import classical libraries merely because:
- proof search got stuck,
- a constructive witness is inconvenient,
- a disjunction is hard to prove,
- or the current theorem would become shorter.

### Prefer decidability over excluded middle

When a proof needs case analysis on a proposition, prefer:
- a boolean test plus specification lemma,
- an explicit decision procedure,
- or a decidability hypothesis,

rather than unrestricted excluded middle.

Typical examples:
- equality decisions,
- finite-membership decisions,
- order decisions,
- bounded search procedures,
- and constructive existence arguments.

### Preserve witness content

When proving existential statements, prefer direct witness construction.

Avoid existence proofs that rely on classical contradiction if a direct witness
can be built.

A constructive witness is usually better for:
- later refinement lemmas,
- executable interpretations,
- and proof reuse.

### Reconsider before using classical reasoning

Before introducing classical reasoning, first try:
1. restating the theorem constructively,
2. strengthening the inductive invariant,
3. introducing an explicit decision procedure,
4. requiring a decidability hypothesis,
5. proving a computational version of the needed fact,
6. splitting the theorem into constructive and non-constructive parts.

Often, apparent need for classical logic is actually a sign that:
- the theorem is stated at the wrong layer,
- a decidability hypothesis is missing,
- or the intended witness has not been exposed.

---

## Classical isolation policy

### If classical reasoning is truly necessary, isolate it

If classical reasoning is genuinely unavoidable for a theorem, isolate it so that
it does not pollute the rest of the project.

Prefer the following strategy:
- place classical results in a separate module or file,
- give the module or file an explicit classical name,
- import classical libraries only there,
- keep classical theorems out of core semantic layers when possible,
- and expose the narrowest possible interface back to the rest of the project.

Good examples of naming:
- `FooClassical.v`
- `ClassicalFacts/Foo.v`
- `Foo/ClassicalBridge.v`

Avoid silent classical imports in general-purpose files.

### Do not let classical assumptions leak outward

When a classical module is unavoidable:
- isolate the import locally,
- document why it is needed,
- and avoid forcing unrelated files to depend on it.

A constructive core with a small isolated classical boundary is preferable to a
project-wide classical default.

### Keep core semantics constructive

Core semantic files, interface files, and reusable invariants should remain
constructive unless there is a compelling reason otherwise.

Do not move classical assumptions into foundational layers merely to simplify
downstream proofs.

---

## Expected workflow before editing

Before changing a definition or proof, the agent should:
1. identify the target abstraction layer,
2. read nearby definitions and theorem statements,
3. check relevant design documents and roadmap files,
4. inspect existing local proof patterns,
5. determine whether the development can remain constructive,
6. only then implement changes.

For nontrivial edits, also determine:
- which invariants already exist,
- which lemmas are reused in the file,
- whether the change affects architecture or documentation,
- and whether any classical dependency would leak too far.

---

## Rules for definitions

### Definitions should reflect semantics

Definitions should express intended meaning as directly as possible.

Prefer:
- simple definitions,
- explicit parameters,
- stable interfaces,
- semantically meaningful names.

Avoid:
- definitions shaped only to satisfy one proof,
- hidden proof-specific encodings,
- unnecessary wrappers,
- and duplicated concepts with slightly different names.

### Do not strengthen assumptions without reason

When changing a definition or theorem:
- use only the assumptions actually needed,
- avoid stronger hypotheses for convenience,
- avoid committing a core interface to a special case unless the layer is
  explicitly specialized.

A weaker and more reusable interface is usually better.

### Separate semantics from computation

If a concept has both:
- a semantic meaning, and
- an executable form,

keep them conceptually distinct unless the file is explicitly about their
connection.

Typical pattern:
- semantic object,
- executable interface,
- correctness or refinement theorem between them.

Do not collapse these into one definition just to simplify a proof.

---

## Rules for theorem statements

### State the right theorem first

Before proving something difficult, ask whether the theorem statement is
well-shaped.

A difficult proof often means:
- the theorem is stated at the wrong layer,
- the theorem bundles too many ideas,
- an intermediate lemma is missing,
- or the invariant is not explicit enough.

Do not respond to proof difficulty only with more tactics.

### Prefer interface lemmas

A theorem is often easier to maintain when split into:
- a reusable interface lemma,
- then a final theorem built from it.

This is especially valuable when a theorem:
- crosses abstraction layers,
- uses a nontrivial invariant,
- or is likely to be reused later.

### Keep theorem statements stable under proof refactoring

Names and statements should describe semantic content,
not the current proof method.

Avoid names that refer to:
- a temporary proof trick,
- a local decomposition choice,
- or an accidental intermediate form.

---

## Preferred proof style

### Use shape-driven proofs

Choose proof steps based on the structure of the goal.

Typical questions:
- Is the goal an implication, conjunction, disjunction, equality, existential,
  or universal statement?
- Is induction the right first step?
- Is inversion appropriate?
- Is a helper lemma missing?
- Is the goal blocked by simplification, rewriting, or an unstated invariant?

Do not begin with heavy automation before understanding the goal shape.

### Prefer small proof blocks

Prefer scripts like:

```coq
Proof.
  intros.
  split.
  - ...
  - ...
Qed.
````

or

```coq
Proof.
  intros x Hx.
  induction Hx.
  - ...
  - ...
Qed.
```

over long tactic chains with many semicolons.

### Prefer explicit control over brute-force automation

Use automation to remove routine work, not to hide proof structure.

Good uses of automation:

* trivial propositional cleanup,
* routine constructor equalities,
* standard arithmetic,
* standard local normalization.

Bad uses:

* repeated blind `auto`, `eauto`, or global proof search,
* solving important structural proof steps opaquely,
* leaving maintainers unable to see why the theorem is true.

### Prefer canonical tactics for common situations

Use standard, predictable tactics for standard proof obligations.

Typical examples:

* `intros`
* `split`
* `destruct`
* `inversion`
* `subst`
* `specialize`
* `rewrite`
* `apply`
* `eapply`
* `constructor`
* `exists`
* `induction`
* `lia`

Use these in a structured way before escalating.

---

## Induction policy

### Use induction on the right object

Before inducting, identify the real source of recursion or semantic progression.

Possible induction targets:

* syntax,
* derivations,
* traces,
* step relations,
* lists,
* time,
* task structure,
* well-founded measures.

Do not default to induction on the most visible variable.

### Generalize before induction when needed

If induction becomes too weak, generalize the right variables first.

Typical signs:

* the induction hypothesis is too specific,
* rewriting destroys useful generality,
* a variable should have remained arbitrary.

### Keep induction hypotheses usable

When possible:

* preserve hypotheses that should remain general,
* avoid introducing too much structure too early,
* maintain a proof state where the induction hypothesis is easy to apply.

---

## Rewriting and simplification policy

### Rewrite intentionally

Every rewrite should make the goal more canonical.

Prefer rewrites that:

* eliminate syntactic noise,
* expose the next proof step,
* normalize a term toward a standard form.

Avoid rewriting back and forth without a clear direction.

### Prefer canonical normal forms

When several equivalent forms are possible, consistently choose the one that
aligns with:

* existing local lemmas,
* standard proof patterns in the file,
* and the abstraction layer of the theorem.

### Avoid uncontrolled simplification

Do not use broad simplification blindly across the whole context.

Avoid patterns like:

```coq
repeat simpl in *.
```

Prefer:

* local `cbn`,
* targeted `simpl`,
* explicit rewriting,
* and normalization through known lemmas.

---

## Case analysis policy

### Split cases only when semantically meaningful

Case analysis should reflect a real branch in the reasoning.

Good reasons:

* a boolean or decision procedure determines behavior,
* a constructor split is essential,
* a semantic transition branches,
* a key equality determines behavior.

Bad reasons:

* proof search got stuck,
* the context became messy,
* no plan exists.

### Keep case splits local

When possible:

* split close to where the distinction matters,
* solve the easy case immediately,
* avoid carrying unnecessary branch assumptions too far.

---

## Helper lemmas

### Add helper lemmas when they clarify structure

A helper lemma is justified when it:

* captures a recurring argument,
* isolates a layer-specific normalization fact,
* exposes the right interface for reuse,
* or makes the main theorem significantly cleaner.

Do not add helper lemmas that merely rename a trivial local step.

### Place helper lemmas at the correct level

A helper lemma should live near the abstraction layer it belongs to.

Do not place:

* semantic lemmas in analysis-specific files,
* implementation-specific lemmas in abstract interface files,
* or highly local proof facts in globally shared modules unless actually
  reusable.

---

## Arithmetic, logic, and existentials

### Prefer standard arithmetic automation for routine goals

For linear arithmetic goals, prefer:

```coq
lia.
```

Do not manually prove routine arithmetic side conditions unless they encode
important semantic structure.

### Keep propositional reasoning simple

For routine propositional goals:

* destruct conjunctions and disjunctions cleanly,
* use `split`,
* use `exfalso` when appropriate,
* and use small local automation only when it keeps the proof readable.

### Prefer constructive logical structure

When handling logical goals:

* prefer direct introduction and elimination rules,
* prefer constructive disjunctions and existentials,
* avoid contradiction-based proofs when direct evidence is available,
* and avoid classical double-negation tricks unless absolutely necessary.

### Construct meaningful witnesses

When proving an existential, choose a witness that reflects the semantics of the
situation.

Avoid obscure witnesses chosen only to satisfy the current proof.

---

## Imports, naming, and comments

### Keep imports minimal

Only import what the file needs.

Avoid:

* wide imports “just in case,”
* duplicating nearby imports unnecessarily,
* relying on accidental transitive imports when clarity matters,
* and adding classical imports by default.

### Make dependencies visible

A reader should be able to see from the imports which main libraries and
abstractions the file depends on.

### Choose stable names

Choose names that are:

* semantically meaningful,
* stable,
* consistent with neighboring files,
* and explicit enough about abstraction level when needed.

### Comment semantic intent, not obvious syntax

Add comments when they explain:

* why a lemma exists,
* which abstraction boundary it serves,
* what invariant it captures,
* or why a decomposition is architecturally important.

Do not add comments that merely restate the next tactic.

---

## When a proof gets stuck

When blocked, do not immediately escalate proof search.

Try the following, in order:

1. restate the goal in plain semantic terms,
2. identify the abstraction layer,
3. check whether the theorem statement is well-shaped,
4. search for an existing canonical lemma,
5. introduce a missing helper lemma,
6. strengthen or clarify the invariant,
7. generalize before induction,
8. reconsider whether a constructive formulation is available,
9. isolate any unavoidable classical reasoning,
10. only then consider stronger automation or deeper refactoring.

Prefer a clean structural fix over a tactical patch.

---

## Final rule

A good Rocq change in this repository should do more than close one proof.

It should make the surrounding development:

* clearer,
* more reusable,
* better layered,
* more constructive when possible,
* and easier to extend,

while keeping any unavoidable classical reasoning isolated from the constructive
core.
