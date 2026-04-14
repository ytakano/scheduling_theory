# STDPP_AGENT.md

Guidelines for AI coding agents working with the `stdpp` library in this
repository.

This document is specific to stdpp usage.
It covers:
- how to recognize stdpp-shaped goals,
- which stdpp modules to consult,
- which tactics to try first,
- which canonical lemmas to prefer,
- and which proof patterns are standard.

For general Rocq proof engineering, consult `ROCQ_AGENT.md`.

---

## Purpose

The goal of this document is not to reproduce all stdpp documentation.

Its purpose is to help an agent use stdpp effectively and predictably:
- choose the right module,
- recognize common proof shapes,
- avoid inventing lemma names,
- and reduce proof-search noise.

The key rule is:
do not treat stdpp as a flat bag of lemmas.

Instead:
1. identify the goal shape,
2. identify the corresponding stdpp layer,
3. apply the standard tactic or canonical rewriting pattern,
4. search only after that.

---

## When to consult this file

Consult this file before editing if a target file:
- imports `stdpp`,
- uses `gmap`, `gset`, `mapset`, or `dom`,
- uses lookup notation such as `!!`,
- uses set notation such as `∈`, `∉`, `⊆`, `∪`, `∩`, `∖`,
- or uses stdpp tactics such as:
  - `set_solver`
  - `simplify_map_eq`
  - `simplify_eq`
  - `done`
  - `naive_solver`
  - `tc_solve`

---

## Main principle

Do not start with blind global search.

First classify the goal.

Typical stdpp layers are:
- `base`
- `tactics`
- `list`
- `sets`
- `fin_maps`
- `fin_map_dom`
- `gmap`
- `countable`
- `relations`

The most important workflow is:
1. classify the goal,
2. use the corresponding standard tactic or lemma family,
3. only then do local proof search.

---

## Preferred imports

Prefer stable, high-level imports.

```coq
From stdpp Require Import base tactics.
From stdpp Require Import list.
From stdpp Require Import sets.
From stdpp Require Import fin_maps fin_map_dom.
From stdpp Require Import gmap.
From stdpp Require Import countable.
From stdpp Require Import relations.
````

### Import rules

Prefer `stdpp.list` over importing individual `list_*` files directly.

Import only what the file needs, but keep the dependency visible.

If a file uses `gmap`, it will often also need:

* `countable`
* `fin_maps`
* `fin_map_dom`

If a file uses set-like notation, import `sets`.

---

## Tactics to try first

### General stdpp-friendly tactics

* `done`
* `naive_solver`
* `simplify_eq`

### Typeclass goals

* `tc_solve`

### Set goals

* `set_solver`

### Finite-map cleanup

* `simplify_map_eq`

### Arithmetic side conditions

* `lia`

Prefer targeted rewriting over broad simplification.

Do not repeatedly call `simpl` or `cbn` blindly on stdpp-heavy goals.

---

## Module map

### `stdpp.base`

Use for:

* foundational typeclasses,
* overloaded notation infrastructure,
* generic stdpp support,
* typeclass-solving support.

Typical symptom:

* notations are unresolved,
* instances are missing,
* or typeclass obligations are blocking progress.

First tactic to try:

```coq
tc_solve.
```

---

### `stdpp.tactics`

Use for:

* stdpp-oriented proof cleanup,
* small automation,
* constructor-equality simplification.

Typical tactics:

```coq
done.
naive_solver.
simplify_eq.
```

Use `simplify_eq` when constructor equalities are blocking progress.

---

### `stdpp.sets`

Use for goals involving:

* `x ∈ X`
* `x ∉ X`
* `X ⊆ Y`
* `X ≡ Y`
* `X ∪ Y`
* `X ∩ Y`
* `X ∖ Y`

Default tactic:

```coq
set_solver.
```

When the goal is about routine set algebra, try `set_solver` first.

Do not manually prove routine set identities unless automation fails.

---

### `stdpp.fin_maps`

Use for:

* abstract finite-map reasoning,
* lookup-based proofs,
* insert/delete reasoning,
* proving map equality extensionally.

Typical goal shapes:

* `m !! i = ...`
* `(<[i:=x]> m) !! j = ...`
* `delete i m !! j = ...`
* `m1 = m2`

Main workflow:

1. rewrite lookups through map operations,
2. discharge equality side conditions on keys,
3. if proving map equality, use extensionality.

Preferred extensional proof pattern:

```coq
apply map_eq; intro i.
```

---

### `stdpp.fin_map_dom`

Use for:

* reasoning about `dom`,
* converting between domain membership and lookup existence,
* normalizing domain expressions after insert/delete.

Typical goal shapes:

* `i ∈ dom _ m`
* `i ∉ dom _ m`
* `dom _ (<[i:=x]> m)`
* subset relations over domains

Main bridge:

* domain membership `<->` lookup existence

When `dom` appears, move quickly to lookup facts.

---

### `stdpp.gmap`

Use for:

* concrete finite maps with countable keys.

Important fact:

* `gmap K A` generally requires `Countable K`

If a `gmap` definition or proof fails unexpectedly, check whether the key type
has:

* `EqDecision K`
* `Countable K`

Do not work around missing instances with ad-hoc encodings unless truly needed.

---

### `stdpp.countable`

Use for:

* proving a type is usable as a key,
* supplying `Countable`,
* and reasoning about custom identifier-like types.

This frequently matters for:

* wrapper record types,
* finite enums,
* custom syntax nodes used as keys,
* and project-specific IDs.

---

### `stdpp.relations`

Use for:

* relation closure reasoning,
* order-like arguments,
* and relation-level abstractions.

If the goal is clearly relational, start with the relation layer rather than
blind global search.

---

## Standard proof recipes

### Set goals

If the goal is about:

* membership,
* subset,
* union,
* intersection,
* or difference,

try:

```coq
set_solver.
```

If automation fails, reduce the problem to membership reasoning rather than
expanding definitions blindly.

---

### Map lookup goals

For goals about `!!`, start by rewriting with canonical lookup lemmas.

Typical first choices:

* `lookup_empty`
* `lookup_insert`
* `lookup_insert_eq`
* `lookup_insert_ne`
* `lookup_delete`
* `lookup_delete_eq`
* `lookup_delete_ne`
* `lookup_union`

If a key equality side condition appears, solve it locally and keep the proof
shape small.

---

### Equality of maps

For map equality, prefer extensional equality:

```coq
apply map_eq; intro i.
```

Then solve the resulting lookup equality by rewriting through the map
operations.

Do not destruct full maps structurally unless there is a strong reason.

---

### Domain goals

If the goal mentions `dom`, convert it early.

Typical lemmas:

* `elem_of_dom`
* `elem_of_dom_2`
* `not_elem_of_dom`
* `dom_empty`
* `dom_insert`
* `dom_insert_lookup`
* `dom_delete`
* `subseteq_dom`

Recommended workflow:

1. rewrite domain membership into lookup existence,
2. solve the lookup fact with map lemmas,
3. rebuild the domain-level statement only if needed.

---

### Constructor equalities

If hypotheses include equalities such as:

* `Some x = Some y`
* `inl x = inl y`
* `S n = S m`

try:

```coq
simplify_eq.
```

This is usually better than manual inversion chains.

---

### Messy map equalities in context

If the context contains complicated map equalities or map-shaped contradictions,
try:

```coq
simplify_map_eq.
```

Use this before writing long manual inversion scripts.

---

## Minimal lemma shortlist

This is the first shortlist an agent should remember.

### Maps

* `map_eq`
* `lookup_empty`
* `lookup_insert`
* `lookup_insert_eq`
* `lookup_insert_ne`
* `lookup_insert_Some`
* `lookup_delete`
* `lookup_delete_eq`
* `lookup_delete_ne`
* `lookup_delete_Some`
* `lookup_union`
* `lookup_union_l`
* `lookup_union_r`

### Domains

* `elem_of_dom`
* `elem_of_dom_2`
* `not_elem_of_dom`
* `dom_empty`
* `dom_insert`
* `dom_insert_lookup`
* `dom_delete`
* `subseteq_dom`

### Sets

* `set_solver`

### General support

* `done`
* `naive_solver`
* `simplify_eq`
* `simplify_map_eq`
* `tc_solve`

### Key-type support

* `EqDecision`
* `Countable`

---

## Search discipline

Do not invent lemma names.

Before writing a complicated proof step, use search-by-shape.

Preferred commands:

```coq
Check lookup_insert.
Check elem_of_dom.
Search (_ !! _).
Search (delete _ _ !! _).
Search (dom _ _).
Search (_ ∈ dom _ _).
Search (_ ⊆ _).
```

Search policy:

* search by notation or shape first,
* prefer local module knowledge over blind global search,
* do not guess a lemma name in committed code.

---

## Anti-patterns

### Blind global simplification

Bad:

```coq
repeat simpl in *.
```

Reason:

* it may destroy useful structure,
* it often does not normalize the right stdpp terms,
* and it makes proofs brittle.

Prefer targeted rewriting.

### Manual set proofs for routine identities

Bad:

* long element-chasing proofs for ordinary set algebra.

Prefer:

```coq
set_solver.
```

### Structural destruction of maps

Bad:

* destructing full maps directly when extensional equality suffices.

Prefer:

```coq
apply map_eq; intro i.
```

### Staying at the `dom` level too long

Bad:

* manipulating `dom` syntax only.

Prefer converting `dom` facts into lookup-existence facts early.

### Forgetting key-type obligations

If `gmap K A` behaves unexpectedly, check:

* `EqDecision K`
* `Countable K`

before deeper debugging.

---

## Preferred local proof style

Prefer short, shape-driven proofs.

Good style:

```coq
Proof.
  intros.
  apply map_eq; intro i.
  destruct (decide (i = k)) as [->|Hneq].
  - rewrite lookup_insert.
    ...
  - rewrite lookup_insert_ne by done.
    ...
Qed.
```

Also good:

```coq
Proof.
  intros.
  set_solver.
Qed.
```

Avoid:

* unnecessary unfolding of stdpp internals,
* long brittle rewrite chains,
* and proof search without a recognized goal shape.

---

## Project-specific recommendations

For this project, the following style is preferred.

For finite environments, states, and tables:

* prefer `gmap` if keys are countable.

For side conditions about domains:

* move quickly from `dom` facts to lookup existence.

For map equalities:

* prefer `map_eq`.

For routine set obligations:

* prefer `set_solver`.

For custom key types:

* define `EqDecision` and `Countable` instances early.

For repetitive map or set obligations:

* use stdpp automation first before creating custom tactics.

---

## Decision procedure for the agent

When facing a stdpp-related goal, follow this order:

1. recognize the structure

   * set?
   * map lookup?
   * domain?
   * map equality?
   * typeclass?

2. try the standard tactic

   * sets -> `set_solver`
   * constructor equalities -> `simplify_eq`
   * messy map equalities -> `simplify_map_eq`
   * typeclasses -> `tc_solve`

3. normalize with core lemmas

   * lookup lemmas for maps
   * `elem_of_dom` or `not_elem_of_dom` for domains

4. only then search for specialized lemmas

5. do not invent lemma names

---

## Final rule

For stdpp, success usually comes from:

* choosing the right abstraction layer,
* rewriting into the canonical goal shape,
* and then applying the standard automation.

Do not start with brute-force proof search.
Start with the structure.