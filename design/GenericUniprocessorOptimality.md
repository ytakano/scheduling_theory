# Generic Uniprocessor Canonicalization and Finite-Horizon Optimality

This is a supplemental design note for the generic uniprocessor
canonicalization and finite-optimality pipeline.

The primary layer document is:

- `design/Uniprocessor.md`

This note exists to explain the detailed mechanics of horizon,
canonicalization, repair, and normalization without pushing that level of
detail into the main layer overview.

## Summary

This design factors finite-job optimality proofs for uniprocessor scheduling
policies into a shared canonicalization pipeline plus small policy-specific
proof obligations.

The key idea is to define, for any scheduling policy, what it means for a
schedule to already follow that policy on a finite prefix. Once this notion is
fixed, the shared infrastructure proves that any feasible witness schedule can
be transformed into a canonical one on the relevant finite horizon, and then
converted into a scheduler witness for the policy.

As a result, a new policy does not need to re-prove the full finite-horizon
inductive argument. It only needs to provide its own one-step canonicality
view, a local repair lemma, and a prefix-stability fact for its chooser.

## Key Terms

This design uses four terms in a precise technical sense.

### Horizon

A **horizon** is a finite time bound up to which we require a schedule to match
the policy chooser.

For a finite enumerated job set `enumJ`, the most important horizon is the
**deadline horizon**:

```text
deadline_horizon(enumJ) = 1 + max { absolute deadline of j | j in enumJ }.
```

So the deadline horizon is literally **maximum deadline + 1**.

This `+1` matters because canonicality is stated on the strict prefix
`t < H`. By taking `H = max_deadline + 1`, every enumerated job deadline is
strictly before the horizon.

In other words:

- if `j` is in `enumJ`, then `job_abs_deadline(j) < deadline_horizon(enumJ)`;
- therefore all deadlines of interest lie inside the prefix `t < H`;
- therefore it is enough to canonicalize only that prefix.

After that point, the proof may safely truncate the tail, because all jobs in
the target finite set must already have completed by their deadlines if the
schedule is feasible.

#### Example

Suppose the enumerated jobs are:

- `j1` with deadline `3`
- `j2` with deadline `5`
- `j3` with deadline `4`

Then:

```text
max deadline = 5
deadline horizon = 6
```

Hence every listed job has deadline `< 6`.

This means the proof only needs the schedule to be canonical at times

```text
t = 0, 1, 2, 3, 4, 5
```

and does not need to care about times `t >= 6` for those jobs.

### Canonical

A schedule is **canonical at time `t`** if the actual job scheduled at time `t`
is exactly the job returned by the policy chooser at time `t`.

A schedule is **canonical before horizon `H`** if it is canonical at every time
`t < H`.

So canonicality is not an arbitrary normal form. It means:

> on the time interval we care about, the schedule already behaves exactly like
> the policy chooser.

This is why horizon and canonicality are directly connected: the horizon tells
us **how far** canonicality must hold.

#### Example

Assume the candidate jobs at time `2` are `A` and `B`, and the policy chooser
returns `A`.

- If the schedule runs `A` at time `2`, then it is canonical at time `2`.
- If the schedule runs `B` at time `2`, then it is not canonical at time `2`.

If the relevant horizon is `6`, then "canonical before `6`" means this matching
must hold at times `0, 1, 2, 3, 4, 5`.

### Repair

A **repair** is a local transformation that fixes one non-canonical time point.

More precisely, if a schedule is valid and feasible, and time `t` is
non-canonical, a repair step constructs a new schedule that:

- still remains valid,
- still remains feasible for the target job set,
- agrees with the old schedule before `t`, and
- becomes canonical at time `t`.

The important point is that repair is **local**: it fixes the current bad time
without rewriting the already-correct past.

#### Example

Suppose at time `2` the chooser says `A` should run, but the schedule runs `B`.

A repair step changes the schedule so that:

- times `0` and `1` stay unchanged,
- time `2` now runs `A`,
- the resulting schedule still preserves feasibility.

The repair may also modify some later time to compensate, but it does not alter
the prefix before `2`.

### Normalization

**Normalization** is the left-to-right process of repeatedly applying repair
until the schedule becomes canonical on the whole prefix of interest.

So normalization does not mean "compute a unique canonical schedule".
It means:

> starting from any feasible witness schedule, construct another feasible
> schedule that matches the policy chooser at every time before the chosen
> horizon.

#### Example

Suppose the relevant horizon is `6`.

- At time `0`, the schedule is already canonical.
- At time `1`, it is canonical.
- At time `2`, it is not canonical, so repair is applied.
- Then move to time `3`, check again, and repair if needed.
- Continue up to time `5`.

At the end, the resulting schedule is canonical before `6`.

### Relationship Between the Four Terms

These four notions fit together as follows:

- **Horizon** says how far we care.
- **Canonical** says the schedule matches the chooser at one time or on that prefix.
- **Repair** fixes one bad time while preserving the past.
- **Normalization** applies repair repeatedly until the whole prefix up to the
  horizon becomes canonical.

For finite-job optimality, the key horizon is the deadline horizon
`max_deadline + 1`, because every enumerated job deadline lies strictly before
it. This is exactly what makes finite-prefix canonicalization sufficient.

## Architecture

The design is split across four layers.

### 1. `SchedulingAlgorithmCanonicalBridge.v`

This layer defines the generic chooser-matching predicates used as the shared
notion of canonicality:

- one-step canonicality at time `t`,
- finite-prefix canonicality before `H`, and
- the bridge from a finite canonical prefix with an idle tail to
  `scheduler_rel`.

This file is where the generic notion of "the schedule follows the policy" is
made precise.

### 2. `SchedulingAlgorithmNormalization.v`

This layer provides the reusable finite-prefix canonicalization proof.

Its interface is the record `CanonicalRepairSpec` together with the hypothesis
`ChooseAgreesBefore`.

`CanonicalRepairSpec` says what a policy must provide in order to participate in
the generic canonicalization proof:

- a policy-facing one-step canonical predicate,
- a policy-facing finite-prefix canonical predicate,
- proof that both coincide with the generic chooser-matching predicates,
- decidability of one-step canonicality, and
- a local repair lemma for one non-canonical time point.

`ChooseAgreesBefore` states that if two schedules agree strictly before time
`t`, then the chooser makes the same decision at time `t`. This is what makes
left-to-right canonicalization possible.

### 3. `SchedulingAlgorithmOptimalitySkeleton.v`

This layer packages the full finite-job optimality pipeline.

The proof has three stages.

1. **Restriction**
   Start from an arbitrary feasible witness for the target job set `J`, and
   restrict it to the single-CPU view and to jobs from `J`.

2. **Canonicalization on the relevant horizon**
   Normalize the restricted schedule so that it becomes canonical before the
   finite horizon of interest.

3. **Truncation and scheduler bridge**
   Truncate the normalized schedule at the deadline horizon. Because all jobs in
   `J` have deadlines before that bound, feasibility for `J` is preserved. Then
   convert the canonical finite-prefix schedule with an idle tail into a
   `scheduler_rel` witness.

### 4. Policy modules

Policy files such as `Uniprocessor/Policies/EDF*.v` and
`Uniprocessor/Policies/LLF*.v` provide only the policy-specific ingredients:

- policy-facing canonical predicates,
- the proof that these match the generic chooser-based predicates,
- a local repair lemma, and
- the prefix-agreement fact required by `ChooseAgreesBefore`.

This keeps the induction, horizon handling, truncation, and scheduler-bridge
machinery out of policy files.

## Why the Design Is Structured This Way

The central design choice is **locality**.

The shared proof never asks a policy to construct a globally canonical suffix in
one step. Instead, it asks only for a repair of the current non-canonical time
point that does not disturb the already-normalized past.

This makes the generic proof reusable across policies whose semantic content is
different, while keeping the inductive structure identical.

## Canonicalization Interface

`CanonicalRepairSpec` is the contract for one policy.

Informally, its fields mean the following.

- `canonical_at`
  The policy-facing statement that the schedule already makes the correct
  decision at one time.

- `canonical_before`
  The policy-facing statement that the entire prefix before some horizon is
  canonical.

- `canonical_at_def` / `canonical_before_def`
  Bridge lemmas connecting the policy presentation to the generic predicates
  `matches_choose_at_with` and `matches_choose_before`.

- `canonical_at_dec`
  A decision procedure for one-step canonicality, used by the constructive
  left-to-right proof.

- `repair_non_canonical`
  A local repair lemma for a single non-canonical time point.

The interface is intentionally narrow: policies provide local semantic facts,
while the shared infrastructure provides the finite-prefix inductive argument.

## Prefix Agreement Requirement

Canonicalization proceeds from left to right, so the proof must know that
repairing the future does not change what the chooser should have done at the
current step.

This is the role of `ChooseAgreesBefore`.

Informally, it says that chooser decisions at time `t` depend only on the
schedule prefix before `t`, not on how the schedule is written later.

In practice, this usually comes from two facts:

- the candidate source depends only on the prefix before `t`, and
- the chooser is prefix-extensional once those candidates are fixed.

Without this property, local repair would not compose into a sound inductive
canonicalization proof.

## Finite-Horizon Optimality Pipeline

The end-to-end proof strategy is:

1. start from any feasible witness schedule for the target finite job set,
2. restrict it to the uniprocessor target view,
3. canonicalize it on the deadline-relevant finite prefix,
4. truncate the tail after the deadline horizon, and
5. turn the result into a witness for `scheduler_rel`.

This isolates policy-specific reasoning to the repair and chooser facts, while
reusing the same restriction, horizon, truncation, and bridge argument across
policies.

## Guidance for Adding a New Policy

To instantiate the shared framework for a new uniprocessor policy:

1. Define the policy chooser and candidate source.
2. Define policy-facing one-step and finite-prefix canonical predicates.
3. Prove that they coincide with the generic chooser-matching predicates.
4. Prove decidability of one-step canonicality.
5. Prove a local repair lemma for one non-canonical time point.
6. Prove `ChooseAgreesBefore`.
7. Instantiate the generic canonicalization theorem.
8. Instantiate the finite optimality skeleton.

The intended outcome is that policy modules contain only policy-local semantics,
while canonicalization and finite-horizon witness construction remain generic.
