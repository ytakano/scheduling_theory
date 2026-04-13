# Generic Uniprocessor Normalization Design

## Summary

This repository factors finite-job optimality proofs for uniprocessor
scheduling policies into a generic pipeline plus small policy-specific proof
obligations. The goal is to let a new policy reuse the normalization and
optimality skeletons without re-proving the same inductive argument structure.

The core idea is to express "canonical" schedules generically as schedules that
match the policy scheduling algorithm on a finite prefix. Policy files are then
responsible only for exposing their own canonical predicates, proving that they
coincide with the generic scheduling algorithm-based predicates, and providing a local
repair step for non-canonical time points.

## Architecture

The normalization design is split across four layers.

1. `SchedulingAlgorithmCanonicalBridge.v`
   Defines the generic scheduling algorithm-matching predicates used as the canonical
   notion in the shared infrastructure. This layer also contains the bridge
   from a finite canonical schedule with an idle tail to `scheduler_rel`.

2. `SchedulingAlgorithmNormalization.v`
   Provides the reusable finite-horizon normalization proof. Its interface is
   the record `CanonicalRepairSpec` together with the hypothesis
   `ChooseAgreesBefore`.

3. `SchedulingAlgorithmOptimalitySkeleton.v`
   Packages the end-to-end finite optimality pipeline: restrict a feasible
   witness, normalize it on the relevant horizon, truncate the tail, and
   convert the result into a scheduler witness.

4. Policy files such as `Uniprocessor/Policies/EDF*.v` and `Uniprocessor/Policies/LLF*.v`
   Supply the policy-specific canonical predicates, local repair proof, and the
   prefix-agreement fact needed by the normalization core.

This split keeps the induction and horizon-management machinery generic while
leaving only the real scheduling-policy content in policy modules.

## Canonicality Interface

`CanonicalRepairSpec` is the contract a uniprocessor policy must implement to
participate in generic normalization.

- `canonical_at` is the policy-facing notion that the schedule already makes
  the correct decision at one time instant.
- `canonical_before` is the policy-facing notion that the whole prefix before a
  horizon is canonical.
- `canonical_at_def` and `canonical_before_def` are bridge lemmas: they connect
  the policy's preferred presentation to the generic predicates
  `matches_choose_at_with` and `matches_choose_before`.
- `canonical_at_dec` keeps normalization constructive by allowing the proof to
  inspect whether repair is needed at each step.
- `repair_non_canonical` is a local repair lemma. Given a schedule that is
  valid, feasible on the target job set, runs only jobs from that set, and is
  single-CPU shaped, it repairs one non-canonical time point while preserving
  those global invariants and agreement before the repaired time.

The key design choice is locality: the generic normalization proof never needs
to know how a policy repairs an entire suffix. It only needs a way to fix the
current step without disturbing the past.

## Prefix Agreement Requirement

Normalization rewrites schedules from left to right. Because of this, the
generic proof also needs `ChooseAgreesBefore`.

This hypothesis says that if two schedules agree strictly before time `t`, then
the scheduling algorithm makes the same decision at `t` when run on those schedules with
their corresponding candidate lists. In practice this combines two facts:

- the candidate source depends only on the prefix before `t`
- the policy chooser itself is prefix-extensional once given those candidates

Without this hypothesis, repairing a later part of the schedule could change
what the policy is supposed to have done earlier, which would break the
inductive normalization argument.

## Finite Optimality Pipeline

`SchedulingAlgorithmOptimalitySkeleton.v` packages finite optimality into three
stages.

1. Restriction
   Start from an arbitrary feasible witness for the designated job set `J`.
   Restrict it to the single-CPU view and to jobs from `J`.

2. Normalization
   Apply the generic normalization result on the finite horizon of interest so
   that the restricted witness becomes scheduling algorithm-matching on that prefix.

3. Truncation and Bridge
   Truncate the normalized schedule at the deadline horizon. Since all jobs in
   `J` have deadlines within that finite horizon, feasibility is preserved.
   Then use the canonical bridge to turn the finite canonical schedule with an
   idle tail into a witness for `scheduler_rel`.

This decomposition isolates policy-specific reasoning in Stage 2 and reuses the
same Stage 1 and Stage 3 argument for every uniprocessor policy that fits the
interface.

## Guidance for Adding a New Policy

To add a new uniprocessor policy without duplicating the generic skeleton:

1. Define the policy's scheduling algorithm and candidate source in the usual policy
   files.
2. Introduce policy-facing predicates for one-step and finite-prefix
   canonicality.
3. Prove equivalence between those predicates and the generic
   scheduling algorithm-matching predicates.
4. Prove decidability of the one-step canonical predicate.
5. Prove a local repair lemma that fixes one non-canonical time point while
   preserving validity, feasibility, J-only execution, single-CPU shape, and
   prefix agreement.
6. Prove `ChooseAgreesBefore` for the policy.
7. Instantiate `normalize_to_canonical_generic` and then
   `finite_optimality_via_normalization` instead of rebuilding the induction
   manually.

The expected outcome is that policy files contribute only local semantic facts
about the policy's chooser and repair operation, while all finite-horizon
normalization structure remains shared infrastructure.
