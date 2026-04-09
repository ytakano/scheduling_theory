# Proof Progress: Partitioned Bridge Refactoring

## Status Overview
- Overall: Complete
- Complete Items: 5/5
- Unproven (`Admitted`): none
- Failed/Abandoned Items: none

## Completed Items

### Step 1: `DispatchInterface.v` comments

Clarified that `candidates` need not all be eligible; subset/finite-set
reasoning belongs in the bridge layer. No signature changes.

### Step 2: `DispatchSchedulerBridge.v` restructure

New reading order: `CandidateSource` → `CandidateSourceSpec` →
`single_cpu_dispatch_schedule` → `single_cpu_dispatch_valid` →
`single_cpu_dispatch_scheduler_on` → inspection lemmas → intro lemma.

New lemmas added:

```coq
Lemma single_cpu_dispatch_eq_cpu0 :
    forall spec candidates_of jobs sched t,
      scheduler_rel (single_cpu_dispatch_schedule spec candidates_of) jobs 1 sched ->
      sched t 0 = spec.(dispatch) jobs 1 sched t (candidates_of jobs 1 sched t).

Lemma single_cpu_dispatch_idle_on_other_cpus :
    forall spec candidates_of jobs sched t c,
      scheduler_rel (single_cpu_dispatch_schedule spec candidates_of) jobs 1 sched ->
      0 < c -> sched t c = None.
```

Renamed `single_cpu_dispatch_schedulable_by_on` →
`single_cpu_dispatch_schedulable_by_on_intro` (old name kept as `Abbreviation`).

### Step 3: `Partitioned.v` bridge integration

Added `Require Import DispatchSchedulerBridge`.
Added `Hypothesis enumJ_sound : forall j, In j enumJ -> J j` to Section
(only affects lemmas that use it; pre-existing theorems unchanged).

New definitions/lemmas:

```coq
Definition local_jobset (c : CPU) : JobId -> Prop :=
  fun j => J j /\ assign j = c.

Definition local_candidates_of (c : CPU) : CandidateSource :=
  fun _ _ _ _ => local_candidates c.

Lemma local_candidates_spec :
  forall c, c < m ->
    CandidateSourceSpec (local_jobset c) (local_candidates_of c).

Lemma partitioned_schedule_on_iff_local_rel :
  forall jobs sched,
    partitioned_schedule_on jobs sched <->
    (forall c, c < m ->
      scheduler_rel
        (single_cpu_dispatch_schedule spec (local_candidates_of c))
        jobs 1 (cpu_schedule sched c)).
```

Key proof note for `partitioned_schedule_on_iff_local_rel`: after unfolding
`cpu_schedule`, the virtual-CPU-0 equality simplifies by `simpl` directly;
`Nat.eqb_refl` is not needed.

### Step 4: `Partitioned.v` feasibility theorems

Kept old `local_feasible_implies_global_feasible_schedule` (marked deprecated).
Added preferred `local_feasible_on_implies_global_feasible_on`:

```coq
Theorem local_feasible_on_implies_global_feasible_on :
  forall jobs sched,
    respects_assignment sched ->
    (forall c, c < m ->
      feasible_schedule_on (local_jobset c) jobs 1 (cpu_schedule sched c)) ->
    feasible_schedule_on J jobs m sched.
```

Proof: take `j` and `J j`; derive `assign j < m`; apply local feasibility at
`assign j`; use `missed_deadline_iff_on_assigned_cpu` to lift to global.

Also added `local_valid_feasible_on_implies_global` corollary.

### Step 5: `Partitioned.v` schedulable_by_on intro

```coq
Corollary partitioned_schedulable_by_on_intro :
  forall assign m spec J enumJ jobs sched,
    scheduler_rel (partitioned_scheduler assign m spec enumJ) jobs m sched ->
    valid_schedule jobs m sched ->
    feasible_schedule_on J jobs m sched ->
    schedulable_by_on J (partitioned_scheduler assign m spec enumJ) jobs m.
```

Thin wrapper around `schedulable_by_on_intro`.

## TODO

(none — all complete)
