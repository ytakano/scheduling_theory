# Proof Progress: Partitioned Scheduling (Lv.5)

## Status Overview
- Overall: **Complete**
- Complete Lemmas: 13/13
- Unproven (`Admitted`): none
- Failed/Abandoned Items: none

---

## Completed: Phase A — Interface Refactoring

### `UniSchedulerInterface.v`
Replaced `UniSchedulerSpec` (5 fields incl. `choose_min_deadline`) with `GenericSchedulerDecisionSpec`
(4 generic fields: `choose_g`, `choose_g_ready`, `choose_g_some_if_ready`,
`choose_g_none_if_no_ready`, `choose_g_in_candidates`).

### `UniSchedulerLemmas.v`
Updated Section variable to `GenericSchedulerDecisionSpec`.  Renamed all field accesses:
`spec.(choose)` → `spec.(choose_g)`, etc.  Removed EDF-specific lemmas A5/C1/C2
(moved to `EDF.v`).

### `EDF.v`
Added `edf_generic_spec : GenericSchedulerDecisionSpec` and `EDFSchedulerSpec` record
(coercion `:>` on `edf_generic` field so `EDFSchedulerSpec <: GenericSchedulerDecisionSpec`).
Updated `edf_scheduler_spec : EDFSchedulerSpec`.
Added `EDFSchedulerLemmasSection` with A5/C1/C2 lemmas.

---

## Completed: Phase B — `Partitioned.v` Helper Lemmas

### `candidates_for_assign_sound`
```coq
Lemma candidates_for_assign_sound :
  forall c jobs sched t xs j,
    In j (candidates_for c jobs sched t xs) -> assign j = c.
```
Proof: `filter_In` + `Nat.eqb_eq`.

### `non_assigned_cpu_zero`
```coq
Lemma non_assigned_cpu_zero :
  forall sched,
    respects_assignment sched ->
    forall j t c,
      c < m -> c <> assign j -> runs_on sched j t c = false.
```
Proof: `runs_on_false_iff`; contrapositive of `respects_assignment`.

### `partitioned_implies_sequential`
```coq
Lemma partitioned_implies_sequential :
  forall sched,
    respects_assignment sched ->
    sequential_jobs m sched.
```
Proof: two `pose proof` + `lia`.

### `cpu_count_assigned_only`
```coq
Lemma cpu_count_assigned_only :
  forall sched,
    respects_assignment sched ->
    forall j t,
      cpu_count sched j t m = if runs_on sched j t (assign j) then 1 else 0.
```
Proof: case split on `runs_on sched j t (assign j)`.
- `true`: lower bound via `cpu_count_pos_iff_executed`, upper bound via `cpu_count_le_1` + `partitioned_implies_sequential`. Then `lia`.
- `false`: `cpu_count_zero_iff_not_executed`; for any c < m with `sched t c = Some j`, derive `assign j = c` from `respects_assignment`, then contradiction with `runs_on_false_iff`.

Key: avoided induction on Section variable `m` by using existing lemmas.

### `runs_on_cpu_schedule`
```coq
Lemma runs_on_cpu_schedule :
  forall sched c j t,
    runs_on (cpu_schedule sched c) j t 0 = runs_on sched j t c.
```
Proof: `unfold runs_on, cpu_schedule; simpl; reflexivity`.

### `service_decomposition_step`
```coq
Lemma service_decomposition_step :
  forall sched,
    respects_assignment sched ->
    forall j t,
      cpu_count sched j t m =
        cpu_count (cpu_schedule sched (assign j)) j t 1.
```
Proof: `rewrite cpu_count_assigned_only`, then `simpl`, `rewrite runs_on_cpu_schedule`, `lia`.

---

## Completed: Phase C — Core Theorems

### Theorem 3: `service_decomposition`
```coq
Theorem service_decomposition :
  forall sched,
    respects_assignment sched ->
    forall j t,
      service_job m sched j t =
        service_job 1 (cpu_schedule sched (assign j)) j t.
```
Proof: induction on `t`; base trivial; step `f_equal` + `service_decomposition_step`.

### Corollary: `completed_iff_on_assigned_cpu`
```coq
Corollary completed_iff_on_assigned_cpu :
  forall jobs sched,
    respects_assignment sched ->
    forall j t,
      completed jobs m sched j t <->
        completed jobs 1 (cpu_schedule sched (assign j)) j t.
```
Proof: unfold `completed`; rewrite `service_decomposition`; `tauto`.

### Theorem 1: `assignment_respect`
```coq
Theorem assignment_respect :
  forall jobs sched xs,
    valid_partitioned_schedule jobs sched xs ->
    forall j t c,
      c < m -> sched t c = Some j -> assign j = c.
```
Proof: trivial from `respects_assignment` component of `valid_partitioned_schedule`.

### Theorem 2: `local_to_global_validity`
```coq
Theorem local_to_global_validity :
  forall jobs sched xs,
    valid_partitioned_schedule jobs sched xs ->
    (forall c, c < m -> valid_schedule jobs 1 (cpu_schedule sched c)) ->
    valid_schedule jobs m sched.
```
Proof: unfold `valid_schedule`; for `(j, t, c)` with `sched t c = Some j`:
1. `cpu_schedule sched c t 0 = Some j` (by `Nat.eqb_refl`).
2. Per-CPU validity gives `eligible jobs 1 (cpu_schedule sched c) j t`.
3. Release part: direct.
4. Non-completion: `completed_iff_on_assigned_cpu` + `respects_assignment` + `rewrite Hassign`.

Key pitfall: after `rewrite completed_iff_on_assigned_cpu`, goal contains `assign j` not `c`.
Use `rewrite Hassign` (not `rewrite <- Hassign`) to change `assign j` to `c`.

---

## TODO
(none — all goals complete)
