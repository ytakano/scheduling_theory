> Obsolete note
>
> This is a historical improvement plan. The current source of truth is
> `Partitioned.v`.

# Proof Plan: Partitioned Scheduling — Local/Global Lifting

## Goal

Lift `missed_deadline` and `feasible_schedule` from per-CPU (local) to global in `Partitioned.v`,
completing Milestones M1 and M2 from `partitioned_improve.md`.

## Proof Strategy

Build on the already-proven `completed_iff_on_assigned_cpu` and `local_to_global_validity`:
1. `missed_deadline` equivalence follows immediately from `completed_iff_on_assigned_cpu` + `tauto`.
2. `feasible_schedule` lifting follows from `missed_deadline` equivalence + per-CPU feasibility.
3. Combined validity + feasibility corollary combines the above with `local_to_global_validity`.

## Proposed Lemmas

- [x] `missed_deadline_iff_on_assigned_cpu`: deadline miss on global m-CPU sched ↔ on 1-CPU view of assigned CPU
- [x] `local_feasible_implies_global_feasible_schedule`: per-CPU feasibility → global feasibility
- [x] `local_valid_feasible_implies_global`: combined validity + feasibility lifting corollary

## Proof Order

1. `missed_deadline_iff_on_assigned_cpu`
2. `local_feasible_implies_global_feasible_schedule`
3. `local_valid_feasible_implies_global`
