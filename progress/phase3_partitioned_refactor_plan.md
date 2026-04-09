# Proof Plan: Phase 3 Partitioned.v Refactor

## Goal

Refactor `Partitioned.v` so that `partitioned_schedule` dispatches via the
**1-CPU local view** (`cpu_schedule sched c`, CPU count 1) instead of the
global schedule.  Side-effect: `respects_assignment` becomes derivable from
`partitioned_schedule` via `dispatch_in_candidates`.

## Proof Strategy

1. Simplify `candidates_for` (remove unused args).
2. Rewrite `partitioned_schedule` to use local dispatch.
3. Make `valid_partitioned_schedule` a trivial alias.
4. Prove `partitioned_schedule_implies_respects_assignment` (new).
5. Simplify `assignment_respect` (just delegates to step 4).
6. Prove `partitioned_schedule_implies_valid_schedule` (replaces `local_to_global_validity`).
7. Update `local_valid_feasible_implies_global`.

## Proposed Lemmas

- [x] `candidates_for` simplification (no proof needed, just type change)
- [x] `candidates_for_assign_sound` update
- [ ] `partitioned_schedule_implies_respects_assignment`
- [ ] `assignment_respect` (simplification)
- [ ] `partitioned_schedule_implies_valid_schedule` (new, replaces local_to_global_validity)
- [ ] `local_valid_feasible_implies_global` (update)

## Proof Order

1. Simplify `candidates_for` + `candidates_for_assign_sound`
2. `partitioned_schedule_implies_respects_assignment`  — uses `dispatch_in_candidates` + `candidates_for_assign_sound`
3. `assignment_respect` — trivial wrapper
4. `partitioned_schedule_implies_valid_schedule` — uses `dispatch_ready` + `completed_iff_on_assigned_cpu`
5. `local_valid_feasible_implies_global` — uses steps 2 and 4
