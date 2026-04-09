# Proof Plan: Partitioned Bridge Refactoring

## Goal

Refactor `DispatchInterface.v`, `DispatchSchedulerBridge.v`, and `Partitioned.v`
so that `Partitioned.v` reads as the extension of `DispatchSchedulerBridge.v`,
and `schedulable_by_on` has a canonical route in both single-CPU and partitioned cases.

## Changes Made

1. `DispatchInterface.v` — comments clarified (no signature changes)
2. `DispatchSchedulerBridge.v` — restructured, 2 new lemmas, `_intro` rename
3. `Partitioned.v` — bridge import, `local_jobset`, `local_candidates_of`,
   `local_candidates_spec`, `partitioned_schedule_on_iff_local_rel`,
   `local_feasible_on_implies_global_feasible_on`,
   `local_valid_feasible_on_implies_global`,
   `partitioned_schedulable_by_on_intro`

## Status: Complete
