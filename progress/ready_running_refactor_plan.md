> Obsolete note
>
> This is a historical refactoring plan. The current source of truth is
> `ScheduleModel.v`, `DispatchInterface.v`, and `SchedulerInterface.v`.

# Proof Plan: ready_running_refactor

## Goal

Redefine `ready` as `runnable AND NOT running` (where `running` is CPU-bounded),
and update `valid_schedule` to use `runnable` directly.

The change refines the state vocabulary:
- `runnable` = released AND NOT completed (dispatch-eligible pool)
- `ready`    = runnable AND NOT running   (waiting in ready queue)
- `running`  = exists c < m, sched t c = Some j (currently executing)

## Proof Strategy

This is a multi-file refactoring. Work file-by-file, compiling after each file.
No Admitted blocks needed since each change is a definition or proof update.

## Proposed Changes

### Schedule.v
- [ ] `running` definition: add `m : nat`, add `c < m` bound
- [ ] `ready` definition: add `~running sched m j t` conjunct
- [ ] `valid_schedule` definition: use `runnable` instead of `ready`
- [ ] Remove `valid_running_implies_ready` (now false)
- [ ] Rename `ready_iff_released_and_not_completed` → `ready_iff_runnable_and_not_running`
- [ ] Add `runnable_iff_released_and_not_completed`
- [ ] Add `ready_implies_not_running`
- [ ] Add `running_implies_not_ready`
- [ ] Update `ready_implies_runnable` proof (no longer definitional)
- [ ] Update `pending_not_ready` proof
- [ ] Update `valid_no_run_before_release` proof
- [ ] Update `valid_no_run_after_completion` proof
- [ ] Update `scheduled_implies_running` (add `c < m` hypothesis)
- [ ] Update `valid_running_implies_runnable` proof (now direct from valid_schedule)

### EDF.v
- [ ] `readyb` definition: add `cpu_count sched j t m =? 0`
- [ ] `readyb_iff` proof: rewrite to use `cpu_count_pos_iff_executed` / `cpu_count_zero_iff_not_executed`

### UniSchedulerLemmas.v
- [ ] `choose_some_implies_runnable` proof: use `ready_implies_runnable` instead of unfold
- [ ] `choose_none_implies_each_candidate_unreleased_or_completed`: add `\/ running sched m j t` to statement; update proof

## Proof Order

1. Apply all Schedule.v changes → `rocq compile Base.v && rocq compile Schedule.v`
2. Apply EDF.v changes → `rocq compile EDF.v`
3. Apply UniSchedulerLemmas.v changes → `rocq compile UniSchedulerLemmas.v`
4. Final check: compile all files
