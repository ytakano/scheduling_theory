# Proof Plan: Phase 0 — Common Foundation

## Goal

Establish the foundational definitions and prove all Lv.0 lemmas from `plan/what_to_prove.md`:
- Lv.0-1: service basics (monotone, ≤1 per step, increases iff executed, no increase if not)
- Lv.0-2: completed/ready consistency
- Lv.0-3: valid_schedule basic properties

## Proof Strategy

Build bottom-up through a strict dependency chain:
1. Define all types and functions first
2. Prove definitional/structural helpers (`service_step`, `cpu_count_*`)
3. Prove no-duplication consequence (`cpu_count_le_1`)
4. Prove `service_*` lemmas using helpers
5. Prove `completed`/`ready` lemmas (mostly logic/lia)
6. Prove `valid_schedule` lemmas (destruct conjunction)

## Proposed Lemmas

### Sub-helpers (must come first)
- [x] `service_step`: `service m sched j (S t) = service m sched j t + cpu_count sched j t m`
- [x] `cpu_count_zero_iff_not_executed`: `cpu_count = 0 <-> forall c, c < m -> sched t c <> Some j`
- [x] `cpu_count_pos_iff_executed`: `0 < cpu_count <-> exists c, c < m /\ sched t c = Some j`
- [x] `cpu_count_le_1`: under `no_duplication`, `cpu_count sched j t m <= 1`
- [x] `service_le_succ`: `service m sched j t <= service m sched j (S t)`

### Lv.0-1: service basics
- [x] `service_monotone`: `t1 <= t2 -> service ... t1 <= service ... t2`
- [x] `service_increase_at_most_1`: under `no_duplication`, `service (S t) <= service t + 1`
- [x] `service_no_increase_if_not_executed`: if not executed at t, `service (S t) = service t`
- [x] `service_increases_iff_executed`: under `no_duplication`, `service (S t) = service t + 1 <-> exists c, ...`

### Lv.0-2: completed/ready
- [x] `completed_not_ready`: `completed -> ~ready`
- [x] `not_ready_before_release`: `t < release -> ~ready`
- [x] `completed_monotone`: `t1 <= t2 -> completed t1 -> completed t2`
- [x] `ready_iff_released_and_not_completed`: unfold equivalence

### Lv.0-3: valid_schedule
- [x] `valid_no_run_before_release`
- [x] `valid_no_run_after_completion`
- [x] `valid_running_implies_ready`

## Proof Order

1. `service_step`
2. `cpu_count_zero_iff_not_executed`
3. `cpu_count_pos_iff_executed`
4. `cpu_count_le_1`
5. `service_le_succ`
6. `service_monotone`
7. `service_increase_at_most_1`
8. `service_no_increase_if_not_executed`
9. `service_increases_iff_executed`
10. `completed_not_ready`
11. `not_ready_before_release`
12. `completed_monotone`
13. `ready_iff_released_and_not_completed`
14. `valid_no_run_before_release`
15. `valid_no_run_after_completion`
16. `valid_running_implies_ready`
