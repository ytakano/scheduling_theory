# Proof Plan: valid_partitioned_schedule_intro / valid_partitioned_schedule_elim

## Goal

Add introduction and elimination lemmas for `valid_partitioned_schedule` in `Partitioned.v`,
and update `SchedulableExamples.v` to use them.

## Proof Strategy

Both lemmas are trivially `exact H` since `valid_partitioned_schedule` is currently
definitionally equal to `partitioned_schedule_on`. The value is as an abstraction boundary.

## Proposed Lemmas

- [ ] `valid_partitioned_schedule_intro`: `partitioned_schedule_on → valid_partitioned_schedule`
- [ ] `valid_partitioned_schedule_elim`: `valid_partitioned_schedule → partitioned_schedule_on`
- [ ] Update `pair_partitioned_schedule` in `SchedulableExamples.v`

## Proof Order

1. `valid_partitioned_schedule_intro`
2. `valid_partitioned_schedule_elim`
3. Update `SchedulableExamples.v` and verify with `make`
