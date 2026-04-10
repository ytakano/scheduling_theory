# Proof Plan: PartitionedCompose

## Goal

Create `theories/PartitionedCompose.v` with:
1. `glue_local_schedules` definition
2. `cpu_schedule_glue_eq` lemma
3. `glue_local_rels_imply_partitioned_schedule_on` theorem
4. `local_witnesses_imply_partitioned_schedulable_by_on` theorem

And `theories/PartitionedPolicies/PartitionedEDF.v` with:
5. `partitioned_edf_scheduler` definition
6. `local_edf_witnesses_imply_partitioned_edf_schedulable_by_on` theorem

## Proof Strategy

- `glue_local_schedules`: trivial definition
- `cpu_schedule_glue_eq`: `extensionality t; extensionality cpu'`. Split on `cpu' =? 0`. For cpu'=0: unfold shows `glue` returns `locals c t 0` (since `c <? m = true`). For cpu'>0: unfold shows `None` on both sides (left from cpu_schedule, right from idle hypothesis).
- `glue_local_rels_imply_partitioned_schedule_on`: apply `partitioned_schedule_on_iff_local_rel ← (proj2 side)`. For each c < m, rewrite `cpu_schedule (glue ...) c = locals c` using `cpu_schedule_glue_eq`, then apply the local relation hypothesis.
- `local_witnesses_imply_partitioned_schedulable_by_on`: set `sched := glue m locals`. Prove `raw_partitioned_schedule_on` using step above. Rewrite `cpu_schedule sched c = locals c` in feasibility. Apply `partitioned_schedulable_by_on_from_local`.
- `partitioned_edf_scheduler`: trivial definition.
- `local_edf_witnesses_imply_partitioned_edf_schedulable_by_on`: unfold `partitioned_edf_scheduler`, note `edf_scheduler cands c = single_cpu_dispatch_schedule edf_generic_spec (cands c)`, apply `local_witnesses_imply_partitioned_schedulable_by_on`.

## Proof Style
- [x] Constructive (preferred)

## Proposed Lemmas
- [ ] `glue_local_schedules`: definition
- [ ] `cpu_schedule_glue_eq`: key identity lemma
- [ ] `glue_local_rels_imply_partitioned_schedule_on`: local rels → partitioned schedule
- [ ] `local_witnesses_imply_partitioned_schedulable_by_on`: main entry theorem
- [ ] `partitioned_edf_scheduler`: EDF wrapper definition
- [ ] `local_edf_witnesses_imply_partitioned_edf_schedulable_by_on`: EDF intro theorem

## Proof Order
1. `glue_local_schedules`
2. `cpu_schedule_glue_eq`
3. `glue_local_rels_imply_partitioned_schedule_on`
4. `local_witnesses_imply_partitioned_schedulable_by_on`
5. `partitioned_edf_scheduler`
6. `local_edf_witnesses_imply_partitioned_edf_schedulable_by_on`
