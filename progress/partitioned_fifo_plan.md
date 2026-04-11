# Proof Plan: partitioned_fifo_scheduler

## Goal

Create `theories/PartitionedPolicies/PartitionedFIFO.v` — a thin wrapper
over `PartitionedCompose` that specialises the generic partitioned scheduler
to `fifo_generic_spec`, providing a convenient entry point that accepts
per-CPU `fifo_scheduler` witness schedules.

## Proof Strategy

Mirror the structure of `PartitionedEDF.v` and `PartitionedRR.v`:

1. Define `partitioned_fifo_scheduler m cands` as
   `partitioned_scheduler m fifo_generic_spec cands`.
2. Prove `local_fifo_witnesses_imply_partitioned_fifo_schedulable_by_on` by
   unfolding `fifo_scheduler` to expose the underlying `scheduler_rel` and
   then delegating to `local_witnesses_imply_partitioned_schedulable_by_on`
   from `PartitionedCompose`.

## Proposed Lemmas / Definitions

- [ ] `partitioned_fifo_scheduler` (definition)
- [ ] `local_fifo_witnesses_imply_partitioned_fifo_schedulable_by_on` (theorem)

## Proof Order

1. `partitioned_fifo_scheduler` (definition — no proof needed)
2. `local_fifo_witnesses_imply_partitioned_fifo_schedulable_by_on`

## Proof Style
- [x] Constructive (preferred)
- [ ] Classical (must justify below)
