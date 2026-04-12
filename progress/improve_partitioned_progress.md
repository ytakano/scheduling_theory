# Proof Progress: improve_partitioned

## Status Overview
- Overall: Complete
- Complete Steps: 11/11
- Unproven (`Admitted`): none
- Failed/Abandoned Items: none

## Completed Steps

### Step I — Stabilize theorem-layer naming

Added public-facing theorem names that separate the partitioned layers more explicitly:

```coq
Definition feasible_partitioned_schedule_on :
  ...

Theorem service_partitioned_eq_local_service :
  ...

Corollary completed_partitioned_iff_local_completed :
  ...

Lemma eligible_local_implies_eligible_global_on_assigned_cpu :
  ...

Lemma global_running_implies_running_on_assigned_cpu :
  ...
```

Kept compatibility names such as `service_decomposition` and
`completed_iff_on_assigned_cpu` as thin aliases.

### Step J — Promote glue-layer public lemmas

`PartitionedCompose.v` now exposes the glue/composition API explicitly:

- `glue_cpu_schedule_eq_local`
- `glue_other_cpus_idle_local_view`
- `glue_respects_assignment`
- `glue_valid_if_local_valid`
- `glue_feasible_on_if_local_feasible_on`

This makes the local-witness -> global-witness proof pattern reusable without
re-deriving helper equalities from internal names.

### Step K — Factor policy wrapper lifting

Added `theories/Multicore/Partitioned/Policies/PartitionedPolicyLift.v` with:

```coq
Theorem local_policy_witnesses_imply_partitioned_schedulable_by_on : ...
Theorem local_policy_schedulable_by_on_implies_partitioned_schedulable_by_on : ...
```

Updated `PartitionedEDF.v`, `PartitionedFIFO.v`, `PartitionedRR.v`, and
`PartitionedLLF.v` to instantiate these generic theorems instead of repeating
the same lifting proof script in each file.

### Step A — Strengthen `valid_partitioned_schedule`

Changed from alias to two-component conjunction:
```coq
Definition valid_partitioned_schedule (jobs : JobId -> Job) (sched : Schedule) : Prop :=
  raw_partitioned_schedule_on jobs sched /\
  respects_assignment sched.
```

### Step B — New public API lemmas

```coq
Lemma valid_partitioned_schedule_intro :
  forall jobs sched,
    raw_partitioned_schedule_on jobs sched ->
    respects_assignment sched ->
    valid_partitioned_schedule jobs sched.

Lemma valid_partitioned_schedule_raw :
  forall jobs sched,
    valid_partitioned_schedule jobs sched ->
    raw_partitioned_schedule_on jobs sched.

Lemma valid_partitioned_schedule_respects_assignment :
  forall jobs sched,
    valid_partitioned_schedule jobs sched ->
    respects_assignment sched.
```

Replaced `valid_partitioned_schedule_elim` (deprecated).

### Step C — Updated theorems inside PartitionedSection

- `assignment_respect`: now uses `valid_partitioned_schedule_respects_assignment`
- `partitioned_schedule_implies_valid_schedule`: extracts raw/respects via projection lemmas
- `local_valid_feasible_implies_global` (deprecated): builds `valid_partitioned_schedule` first from raw + respects
- `local_valid_feasible_on_implies_global`: uses `valid_partitioned_schedule_respects_assignment`

### Step D — Updated `partitioned_schedulable_by_on_from_local`

Key design decision: `partitioned_scheduler` stores `raw_partitioned_schedule_on` (not
`valid_partitioned_schedule`) because `respects_assignment` depends on `assign` which is not
a parameter of `partitioned_scheduler`. When building the `scheduler_rel`, we extract raw
from `Hvps` using `valid_partitioned_schedule_raw`.

```coq
  - unfold partitioned_scheduler, scheduler_rel. split.
    + reflexivity.
    + exact (valid_partitioned_schedule_raw assign n spec cands jobs sched Hvps).
```

Also updated `partitioned_schedule_implies_valid_schedule` call to remove `J` and `cands_spec`
args (no longer included in discharge after switching away from `partitioned_schedule_implies_respects_assignment`).

### Step E — Updated `PartitionedCompose.v`

`local_witnesses_imply_partitioned_schedulable_by_on` now builds `valid_partitioned_schedule`
by:
1. Proving `Hraw` via `glue_local_rels_imply_partitioned_schedule_on`
2. Deriving `respects_assignment` via `partitioned_schedule_implies_respects_assignment` on `Hraw`
3. Combining with `valid_partitioned_schedule_intro`

### Step F — Updated `SchedulableExamples.v`

- `pair_partitioned_schedule`: added `respects_assignment assign_pair 2 pair_sched` proof
- `pair_partitioned_rel`: uses `valid_partitioned_schedule_raw` to extract raw for `scheduler_rel`
- `pair_partitioned_valid`: removed `J_pair` and `pair_cands_spec` from call (no longer in discharge)

### Steps G — Updated comments

Updated `valid_partitioned_schedule` doc comment to describe the two-component definition and
projection API.

### Step H — Full build passes

`make` with zero errors.

## Key Design Notes

- `partitioned_scheduler` stores `raw_partitioned_schedule_on` (not `valid_partitioned_schedule`)
  because `respects_assignment` depends on `assign` (section variable), but `partitioned_scheduler`
  is defined outside the section and doesn't take `assign` as a parameter.
- `valid_partitioned_schedule` is the *client-facing* predicate (stronger than `scheduler_rel`).
  Clients prove it via `valid_partitioned_schedule_intro` and use it to derive validity/feasibility.
- `valid_partitioned_schedule_elim` was removed; clients should use the two projection lemmas.
