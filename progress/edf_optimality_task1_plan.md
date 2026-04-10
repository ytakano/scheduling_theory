# Proof Plan: eligible_feasible_implies_runs_later_before_deadline

## Goal

Add the following lemma to `theories/UniPolicies/EDFLemmas.v` (Section 6):

```coq
Lemma eligible_feasible_implies_runs_later_before_deadline :
  forall J jobs sched j t,
    J j ->
    valid_schedule jobs 1 sched ->
    feasible_schedule_on J jobs 1 sched ->
    eligible jobs 1 sched j t ->
    exists t',
      t <= t' /\
      t' < job_abs_deadline (jobs j) /\
      sched t' 0 = Some j.
```

This is "Task 1" from `plan/edf_optimality.md`: the "交換相手が後ろに存在する" (the swap target exists later) lemma.

## Proof Strategy

### Step 1: From eligible to service inequality

- `eligible jobs 1 sched j t` → `~completed jobs 1 sched j t` → `service_job 1 sched j t < job_cost (jobs j)`
  (via `not_completed_iff_service_lt_cost`)

### Step 2: From feasible to service at deadline

- `feasible_schedule_on J jobs 1 sched` + `J j` → `~missed_deadline jobs 1 sched j`
  → `completed jobs 1 sched j (job_abs_deadline (jobs j))`
  → `service_job 1 sched j (job_abs_deadline (jobs j)) >= job_cost (jobs j)`
  (via `completed_iff_service_ge_cost`)

### Step 3: Service strictly increases → execution point exists

- From steps 1 and 2: `service_job 1 sched j t < service_job 1 sched j (job_abs_deadline (jobs j))`
- This implies `t < job_abs_deadline (jobs j)` (by service_job_monotone contrapositive)
- Apply helper lemma `service_increases_implies_executed_in_interval` to get t' in [t, deadline) with `cpu_count 1 sched j t' > 0`

### Step 4: Single-CPU gives sched t' 0 = Some j

- `cpu_count_pos_iff_executed` gives `exists c, c < 1 /\ sched t' c = Some j`
- c < 1 → c = 0 (by lia)
- So `sched t' 0 = Some j`

### Helper lemma needed

```coq
Lemma service_increases_implies_executed_in_interval :
  forall m sched j t1 t2,
    t1 < t2 ->
    service_job m sched j t1 < service_job m sched j t2 ->
    exists t',
      t1 <= t' < t2 /\
      0 < cpu_count m sched j t'.
```

**Proof strategy**: Induction on `t2`.
- Base `t2 = 0`: contradiction with `t1 < 0`.
- Step `t2 = S t2'`:
  - Case A: `cpu_count m sched j t2' > 0` → t' = t2' works.
  - Case B: `cpu_count m sched j t2' = 0` → `service_job m sched j (S t2') = service_job m sched j t2'` (by `service_job_no_increase_if_not_executed` / `service_job_step + lia`)
    → so `service_job j t1 < service_job j t2'`
    - If `t1 < t2'`: apply IH, adjust bounds.
    - If `t1 = t2'`: `service_job j t1 < service_job j t1` → contradiction.

## Proposed Lemmas

- [ ] `service_increases_implies_executed_in_interval`: helper lemma
- [ ] `eligible_feasible_implies_runs_later_before_deadline`: main goal

## Proof Order

1. `service_increases_implies_executed_in_interval`
2. `eligible_feasible_implies_runs_later_before_deadline`
