# Proof Plan: EDF Optimality Phase 1 — 有限 horizon を job 集合から作る

## Goal

Create `theories/UniPolicies/EDFTransform.v` containing:

1. **Definition** `deadline_horizon` — computes S(max deadline in enumJ) as the finite horizon
2. **Lemma** `in_enum_implies_deadline_lt_horizon` — any job in enumJ has deadline < horizon
3. **Lemma** `J_implies_deadline_lt_horizon` — any job in J has deadline < horizon (via enumJ_complete)

These are the foundational definitions used in Phase 9 of the EDF optimality proof
to bound the time horizon to `deadline_horizon jobs enumJ`.

## New File

`theories/UniPolicies/EDFTransform.v`

Depends on: `Base.v`, `ScheduleModel.v`, `UniPolicies/EDF.v`

## Definition

```coq
Definition deadline_horizon
    (jobs : JobId -> Job)
    (enumJ : list JobId) : nat :=
  S (fold_right Nat.max 0 (map (fun j => job_abs_deadline (jobs j)) enumJ)).
```

## Proposed Lemmas

- [ ] `fold_right_max_upper_bound`: ∀ x l, In x l → x ≤ fold_right Nat.max 0 l
  (helper for the next two lemmas)
- [ ] `in_enum_implies_deadline_lt_horizon`: In j enumJ → deadline(j) < deadline_horizon jobs enumJ
- [ ] `J_implies_deadline_lt_horizon`: (∀ j, J j → In j enumJ) → J j → deadline(j) < deadline_horizon jobs enumJ

## Proof Order

1. `fold_right_max_upper_bound`
2. `in_enum_implies_deadline_lt_horizon`
3. `J_implies_deadline_lt_horizon`
