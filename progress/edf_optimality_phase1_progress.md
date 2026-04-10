# Proof Progress: EDF Optimality Phase 1

## Status Overview
- Overall: Complete
- Complete Lemmas: 3/3
- Unproven (`Admitted`): none
- Failed/Abandoned Items: none

## Completed Lemmas

### `fold_right_max_upper_bound`

Helper: every element of a `list nat` is ≤ `fold_right Nat.max 0` of that list.

```coq
Lemma fold_right_max_upper_bound :
  forall (l : list nat) (x : nat),
    In x l ->
    x <= fold_right Nat.max 0 l.
Proof.
  intros l x Hin.
  induction l as [| h rest IH].
  - contradiction.
  - simpl. destruct Hin as [-> | Hin'].
    + apply Nat.le_max_l.
    + apply Nat.le_trans with (fold_right Nat.max 0 rest).
      * apply IH. exact Hin'.
      * apply Nat.le_max_r.
Qed.
```

### `in_enum_implies_deadline_lt_horizon`

Any job in `enumJ` has deadline strictly less than `deadline_horizon`.

```coq
Lemma in_enum_implies_deadline_lt_horizon :
  forall jobs enumJ j,
    In j enumJ ->
    job_abs_deadline (jobs j) < deadline_horizon jobs enumJ.
Proof.
  intros jobs enumJ j Hin.
  unfold deadline_horizon.
  apply Nat.lt_succ_r.
  apply fold_right_max_upper_bound.
  exact (in_map (fun j0 => job_abs_deadline (jobs j0)) enumJ j Hin).
Qed.
```

### `J_implies_deadline_lt_horizon`

Any job in J has deadline < horizon, given a complete enumeration.

```coq
Lemma J_implies_deadline_lt_horizon :
  forall J enumJ jobs j,
    (forall j, J j -> In j enumJ) ->
    J j ->
    job_abs_deadline (jobs j) < deadline_horizon jobs enumJ.
Proof.
  intros J enumJ jobs j Hcomplete HJj.
  apply in_enum_implies_deadline_lt_horizon.
  apply Hcomplete. exact HJj.
Qed.
```

## Proof Attempts & Diagnostics

### `apply in_map` unification issue

`apply in_map` failed inside `in_enum_implies_deadline_lt_horizon` because Rocq's
unifier matched `f := fun j0 => job_abs_deadline j0` (treating `jobs j0` as `j0`)
instead of `f := fun j0 => job_abs_deadline (jobs j0)`.

Fixed by using explicit application:
```coq
exact (in_map (fun j0 => job_abs_deadline (jobs j0)) enumJ j Hin).
```

## TODO

(all done)
