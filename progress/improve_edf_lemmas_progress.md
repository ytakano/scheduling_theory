# Proof Progress: improve_edf_lemmas

## Status Overview
- Overall: Complete
- Complete Lemmas: 14/14
- Unproven (`Admitted`): none
- Failed/Abandoned Items: none

## Completed Lemmas

### `edf_violation_at_in` (definition, Section 7)

```coq
Definition edf_violation_at_in
    (J : JobId -> Prop)
    (jobs : JobId -> Job)
    (sched : Schedule)
    (t : Time)
    (cands : list JobId) : Prop :=
  exists j j',
    J j /\ J j' /\
    sched t 0 = Some j /\
    In j' cands /\
    eligible jobs 1 sched j' t /\
    job_abs_deadline (jobs j') < job_abs_deadline (jobs j).
```

### `edf_violation_at_with` (definition, Section 7)

```coq
Definition edf_violation_at_with J candidates_of jobs sched t :=
  edf_violation_at_in J jobs sched t (candidates_of jobs 1 sched t).
```

### `matches_choose_edf_at_with_no_finite_violation` (Section 7)

Wraps `matches_choose_edf_at_with_no_earlier_eligible_job`. Unfold the violation,
extract j/j', and apply the existing lemma.

### `edf_violationb_in` (definition, Section 8)

Boolean version using `existsb`, `eligibleb`, `Nat.ltb`.

### `edf_violationb_at_with` (definition, Section 8)

Wraps `edf_violationb_in` with `candidates_of jobs 1 sched t`.

### `edf_violationb_in_true_iff` (Section 8)

Forward: `destruct (sched t 0)` → `andb_true_iff` → `existsb_exists` → `Nat.ltb_lt` → `eligibleb_iff` → `proj1 (HJ_bool ...)`.
Backward: `rewrite Hsched` → `andb_true_iff` → `existsb_exists` → `proj2 (HJ_bool ...)` → `eligibleb_iff` → `Nat.ltb_lt`.

⚠️ After `destruct (sched t 0) as [j|] eqn:Hsched`, the goal's `sched t 0` is replaced by `Some j`, so the `sched t 0 = Some j` sub-goal becomes `Some j = Some j` → needs `reflexivity`, NOT `exact Hsched`.

### `edf_violationb_at_with_true_iff` (Section 8)

Corollary: unfold both `_at_with` versions and apply `edf_violationb_in_true_iff`.

### `find_first_in_range` (Fixpoint, Section 9)

```coq
Fixpoint find_first_in_range (p : nat -> bool) (base n : nat) : option nat :=
  match n with
  | 0 => None
  | S n' => if p base then Some base else find_first_in_range p (S base) n'
  end.
```

### `find_first_in_range_some_spec` (Section 9)

Induction on n. Use `cbn in H` (not `simpl`) to unfold one step.
For `p base = true`: `injection H as Heq. rewrite <- Heq.` to unify t0 with base.
For `p base = false`: `specialize (IH p (S base) t0 H) as [[Hlo Hhi] [Hpt0 Hmin]]` then adjust bounds with `lia`.
Minimality for `t = base`: `exact Hpbase`. For `t > base`: `apply Hmin. lia.`.

⚠️ The minimality branch `intros t Hle Hlt. lia.` requires BOTH `Hle : base <= t` and `Hlt : t < base` in context — do NOT discard `Hle` with `_`.

### `find_first_in_range_none_spec` (Section 9)

Induction on n. Base: `lia` closes vacuous goal.
`S n'`: if `p base = true`, discriminate. Otherwise: `t = base` case uses `Hpbase`; `t > base` case delegates to IH.

### `first_nat_up_to` (definition, Section 9)

```coq
Definition first_nat_up_to H p := find_first_in_range p 0 H.
```

### `first_nat_up_to_some_spec` (Section 9)

Apply `find_first_in_range_some_spec`, discard `0 <= t0`, adjust `t0 < 0 + H` to `t0 < H` via `lia`.
Minimality: `apply Hmin. lia. exact Hlt.`

### `first_nat_up_to_none_spec` (Section 9)

Apply `find_first_in_range_none_spec H p 0 Hnone t (Nat.le_0_l t) Hlt`.
`Hlt : t < H` unifies with `t < 0 + H` by definitional equality.

### `exists_first_edf_violation_before_with` (Section 9)

1. Convert Prop violation to Boolean via `edf_violationb_at_with_true_iff`.
2. `destruct (first_nat_up_to H ...) as [t0|] eqn:Hopt`.
3. Some branch: apply `first_nat_up_to_some_spec`, convert back via iff, use minimality.
4. None branch: `pose proof (first_nat_up_to_none_spec ...) as Hcontra. rewrite Hcontra in Hviol_b. discriminate.`

## Proof Attempts & Diagnostics

- `repeat split; assumption` failed at `edf_violationb_in_true_iff` because after `destruct (sched t 0)` the `sched t 0 = Some j` sub-goal reduces to `Some j = Some j` → fixed with `reflexivity`.
- `intros t _ Hlt. lia.` failed at `find_first_in_range_some_spec` because `lia` needs BOTH `base <= t` and `t < base` to derive contradiction → fixed by keeping `Hle` instead of `_`.

## TODO

(all done)
