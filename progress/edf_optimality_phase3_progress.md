# Proof Progress: EDF Optimality Phase 3 — swap_at の定義と基本補題

## Status Overview
- Overall: Complete
- Complete Lemmas: 4/4
- Unproven (`Admitted`): none
- Failed/Abandoned Items: none

## Completed Lemmas

### `swap_at` (Definition 5)

```coq
Definition swap_at
    (sched : Schedule)
    (t1 t2 : Time) : Schedule :=
  fun t c =>
    if Nat.eqb c 0 then
      if Nat.eqb t t1 then sched t2 0
      else if Nat.eqb t t2 then sched t1 0
      else sched t c
    else sched t c.
```

Single-CPU (CPU 0) 2-point swap. When `t1 = t2` acts as identity.

### `swap_at_same_outside` (Lemma 6)

```coq
Lemma swap_at_same_outside :
  forall sched t1 t2 t c,
    c <> 0 \/ (t <> t1 /\ t <> t2) ->
    swap_at sched t1 t2 t c = sched t c.
Proof.
  intros sched t1 t2 t c Hor.
  unfold swap_at.
  destruct (Nat.eqb c 0) eqn:Hc.
  - apply Nat.eqb_eq in Hc. subst c.
    destruct Hor as [Hne | [Hne1 Hne2]].
    + exact (False_ind _ (Hne eq_refl)).
    + apply Nat.eqb_neq in Hne1. rewrite Hne1.
      apply Nat.eqb_neq in Hne2. rewrite Hne2.
      reflexivity.
  - reflexivity.
Qed.
```

### `swap_at_t1` (Lemma 7a)

```coq
Lemma swap_at_t1 :
  forall sched t1 t2,
    swap_at sched t1 t2 t1 0 = sched t2 0.
Proof.
  intros sched t1 t2.
  unfold swap_at.
  rewrite Nat.eqb_refl.
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.
```

### `swap_at_t2` (Lemma 7b)

```coq
Lemma swap_at_t2 :
  forall sched t1 t2,
    swap_at sched t1 t2 t2 0 = sched t1 0.
Proof.
  intros sched t1 t2.
  unfold swap_at.
  rewrite Nat.eqb_refl.
  destruct (Nat.eqb t2 t1) eqn:Ht.
  - apply Nat.eqb_eq in Ht. subst t1. reflexivity.
  - rewrite Nat.eqb_refl. reflexivity.
Qed.
```

Key insight: when `t2 = t1`, the `Nat.eqb t2 t1` branch fires after `Nat.eqb_refl` for CPU 0,
giving `sched t1 0 = sched t2 0` trivially by `subst`.

## Proof Attempts & Diagnostics

(none — all proved on first attempt)

## TODO

(all done)
