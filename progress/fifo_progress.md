# Proof Progress: FIFO Scheduler (FIFO.v)

## Status Overview
- Overall: Complete
- Complete Lemmas: 8/8
- Unproven (`Admitted`): none
- Failed/Abandoned Items: none

## Completed Lemmas

### Step 0: `readyb` / `readyb_iff` moved to `Schedule.v`

Refactoring (no new proof). Both definitions moved from `EDF.v` to `Schedule.v`
(placed after `cpu_count_zero_iff_not_executed` which the proof uses).
`EDF.v` now relies on `Schedule.v`'s versions.

### `choose_fifo_ready`

```coq
Lemma choose_fifo_ready : forall jobs m sched t candidates j,
    choose_fifo jobs m sched t candidates = Some j ->
    ready jobs m sched j t.
Proof.
  intros jobs m sched t candidates.
  induction candidates as [| j0 rest IH].
  - intros j H. discriminate.
  - intros j H.
    simpl in H.
    destruct (readyb jobs m sched j0 t) eqn:Erb.
    + injection H as Heq. subst j.
      apply readyb_iff. exact Erb.
    + apply IH. exact H.
Qed.
```

### `choose_fifo_none_if_no_ready`

```coq
Lemma choose_fifo_none_if_no_ready : forall jobs m sched t candidates,
    (forall j, In j candidates -> ~ready jobs m sched j t) ->
    choose_fifo jobs m sched t candidates = None.
Proof.
  intros jobs m sched t candidates Hnone.
  induction candidates as [| j0 rest IH].
  - reflexivity.
  - simpl.
    destruct (readyb jobs m sched j0 t) eqn:Erb.
    + exfalso.
      apply (Hnone j0 (or_introl eq_refl)).
      apply readyb_iff. exact Erb.
    + apply IH.
      intros j Hin. apply Hnone. right. exact Hin.
Qed.
```

### `choose_fifo_some_if_exists`

Key insight: do `induction candidates` BEFORE destructuring the existential, so the IH has type `(exists j, In j rest /\ ready ...) -> exists j', ...`.

```coq
Lemma choose_fifo_some_if_exists : forall jobs m sched t candidates,
    (exists j, In j candidates /\ ready jobs m sched j t) ->
    exists j', choose_fifo jobs m sched t candidates = Some j'.
Proof.
  intros jobs m sched t.
  induction candidates as [| h rest IHc].
  - intros [j [Hin _]]. contradiction.
  - intros [j [Hin Hready]].
    simpl.
    destruct (readyb jobs m sched h t) eqn:Erh.
    + exists h. reflexivity.
    + destruct Hin as [-> | Hin'].
      * exfalso.
        apply Bool.not_true_iff_false in Erh.
        apply Erh. apply readyb_iff. exact Hready.
      * apply IHc. exists j. split. exact Hin'. exact Hready.
Qed.
```

### `choose_fifo_in_candidates`

```coq
Lemma choose_fifo_in_candidates : forall jobs m sched t candidates j,
    choose_fifo jobs m sched t candidates = Some j ->
    In j candidates.
Proof.
  intros jobs m sched t candidates.
  induction candidates as [| j0 rest IH].
  - intros j H. discriminate.
  - intros j H.
    simpl in H.
    destruct (readyb jobs m sched j0 t) eqn:Erb.
    + injection H as Heq. subst j. left. reflexivity.
    + right. apply IH. exact H.
Qed.
```

### `fifo_generic_spec`

```coq
Definition fifo_generic_spec : GenericDispatchSpec :=
  mkGenericDispatchSpec
    choose_fifo
    choose_fifo_ready
    choose_fifo_some_if_exists
    choose_fifo_none_if_no_ready
    choose_fifo_in_candidates.
```

### `choose_fifo_first_ready`

```coq
Lemma choose_fifo_first_ready : forall jobs m sched t candidates j,
    choose_fifo jobs m sched t candidates = Some j ->
    exists prefix suffix,
      candidates = prefix ++ j :: suffix /\
      forall j', In j' prefix -> ~ready jobs m sched j' t.
Proof.
  intros jobs m sched t candidates.
  induction candidates as [| j0 rest IH].
  - intros j H. discriminate.
  - intros j H.
    simpl in H.
    destruct (readyb jobs m sched j0 t) eqn:Erb.
    + injection H as Heq. subst j.
      exists [], rest.
      split.
      * reflexivity.
      * intros j' Hin. contradiction.
    + destruct (IH j H) as [prefix [suffix [Heq Hpre]]].
      exists (j0 :: prefix), suffix.
      split.
      * simpl. rewrite Heq. reflexivity.
      * intros j' Hin.
        destruct Hin as [-> | Hin'].
        -- apply Bool.not_true_iff_false in Erb.
           intro Hready. apply Erb. apply readyb_iff. exact Hready.
        -- apply Hpre. exact Hin'.
Qed.
```

### `choose_fifo_example`

Concrete example: `[j1; j2; j3]` where j1 is completed (not ready), j2 and j3 are ready.
`choose_fifo` returns `j2` (first ready). Proved by `simpl; reflexivity`.

## TODO
(All done)
