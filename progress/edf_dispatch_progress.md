# Proof Progress: EDF Dispatch Correctness

## Status Overview
- Overall: **Complete**
- Complete Lemmas: 7/7
- Unproven (`Admitted`): none
- Failed/Abandoned Items: none

## Completed Lemmas

### `readyb_iff`

```coq
Lemma readyb_iff : forall jobs m sched j t,
    readyb jobs m sched j t = true <-> ready jobs m sched j t.
Proof.
  intros jobs m sched j t.
  unfold readyb, ready, pending, released, completed.
  rewrite Bool.andb_true_iff, Nat.leb_le, Bool.negb_true_iff.
  split; intros [H1 H2]; split; try exact H1.
  - intro Hge. apply Nat.leb_le in Hge. rewrite Hge in H2. discriminate.
  - apply Bool.not_true_iff_false. intro H. apply Nat.leb_le in H. exact (H2 H).
Qed.
```

### `min_dl_job_none_iff`

```coq
Lemma min_dl_job_none_iff : forall jobs l,
    min_dl_job jobs l = None <-> l = [].
Proof.
  intros jobs l. induction l as [| j rest IH]; simpl.
  - tauto.
  - split; [| discriminate].
    intro Hsome.
    destruct (min_dl_job jobs rest) as [j'|].
    + destruct (job_abs_deadline (jobs j) <=? job_abs_deadline (jobs j')); discriminate.
    + discriminate.
Qed.
```

### `min_dl_job_in`

```coq
Lemma min_dl_job_in : forall jobs l j,
    min_dl_job jobs l = Some j -> In j l.
Proof.
  intros jobs l. induction l as [| j0 rest IH]; simpl.
  - discriminate.
  - intros j Hsome.
    destruct (min_dl_job jobs rest) as [j'|] eqn:Erest.
    + destruct (job_abs_deadline (jobs j0) <=? job_abs_deadline (jobs j')) eqn:Ecmp.
      * injection Hsome as Heq. subst. left. reflexivity.
      * injection Hsome as Heq. subst. right. apply IH. reflexivity.
    + injection Hsome as Heq. subst. left. reflexivity.
Qed.
```

**Key pitfall**: After `destruct (min_dl_job jobs rest) as [j'|] eqn:Erest`, the IH gets
rewritten — it changes from `forall j, min_dl_job jobs rest = Some j -> In j rest`
to `forall j, Some j' = Some j -> In j rest`. So to apply IH in the false branch,
use `apply IH. reflexivity.` (not `exact Erest`).

### `min_dl_job_min`

```coq
Lemma min_dl_job_min : forall jobs l j,
    min_dl_job jobs l = Some j ->
    forall j', In j' l ->
    job_abs_deadline (jobs j) <= job_abs_deadline (jobs j').
Proof.
  intros jobs l. induction l as [| j0 rest IH]; simpl.
  - discriminate.
  - intros j Hsome j' Hin.
    destruct (min_dl_job jobs rest) as [jmin|] eqn:Erest.
    + destruct (job_abs_deadline (jobs j0) <=? job_abs_deadline (jobs jmin)) eqn:Ecmp.
      * injection Hsome as Heq. subst j.
        apply Nat.leb_le in Ecmp.
        destruct Hin as [-> | Hin'].
        -- lia.
        -- pose proof (IH jmin eq_refl j' Hin'). lia.
      * injection Hsome as Heq. subst jmin.
        apply Bool.not_true_iff_false in Ecmp.
        rewrite Nat.leb_le in Ecmp.
        destruct Hin as [-> | Hin'].
        -- lia.
        -- apply IH. reflexivity. exact Hin'.
    + injection Hsome as Heq. subst j.
      destruct Hin as [-> | Hin'].
      * lia.
      * apply min_dl_job_none_iff in Erest. subst rest. contradiction.
Qed.
```

**Key pitfall**: Same IH rewriting issue as `min_dl_job_in`. Use `eq_refl` or `reflexivity`
when applying IH, not the `eqn` hypothesis.

### `choose_edf_ready` (Theorem 1)

```coq
Theorem choose_edf_ready : forall jobs m sched t candidates j,
    choose_edf jobs m sched t candidates = Some j ->
    ready jobs m sched j t.
Proof.
  intros jobs m sched t candidates j Hchoose.
  unfold choose_edf in Hchoose.
  apply min_dl_job_in in Hchoose.
  apply filter_In in Hchoose.
  destruct Hchoose as [_ Hrb].
  apply readyb_iff. exact Hrb.
Qed.
```

### `choose_edf_min_deadline` (Theorem 2)

```coq
Theorem choose_edf_min_deadline : forall jobs m sched t candidates j,
    choose_edf jobs m sched t candidates = Some j ->
    forall j', In j' candidates ->
    ready jobs m sched j' t ->
    job_abs_deadline (jobs j) <= job_abs_deadline (jobs j').
Proof.
  intros jobs m sched t candidates j Hchoose j' Hin Hready.
  unfold choose_edf in Hchoose.
  apply (min_dl_job_min jobs _ j Hchoose).
  apply filter_In. split.
  - exact Hin.
  - apply readyb_iff. exact Hready.
Qed.
```

### `choose_edf_some_if_exists` (Theorem 3)

```coq
Theorem choose_edf_some_if_exists : forall jobs m sched t candidates,
    (exists j, In j candidates /\ ready jobs m sched j t) ->
    exists j', choose_edf jobs m sched t candidates = Some j'.
Proof.
  intros jobs m sched t candidates [j [Hin Hready]].
  unfold choose_edf.
  assert (Hne : filter (fun j => readyb jobs m sched j t) candidates <> []).
  { intro Hempty.
    assert (Hin' : In j (filter (fun j => readyb jobs m sched j t) candidates)).
    { apply filter_In. split. exact Hin. apply readyb_iff. exact Hready. }
    rewrite Hempty in Hin'. contradiction. }
  destruct (min_dl_job jobs (filter (fun j => readyb jobs m sched j t) candidates))
      as [j'|] eqn:Hmin.
  - exists j'. reflexivity.
  - apply min_dl_job_none_iff in Hmin. contradiction.
Qed.
```

## TODO

(none — all complete)
