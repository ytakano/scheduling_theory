# Proof Progress: EDFLemmas Section 2 — Prefix agreement 補題

## Status Overview
- Overall: Complete
- Complete Lemmas: 10/10
- Unproven (`Admitted`): none
- Failed/Abandoned Items: none

## Completed Lemmas

### `agrees_before` (definition)

```coq
Definition agrees_before (s1 s2 : Schedule) (t : Time) : Prop :=
  forall t' c, t' < t -> s1 t' c = s2 t' c.
```

### `agrees_before_weaken`

```coq
Lemma agrees_before_weaken :
  forall s1 s2 t1 t2,
    t1 <= t2 ->
    agrees_before s1 s2 t2 ->
    agrees_before s1 s2 t1.
Proof.
  intros s1 s2 t1 t2 Hle Hagree t' c Hlt.
  apply Hagree. lia.
Qed.
```

### `agrees_before_refl`

```coq
Lemma agrees_before_refl :
  forall s t, agrees_before s s t.
Proof.
  intros s t t' c _. reflexivity.
Qed.
```

### `agrees_before_sym`

```coq
Lemma agrees_before_sym :
  forall s1 s2 t, agrees_before s1 s2 t -> agrees_before s2 s1 t.
Proof.
  intros s1 s2 t Hagree t' c Hlt.
  symmetry. apply Hagree. exact Hlt.
Qed.
```

### `agrees_before_trans`

```coq
Lemma agrees_before_trans :
  forall s1 s2 s3 t,
    agrees_before s1 s2 t ->
    agrees_before s2 s3 t ->
    agrees_before s1 s3 t.
Proof.
  intros s1 s2 s3 t H12 H23 t' c Hlt.
  rewrite (H12 t' c Hlt). apply H23. exact Hlt.
Qed.
```

### `cpu_count_agrees_at` (helper)

```coq
Lemma cpu_count_agrees_at :
  forall m s1 s2 j t,
    (forall c, s1 t c = s2 t c) ->
    cpu_count m s1 j t = cpu_count m s2 j t.
Proof.
  induction m as [| m' IH]; intros s1 s2 j t Heq.
  - simpl. reflexivity.
  - simpl.
    unfold runs_on.
    rewrite (Heq m').
    rewrite (IH s1 s2 j t Heq).
    reflexivity.
Qed.
```

### `agrees_before_service_job`

```coq
Lemma agrees_before_service_job :
  forall m s1 s2 j t,
    agrees_before s1 s2 t ->
    service_job m s1 j t = service_job m s2 j t.
Proof.
  intros m s1 s2 j t Hagree.
  induction t as [| t' IH].
  - simpl. reflexivity.
  - rewrite (service_job_step m s1 j t').
    rewrite (service_job_step m s2 j t').
    assert (Hcpu : cpu_count m s1 j t' = cpu_count m s2 j t').
    { apply cpu_count_agrees_at.
      intro c. apply Hagree. lia. }
    assert (Hpre : agrees_before s1 s2 t').
    { apply (agrees_before_weaken s1 s2 t' (S t')). lia. exact Hagree. }
    rewrite (IH Hpre). rewrite Hcpu. reflexivity.
Qed.
```

### `agrees_before_completed`

```coq
Lemma agrees_before_completed :
  forall jobs m s1 s2 j t,
    agrees_before s1 s2 t ->
    completed jobs m s1 j t <-> completed jobs m s2 j t.
Proof.
  intros jobs m s1 s2 j t Hagree.
  unfold completed.
  rewrite (agrees_before_service_job m s1 s2 j t Hagree).
  tauto.
Qed.
```

### `agrees_before_eligible`

```coq
Lemma agrees_before_eligible :
  forall jobs m s1 s2 j t,
    agrees_before s1 s2 t ->
    eligible jobs m s1 j t <-> eligible jobs m s2 j t.
Proof.
  intros jobs m s1 s2 j t Hagree.
  unfold eligible.
  pose proof (agrees_before_completed jobs m s1 s2 j t Hagree) as Hcomp.
  tauto.
Qed.
```

### `agrees_before_ready`

```coq
(* 注意: running は s t c を直接参照するため、agrees_before s1 s2 (S t) が必要 *)
Lemma agrees_before_ready :
  forall jobs m s1 s2 j t,
    agrees_before s1 s2 (S t) ->
    ready jobs m s1 j t <-> ready jobs m s2 j t.
Proof.
  intros jobs m s1 s2 j t Hagree.
  assert (Hpre : agrees_before s1 s2 t)
    by (apply (agrees_before_weaken s1 s2 t (S t)); [lia | exact Hagree]).
  pose proof (agrees_before_eligible jobs m s1 s2 j t Hpre) as Helig.
  assert (Hat : forall c, s1 t c = s2 t c)
    by (intro c; apply Hagree; lia).
  unfold ready.
  split.
  - intros [Hel Hnrun].
    split.
    + exact (proj1 Helig Hel).
    + unfold running. intros [c [Hlt Hrun]].
      apply Hnrun. exists c. split. exact Hlt.
      rewrite (Hat c). exact Hrun.
  - intros [Hel Hnrun].
    split.
    + exact (proj2 Helig Hel).
    + unfold running. intros [c [Hlt Hrun]].
      apply Hnrun. exists c. split. exact Hlt.
      rewrite <- (Hat c). exact Hrun.
Qed.
```

## Proof Attempts & Diagnostics

### `agrees_before_ready` — rewrite direction bug (fixed)

- Attempt 1: used `rewrite <- (Hat c)` in first branch, `rewrite (Hat c)` in second branch.
- Error: "Found no subterm matching 's2 t c'" at line 276.
- Diagnosis: In the first branch (s1→s2), after `apply Hnrun`, goal is `s1 t c = Some j` and
  `Hrun : s2 t c = Some j`. Need `rewrite (Hat c)` (replaces `s1 t c` with `s2 t c`), not `<-`.
  In second branch (s2→s1), goal is `s2 t c = Some j` and `Hrun : s1 t c = Some j`.
  Need `rewrite <- (Hat c)` (replaces `s2 t c` with `s1 t c`).
- Fix: swap directions. Resolved.

### Key design decision: `agrees_before_ready` uses `agrees_before s1 s2 (S t)`

- `running m s j t` references `s t c` at time `t` directly.
- `agrees_before s1 s2 t` only covers `t' < t` (strictly), so `s1 t c = s2 t c` is NOT available.
- Solution: strengthen the hypothesis to `agrees_before s1 s2 (S t)`, which covers `t' < S t`,
  i.e., `t' <= t`, giving us `s1 t c = s2 t c` via `Hagree t c (lia)`.
- The plan noted this issue in advance.

## TODO

(all done)
