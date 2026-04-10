# Proof Progress: EDF Optimality Phase 5 — swap_at preserves valid_schedule

## Status Overview
- Overall: Complete
- Complete Lemmas: 4/4
- Unproven (`Admitted`): none
- Failed/Abandoned Items: none

## Completed Lemmas

### `valid_schedule_1_service_le_cost` (Helper)
```coq
Lemma valid_schedule_1_service_le_cost :
  forall jobs sched j T,
    valid_schedule jobs 1 sched ->
    service_job 1 sched j T <= job_cost (jobs j).
Proof.
  intros jobs sched j T Hvalid.
  induction T as [| T' IH].
  - simpl. lia.
  - rewrite service_job_step.
    destruct (Nat.eq_dec (cpu_count 1 sched j T') 0) as [Hz | Hnz].
    + rewrite Hz. lia.
    + assert (Hpos : 0 < cpu_count 1 sched j T') by lia.
      apply cpu_count_pos_iff_executed in Hpos.
      destruct Hpos as [c [Hlt Hrun]].
      assert (Hc : c = 0) by lia. subst c.
      assert (Hncomp : ~completed jobs 1 sched j T').
      { exact (valid_no_run_after_completion jobs 1 sched j T' 0 Hvalid
                 (Nat.lt_succ_diag_r 0) Hrun). }
      apply not_completed_iff_service_lt_cost in Hncomp.
      assert (Hcpu1 : cpu_count 1 sched j T' = 1).
      { apply cpu_count_1_some_eq. exact Hrun. }
      lia.
Qed.
```

### Lemma 11: `swap_at_validity_new_front_job`
```coq
Lemma swap_at_validity_new_front_job :
  forall jobs sched j j' t t',
    valid_schedule jobs 1 sched ->
    sched t 0 = Some j ->
    sched t' 0 = Some j' ->
    t <= t' ->
    eligible jobs 1 sched j' t ->
    eligible jobs 1 (swap_at sched t t') j' t.
Proof.
  intros jobs sched j j' t t' Hvalid Hj Hj' Hle Helig.
  split.
  - exact (proj1 Helig).
  - intro Hcomp_swap.
    apply (proj2 Helig).
    unfold completed in *.
    rewrite (swap_at_service_prefix_before_t1 sched j' t t' t Hle (Nat.le_refl t))
      in Hcomp_swap.
    exact Hcomp_swap.
Qed.
```

### Lemma 12: `swap_at_validity_new_back_job`
```coq
Lemma swap_at_validity_new_back_job :
  forall jobs sched j j' t t',
    valid_schedule jobs 1 sched ->
    sched t 0 = Some j ->
    sched t' 0 = Some j' ->
    t <= t' ->
    job_abs_deadline (jobs j') < job_abs_deadline (jobs j) ->
    eligible jobs 1 (swap_at sched t t') j t'.
Proof.
  intros jobs sched j j' t t' Hvalid Hj Hj' Hle Hdl.
  assert (Hne : j <> j') by (intro Heq; subst; lia).
  split.
  - unfold released.
    apply (valid_no_run_before_release jobs 1 sched j t 0 Hvalid
             (Nat.lt_succ_diag_r 0)) in Hj.
    lia.
  - intro Hcomp_swap.
    unfold completed in Hcomp_swap.
    assert (Hlt : t < t').
    { destruct (Nat.eq_dec t t') as [Heqt | Hlt].
      - subst t'. rewrite Hj in Hj'. injection Hj' as Heqjj'. exfalso. exact (Hne Heqjj').
      - lia. }
    assert (Hservice : service_job 1 sched j t' =
                       S (service_job 1 (swap_at sched t t') j t')).
    { exact (swap_at_service_j1_back_before_t2 sched j j' t t' t'
               Hlt Hj Hj' Hne Hlt (Nat.le_refl t')). }
    assert (Hbound : service_job 1 sched j t' <= job_cost (jobs j)).
    { exact (valid_schedule_1_service_le_cost jobs sched j t' Hvalid). }
    lia.
Qed.
```

### Lemma 13: `swap_at_preserves_valid_schedule`
```coq
Lemma swap_at_preserves_valid_schedule :
  forall jobs sched j j' t t',
    valid_schedule jobs 1 sched ->
    sched t 0 = Some j ->
    sched t' 0 = Some j' ->
    eligible jobs 1 sched j' t ->
    t <= t' ->
    job_abs_deadline (jobs j') < job_abs_deadline (jobs j) ->
    valid_schedule jobs 1 (swap_at sched t t').
```
Full proof in `theories/UniPolicies/EDFTransform.v` (Phase 5 block).
Key steps: derive `t < t'` up front; case split on t''=t (L11), t''=t' (L12), other;
for the other case: case on j''∈{j, j', other}, then for each: ordering subcase
gives service equality/inequality via Lemmas 8/9/10a-d; the tricky case j''=j',
t<t''<t' uses service_job_step + service_job_monotone + valid_no_run_after_completion
at t' to prove service_swap(j', t'') = service_orig + 1 < job_cost.

## Proof Attempts & Diagnostics

### Compilation errors encountered and fixed

**Error 1** (swap_at_validity_new_back_job): `exact (Hne Heqjj')` has type `False` but
goal expected `t < t`. Fix: add `exfalso.` before.

**Error 2** (swap_at_validity_new_back_job): Called `swap_at_service_j1_back_before_t2`
with `Nat.lt_succ_diag_r t'` (= `t' < S t'`) for the `t1 < T` argument, but needed `t < t'`.
Fix: pass `Hlt` directly.

**Error 3** (swap_at_preserves_valid_schedule L11/L12 cases): Used `injection Hrun as Heq`
after `rewrite swap_at_t1/t2 in Hrun`, but `Hrun : sched t' 0 = Some j''` is not a
constructor application. Fix: first `rewrite Hj'` (or `Hj`) to get `Some j' = Some j''`,
then inject.

**Error 4** (two name clashes): `Hge_t'` was used both as `assert (Hge_t' : t <= t'') by lia`
and as the `else` branch of `destruct (lt_dec t'' t')`. Fix: rename assert to `Hle_t`.

**Error 5** (j=j' branch lia): `assert (Hlt12 : t < t') by lia` failed because `t < t'`
was not derivable from context when `t = t'` was possible. Fix: derive `Hlt : t < t'`
at the top of the main lemma (using Hne + Hj + Hj').

## TODO
(none — all complete)
