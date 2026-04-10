# Proof Progress: EDF Optimality Phase 4 — swap_at Service Analysis

## Status Overview
- Overall: Complete
- Complete Lemmas: 11/11
- Unproven (`Admitted`): none
- Failed/Abandoned Items: none

## Completed Lemmas

All lemmas proved in `theories/UniPolicies/EDFTransform.v` (Phase 4 block, lines ~175–460).

### Helper: `cpu_count_1_swap_at_t1`
```coq
Lemma cpu_count_1_swap_at_t1 :
  forall sched t1 t2 j,
    cpu_count 1 (swap_at sched t1 t2) j t1 = cpu_count 1 sched j t2.
```
Proof: `simpl; unfold runs_on; rewrite swap_at_t1; reflexivity`.

### Helper: `cpu_count_1_swap_at_t2`
```coq
Lemma cpu_count_1_swap_at_t2 :
  forall sched t1 t2 j,
    cpu_count 1 (swap_at sched t1 t2) j t2 = cpu_count 1 sched j t1.
```
Proof: `simpl; unfold runs_on; rewrite swap_at_t2; reflexivity`.

### Helper: `cpu_count_1_swap_at_other`
```coq
Lemma cpu_count_1_swap_at_other :
  forall sched t1 t2 j t,
    t <> t1 -> t <> t2 ->
    cpu_count 1 (swap_at sched t1 t2) j t = cpu_count 1 sched j t.
```
Proof: `simpl; unfold runs_on; rewrite swap_at_same_outside; reflexivity`.

### Helper: `cpu_count_1_some_eq`
```coq
Lemma cpu_count_1_some_eq :
  forall sched j t,
    sched t 0 = Some j ->
    cpu_count 1 sched j t = 1.
```
Proof: `apply runs_on_true_iff; simpl; rewrite Hrun`.

### Helper: `cpu_count_1_some_neq`
```coq
Lemma cpu_count_1_some_neq :
  forall sched j j' t,
    sched t 0 = Some j' ->
    j <> j' ->
    cpu_count 1 sched j t = 0.
```
Proof: `apply cpu_count_zero_iff_not_executed`; case analysis; `injection` + `subst`.

### Helper: `service_job_eq_of_cpu_count_eq`
```coq
Lemma service_job_eq_of_cpu_count_eq :
  forall m (sched1 sched2 : Schedule) j T,
    (forall t, t < T -> cpu_count m sched1 j t = cpu_count m sched2 j t) ->
    service_job m sched1 j T = service_job m sched2 j T.
```
Proof: induction on T; use `service_job_step`; `f_equal`.

### Lemma 8: `swap_at_service_unchanged_other_job`
```coq
Lemma swap_at_service_unchanged_other_job :
  forall sched j j1 j2 t1 t2 T,
    sched t1 0 = Some j1 ->
    sched t2 0 = Some j2 ->
    j <> j1 ->
    j <> j2 ->
    service_job 1 (swap_at sched t1 t2) j T =
    service_job 1 sched j T.
```
Proof: `service_job_eq_of_cpu_count_eq` + case split on t=t1/t=t2/other.

### Lemma 9: `swap_at_service_prefix_before_t1`
```coq
Lemma swap_at_service_prefix_before_t1 :
  forall sched j t1 t2 T,
    t1 <= t2 ->
    T <= t1 ->
    service_job 1 (swap_at sched t1 t2) j T = service_job 1 sched j T.
```
Proof: `service_job_eq_of_cpu_count_eq`; every t < T < t1 satisfies t≠t1, t≠t2 → `cpu_count_1_swap_at_other` by lia.

### Lemma 10a: `swap_at_service_j1_back_before_t2`
```coq
Lemma swap_at_service_j1_back_before_t2 :
  forall sched j1 j2 t1 t2 T,
    t1 < t2 ->
    sched t1 0 = Some j1 ->
    sched t2 0 = Some j2 ->
    j1 <> j2 ->
    t1 < T ->
    T <= t2 ->
    service_job 1 sched j1 T = S (service_job 1 (swap_at sched t1 t2) j1 T).
```
Proof: Induction on T (keeping `t1 < T` and `T <= t2` as implications for the IH).
Base T=S t1: show prefixes equal (Lemma 9), cpu_count orig=1, cpu_count swap=0 (j2 at t1), lia.
Step T=S T': cpu_count at T' unchanged (not t1 or t2 by lia), rewrite IH with both conditions, lia.

Key pitfall: `intros` must introduce `T` before the hypotheses (`intros sched j1 j2 t1 t2 T Hlt12 Hj1 Hj2 Hne`), NOT after them. If `Hlt12` is introduced before `T`, then `induction T` actually inducts on `j1 <> j2` (a Prop), causing "Expects a disjunctive pattern with 0 branches."

Also: `Heq` direction must match `swap_at_service_prefix_before_t1`'s conclusion (LHS=swap, RHS=orig).

### Lemma 10b: `swap_at_service_j2_front_before_t2`
```coq
Lemma swap_at_service_j2_front_before_t2 :
  forall sched j1 j2 t1 t2 T,
    t1 < t2 ->
    sched t1 0 = Some j1 ->
    sched t2 0 = Some j2 ->
    j1 <> j2 ->
    t1 < T ->
    T <= t2 ->
    service_job 1 (swap_at sched t1 t2) j2 T = S (service_job 1 sched j2 T).
```
Proof: Symmetric to 10a; base T=S t1: cpu_count orig=0, cpu_count swap=1 (j2 gains t1 slot).

### Lemma 10c: `swap_at_service_j1_after_t2`
```coq
Lemma swap_at_service_j1_after_t2 :
  forall sched j1 j2 t1 t2 T,
    t1 < t2 ->
    sched t1 0 = Some j1 ->
    sched t2 0 = Some j2 ->
    j1 <> j2 ->
    t2 < T ->
    service_job 1 (swap_at sched t1 t2) j1 T = service_job 1 sched j1 T.
```
Proof: Induction on T. Base T=S t2: use Lemma 10a at t2 plus cpu_count swap=1 and cpu_count orig=0 at t2, lia. Step: cpu_count unchanged at T'>t2, rewrite IH.

### Lemma 10d: `swap_at_service_j2_after_t2`
Symmetric to 10c for j2.

## Proof Attempts & Diagnostics

### Initial compilation errors and fixes

**Error 1** (line 273): `cpu_count_1_some_neq` used with `exact` but goal had reversed equality.
Fix: use `rewrite ... ; reflexivity` instead.

**Error 2** (lines 315, 357, 398, 426): `intros sched j1 j2 t1 t2 Hlt12 Hj1 Hj2 Hne T` introduces T as the 6th hypothesis but the forall binds T as 6th variable (before the implications). This names the nat `Hlt12` and names `j1 <> j2` as `T`, causing `induction T` to fail: "Expects a disjunctive pattern with 0 branches."
Fix: `intros sched j1 j2 t1 t2 T Hlt12 Hj1 Hj2 Hne`.

**Error 3** (line 324): `Heq` asserted as `orig = swap` but `swap_at_service_prefix_before_t1` gives `swap = orig`.
Fix: swap the order of the assertion.

**Error 4** (lines 339–341, 380–382): `rewrite (IH HT'gt)` fails because IH has TWO conditions (`t1 < T'` and `T' <= t2`), and `IH HT'gt` is still an implication (not an equality).
Fix: assert `HT'le2 : T' <= t2 by lia` and use `rewrite (IH HT'gt HT'le2)`.

## TODO
(none — all complete)
