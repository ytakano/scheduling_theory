# Proof Knowledge Base

## Lemmas and Theorems

### `runs_on_true_iff`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma runs_on_true_iff : forall sched j t c,
      runs_on sched j t c = true <-> sched t c = Some j.
  ```
- **Proof Strategy**: Unfold `runs_on`, destruct `sched t c`. In the `Some j'` branch: forward uses `Nat.eqb_eq` + `subst`; backward uses `injection H as Heq; subst; apply Nat.eqb_refl`. In the `None` branch: both directions by `discriminate`.
- **Key Tactics**: `unfold runs_on`, `Nat.eqb_eq`, `subst`, `injection H as Heq`, `Nat.eqb_refl`, `discriminate`
- **Dependencies**: `runs_on`
- **Notes**: Use `injection H as Heq; subst` rather than `injection H as ->` — the `as ->` syntax causes a syntax error in Rocq 9.
- **Date**: 2026-04-06

---

### `runs_on_false_iff`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma runs_on_false_iff : forall sched j t c,
      runs_on sched j t c = false <-> sched t c <> Some j.
  ```
- **Proof Strategy**: Unfold `runs_on`, destruct `sched t c`. In `Some j'` branch: forward uses `Nat.eqb_neq` then `injection + subst + eq_refl`; backward uses `Nat.eqb_neq` then `subst + eq_refl`. In `None` branch: forward by `discriminate`, backward by `reflexivity`.
- **Key Tactics**: `Nat.eqb_neq`, `injection H as Heq'`, `subst`, `exact (H eq_refl)`
- **Dependencies**: `runs_on`
- **Notes**: `exact (H eq_refl)` works after `subst` makes `H : A <> A`, giving `H (eq_refl : A = A) : False`.
- **Date**: 2026-04-06

---

### `service_step`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma service_step : forall m sched j t,
      service m sched j (S t) = service m sched j t + cpu_count sched j t m.
  ```
- **Proof Strategy**: Direct by `simpl; reflexivity` — matches the Fixpoint definition exactly.
- **Key Tactics**: `simpl`, `reflexivity`
- **Dependencies**: `service`, `cpu_count`
- **Notes**: Always use this as a rewrite lemma (`rewrite service_step`) rather than unfolding `service` manually.
- **Date**: 2026-04-06

---

### `cpu_count_zero_iff_not_executed`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma cpu_count_zero_iff_not_executed : forall m sched j t,
      cpu_count sched j t m = 0 <->
      forall c, c < m -> sched t c <> Some j.
  ```
- **Proof Strategy**: Induction on `m`. Base: trivial. Step (`S m'`): destruct `runs_on sched j t m'` with `eqn:Erun`. Forward: if `runs_on = true`, `lia` (1 + ... = 0 contradiction); if `runs_on = false`, use `Nat.lt_succ_r` then `Nat.eq_dec c m'` to split — for `c = m'` apply `runs_on_false_iff`, for `c < m'` apply `proj1 (IH sched j t) Hzero` on goal. Backward: if `runs_on = true`, get `Hnone m' ... Erun` and `exfalso`; if `runs_on = false`, apply `proj2 (IH sched j t)`.
- **Key Tactics**: `induction m as [| m' IH]`, `destruct (runs_on ...) eqn:Erun`, `Nat.lt_succ_r`, `Nat.eq_dec`, `runs_on_false_iff`, `proj1`, `proj2`
- **Dependencies**: `cpu_count`, `runs_on_true_iff`, `runs_on_false_iff`
- **Notes**: ⚠️ Do NOT use `apply (proj1 (IH sched j t)) in Hzero` when `c` is already in scope — Rocq 9 fails with "Unable to find an instance for the variable c". Instead apply on the GOAL: `apply (proj1 (IH sched j t) Hzero)`. This is the critical fix.
- **Date**: 2026-04-06

---

### `cpu_count_pos_iff_executed`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma cpu_count_pos_iff_executed : forall m sched j t,
      0 < cpu_count sched j t m <->
      exists c, c < m /\ sched t c = Some j.
  ```
- **Proof Strategy**: Induction on `m`. Base: both directions trivial by `lia`. Step: forward — destruct `runs_on`, if true: witness is `m'`; if false: use `proj1 (IH sched j t) Hpos` and `destruct` with fresh names. Backward — `Nat.lt_succ_r` then `Nat.eq_dec c m'`; if `c = m'`: rewrite `runs_on` to true via `runs_on_true_iff`; if `c < m'`: use `proj2 (IH sched j t)` then `lia`.
- **Key Tactics**: `induction m as [| m' IH]`, `Nat.lt_succ_r`, `Nat.eq_dec`, `runs_on_true_iff`, `proj1`, `proj2`
- **Dependencies**: `cpu_count`, `runs_on_true_iff`
- **Notes**: ⚠️ Same `apply ... in` name clash issue as `cpu_count_zero_iff_not_executed`. Use `destruct (proj1 (IH sched j t) Hpos) as [c' [Hlt' Hrun']]` with fresh names.
- **Date**: 2026-04-06

---

### `cpu_count_le_1`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma cpu_count_le_1 : forall m sched j t,
      no_duplication m sched ->
      cpu_count sched j t m <= 1.
  ```
- **Proof Strategy**: Induction on `m`. Base: trivial. Step: destruct `runs_on`. If true: apply `runs_on_true_iff` to get `sched t m' = Some j`, then prove `cpu_count m' = 0` via `cpu_count_zero_iff_not_executed` — the key step uses `no_duplication` to derive `c = m'` from any `c < m'` running `j`, giving contradiction with `c < m'`. If false: derive `no_duplication m' sched` from `Hnd` by `lia`, then apply IH.
- **Key Tactics**: `induction m as [| m' IH]`, `runs_on_true_iff`, `cpu_count_zero_iff_not_executed`, `no_duplication`, `apply (Hnd j t c m'); [lia | lia | exact Hrun | exact Erun]`
- **Dependencies**: `cpu_count`, `runs_on_true_iff`, `cpu_count_zero_iff_not_executed`, `no_duplication`
- **Notes**: For the `no_duplication m' sched` assertion, use `apply (Hnd j0 t0 c1 c2); [lia | lia | exact H3 | exact H4]` pattern.
- **Date**: 2026-04-06

---

### `service_le_succ`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma service_le_succ : forall m sched j t,
      service m sched j t <= service m sched j (S t).
  ```
- **Proof Strategy**: `rewrite service_step; lia`.
- **Key Tactics**: `rewrite service_step`, `lia`
- **Dependencies**: `service_step`
- **Notes**: Used as a stepping stone for `service_monotone`.
- **Date**: 2026-04-06

---

### `service_monotone`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma service_monotone : forall m sched j t1 t2,
      t1 <= t2 ->
      service m sched j t1 <= service m sched j t2.
  ```
- **Proof Strategy**: Induction on `t2`. Base: `t1 = 0` by `lia`. Step: use `Nat.le_succ_r` to case-split `t1 <= t2'` vs `t1 = S t2'`; former: `eapply Nat.le_trans` with IH and `service_le_succ`; latter: `lia`.
- **Key Tactics**: `induction t2 as [| t2' IH]`, `Nat.le_succ_r`, `eapply Nat.le_trans`, `service_le_succ`
- **Dependencies**: `service_le_succ`
- **Notes**: Induction on `t2` (not on the difference) works cleanly.
- **Date**: 2026-04-06

---

### `service_increase_at_most_1`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma service_increase_at_most_1 : forall m sched j t,
      no_duplication m sched ->
      service m sched j (S t) <= service m sched j t + 1.
  ```
- **Proof Strategy**: `rewrite service_step; pose proof (cpu_count_le_1 ...); lia`.
- **Key Tactics**: `rewrite service_step`, `cpu_count_le_1`, `lia`
- **Dependencies**: `service_step`, `cpu_count_le_1`
- **Date**: 2026-04-06

---

### `service_no_increase_if_not_executed`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma service_no_increase_if_not_executed : forall m sched j t,
      (forall c, c < m -> sched t c <> Some j) ->
      service m sched j (S t) = service m sched j t.
  ```
- **Proof Strategy**: `rewrite service_step; apply proj2 cpu_count_zero_iff_not_executed in Hnone; lia`.
- **Key Tactics**: `rewrite service_step`, `proj2 (cpu_count_zero_iff_not_executed ...)`, `lia`
- **Dependencies**: `service_step`, `cpu_count_zero_iff_not_executed`
- **Notes**: `apply (proj2 (...)) in Hnone` is safe here because the hypothesis `Hnone` has type `forall c, ...` and does not create name clashes.
- **Date**: 2026-04-06

---

### `service_increases_iff_executed`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma service_increases_iff_executed : forall m sched j t,
      no_duplication m sched ->
      (service m sched j (S t) = service m sched j t + 1 <->
       exists c, c < m /\ sched t c = Some j).
  ```
- **Proof Strategy**: `rewrite service_step`. Forward: `cpu_count_le_1` gives `cpu_count <= 1`, so `cpu_count = 1`, apply `proj1 cpu_count_pos_iff_executed`. Backward: `proj2 cpu_count_pos_iff_executed` gives `cpu_count > 0`, and `cpu_count_le_1` gives `cpu_count <= 1`, so `cpu_count = 1`, then `lia`.
- **Key Tactics**: `rewrite service_step`, `cpu_count_le_1`, `cpu_count_pos_iff_executed`, `proj1`, `proj2`, `lia`
- **Dependencies**: `service_step`, `cpu_count_le_1`, `cpu_count_pos_iff_executed`
- **Date**: 2026-04-06

---

### `completed_not_ready`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma completed_not_ready : forall jobs m sched j t,
      completed jobs m sched j t -> ~ready jobs m sched j t.
  ```
- **Proof Strategy**: `unfold completed, ready; intros ...; exact (Hnot Hcomp)`.
- **Key Tactics**: `unfold`, `exact`
- **Dependencies**: `completed`, `ready`
- **Date**: 2026-04-06

---

### `completed_monotone`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma completed_monotone : forall jobs m sched j t1 t2,
      t1 <= t2 ->
      completed jobs m sched j t1 ->
      completed jobs m sched j t2.
  ```
- **Proof Strategy**: Unfold `completed`, then `eapply Nat.le_trans` with `Hcomp` and `service_monotone`.
- **Key Tactics**: `unfold completed`, `eapply Nat.le_trans`, `service_monotone`
- **Dependencies**: `service_monotone`
- **Date**: 2026-04-06

---

### `valid_no_run_before_release`, `valid_no_run_after_completion`, `valid_running_implies_ready`
- **Type**: Lemma
- **Statement**: Three similar lemmas extracting conjuncts from `valid_schedule`.
- **Proof Strategy**: `unfold valid_schedule; intros ... [H _] / [_ [H _]] / [_ [_ H]] ...; apply (H j t c); assumption`.
- **Key Tactics**: `unfold valid_schedule`, destruct conjunction, `apply (H j t c)`
- **Dependencies**: `valid_schedule`
- **Notes**: Pattern `apply (H j t c); assumption` works because `valid_schedule` conjuncts have the form `forall j t c, c < m -> sched t c = Some j -> P`.
- **Date**: 2026-04-06

---

## Global Notes

### Rocq 9 Syntax Issues
- **`intro ->`**: NOT supported. Use `intro Heq; subst` instead.
- **`injection H as ->`**: NOT supported. Use `injection H as Heq; subst` instead.
- **`From Stdlib Require Import`**: Required (not `Require Import`) to avoid deprecation warnings.

### Apply-in Name Clash
- When `c` is already in scope as a local variable, `apply (f : A -> forall c, P c) in H` can fail with "Unable to find an instance for variable c".
- **Fix**: Apply on the goal instead: `apply (f H_premise)` or `apply (proj1 (IH ...) H)`.
- **Alternative**: Use fresh names in destruct: `destruct (proj1 (IH ...) H) as [c' ...]`.
