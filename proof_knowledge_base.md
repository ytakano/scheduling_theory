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
- **Statement**: Three lemmas extracting consequences from `valid_schedule`.
- **Proof Strategy**: `valid_schedule` is now a single `forall j t c, c < m -> sched t c = Some j -> ready jobs m sched j t`. Extract via `Hv j t c Hlt Hrun : ready ...`, then unfold `ready`/`pending`/`released` and use `proj1`/`proj2`. `valid_running_implies_ready` is trivially `exact (Hv j t c Hlt Hrun)`.
- **Key Tactics**: `unfold valid_schedule, ready, pending, released`, `proj1`, `proj2`, `exact (Hv j t c Hlt Hrun)`
- **Dependencies**: `valid_schedule`, `ready`, `pending`, `released`
- **Notes**: After 2026-04-06 refactoring, `valid_schedule` is a single `forall` (not a conjunction). The old 3-conjunct form was redundant (3rd followed from first two). Now `valid_running_implies_ready` is a direct application.
- **Date**: 2026-04-06

---

### `service_unfold`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma service_unfold : forall m sched j t,
      service m sched j (S t) = cpu_count sched j t m + service m sched j t.
  ```
- **Proof Strategy**: `simpl; reflexivity` — matches the Fixpoint definition exactly (cpu_count first).
- **Key Tactics**: `simpl`, `reflexivity`
- **Dependencies**: `service`, `cpu_count`
- **Notes**: `service_step` is the commuted form (`service t + cpu_count`). Use `service_unfold` when you want the definitional order; use `service_step` when you want `service t + ...` for `lia`.
- **Date**: 2026-04-06

---

### `cpu_count_nonzero_iff_executed`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma cpu_count_nonzero_iff_executed : forall m sched j t,
      cpu_count sched j t m <> 0 <->
      exists c, c < m /\ sched t c = Some j.
  ```
- **Proof Strategy**: Bridge from `cpu_count_pos_iff_executed` via `lia` in both directions.
- **Key Tactics**: `cpu_count_pos_iff_executed`, `lia`
- **Dependencies**: `cpu_count_pos_iff_executed`
- **Notes**: Companion to `cpu_count_pos_iff_executed`; prefer this when the goal has `<> 0` rather than `0 <`.
- **Date**: 2026-04-06

---

### `cpu_count_0_or_1`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma cpu_count_0_or_1 : forall m sched j t,
      no_duplication m sched ->
      cpu_count sched j t m = 0 \/ cpu_count sched j t m = 1.
  ```
- **Proof Strategy**: `pose proof (cpu_count_le_1 ...)` then `destruct (cpu_count ...)` — `O` gives `left; reflexivity`; `S n` gives `right; lia` (since `S n <= 1` forces `n = 0`).
- **Key Tactics**: `cpu_count_le_1`, `destruct (cpu_count ...)`, `lia`
- **Dependencies**: `cpu_count_le_1`, `no_duplication`
- **Notes**: Stronger than `cpu_count_le_1`; useful when downstream proofs need the disjunction explicitly.
- **Date**: 2026-04-06

---

---

### `generated_job_release`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma generated_job_release :
    forall tasks offset jobs j,
      generated_by_periodic_task tasks offset jobs j ->
      job_release (jobs j) =
        expected_release tasks offset (job_task (jobs j)) (job_index (jobs j)).
  ```
- **Proof Strategy**: `exact (proj1 Hgen)` — `generated_by_periodic_task` is a conjunction whose first component is exactly the goal.
- **Key Tactics**: `proj1`
- **Dependencies**: `generated_by_periodic_task`
- **Notes**: Trivial extraction from the first conjunct.
- **Date**: 2026-04-06

---

### `generated_job_deadline`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma generated_job_deadline :
    forall tasks offset jobs j,
      generated_by_periodic_task tasks offset jobs j ->
      job_abs_deadline (jobs j) =
        job_release (jobs j) + task_relative_deadline (tasks (job_task (jobs j))).
  ```
- **Proof Strategy**: Destruct `Hgen` into `[Hrel [Hdl _]]`. `Hdl` has `expected_abs_deadline` on the RHS — `unfold expected_abs_deadline in Hdl` to expose `expected_release + relative_deadline`. Then `rewrite <- Hrel in Hdl` to replace `expected_release ...` with `job_release (jobs j)`. Result matches goal: `exact Hdl`.
- **Key Tactics**: `destruct Hgen as [Hrel [Hdl _]]`, `unfold expected_abs_deadline in Hdl`, `rewrite <- Hrel in Hdl`, `exact Hdl`
- **Dependencies**: `generated_by_periodic_task`, `expected_abs_deadline`, `expected_release`
- **Notes**: ⚠️ `rewrite Hrel in Hdl` (forward) doesn't help because `Hdl` contains `expected_abs_deadline` not `job_release`. Must unfold `expected_abs_deadline` first, then rewrite `<-` to substitute `expected_release` back to `job_release`.
- **Date**: 2026-04-06

---

### `generated_job_cost_bounded`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma generated_job_cost_bounded :
    forall tasks offset jobs j,
      generated_by_periodic_task tasks offset jobs j ->
      job_cost (jobs j) <= task_cost (tasks (job_task (jobs j))).
  ```
- **Proof Strategy**: `exact (proj2 (proj2 Hgen))` — third conjunct of `generated_by_periodic_task`.
- **Key Tactics**: `proj2`
- **Dependencies**: `generated_by_periodic_task`
- **Notes**: The conjunction structure is `A /\ B /\ C` = `A /\ (B /\ C)`, so cost is `proj2 (proj2 Hgen)`.
- **Date**: 2026-04-06

---

### `generated_implies_valid_job_of_task`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma generated_implies_valid_job_of_task :
    forall tasks offset jobs j,
      generated_by_periodic_task tasks offset jobs j ->
      valid_job_of_task tasks jobs j.
  ```
- **Proof Strategy**: `unfold valid_job_of_task`, then `split` into the two conjuncts. First conjunct: `generated_job_deadline`. Second conjunct: `generated_job_cost_bounded`.
- **Key Tactics**: `unfold valid_job_of_task`, `split`, `exact (generated_job_deadline ...)`, `exact (generated_job_cost_bounded ...)`
- **Dependencies**: `generated_job_deadline`, `generated_job_cost_bounded`, `valid_job_of_task`
- **Notes**: Clean delegation to the already-proven sub-lemmas. This is the key connection between `PeriodicTasks.v` and `Base.v`.
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

---

### `cpu_count_le_m`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma cpu_count_le_m : forall m sched j t,
      cpu_count sched j t m <= m.
  ```
- **Proof Strategy**: induction on m. Base: trivial. Step: `pose proof (IH ...)`, `destruct (runs_on ...)`, `lia`.
- **Key Tactics**: `induction m`, `pose proof`, `destruct (runs_on ...)`, `lia`
- **Dependencies**: `cpu_count`, `runs_on`
- **Notes**: 上界。`no_duplication` なし。`cpu_count_le_1` とは異なり前提不要。
- **Date**: 2026-04-06

---

### `service_le_m_mul_t`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma service_le_m_mul_t : forall m sched j t,
      service m sched j t <= m * t.
  ```
- **Proof Strategy**: induction on t. Base: trivial. Step: `rewrite service_step`, `pose proof (cpu_count_le_m ...)`, `lia`.
- **Key Tactics**: `induction t`, `rewrite service_step`, `pose proof`, `lia`
- **Dependencies**: `service_step`, `cpu_count_le_m`
- **Notes**: not-schedulable の証明（上界による矛盾）に有用。`service_le_m_mul_t 1 sched j 2` → `service ≤ 2`。
- **Date**: 2026-04-06

---

### `readyb_iff`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma readyb_iff : forall jobs m sched j t,
      readyb jobs m sched j t = true <-> ready jobs m sched j t.
  ```
- **Proof Strategy**: Unfold `readyb`, `ready`, `pending`, `released`, `completed`. Rewrite `Bool.andb_true_iff`, `Nat.leb_le`, `Bool.negb_true_iff`. Split: forward uses `Nat.leb_le` + `discriminate`; backward uses `Bool.not_true_iff_false` + `Nat.leb_le`.
- **Key Tactics**: `Bool.andb_true_iff`, `Nat.leb_le`, `Bool.negb_true_iff`, `Bool.not_true_iff_false`, `discriminate`
- **Dependencies**: `readyb`, `ready`, `pending`, `released`, `completed`
- **Notes**: Bridge between bool world (filter) and Prop world (ready). Pattern: `negb (a <=? b) = true` → `Bool.negb_true_iff` gives `a <=? b = false` → `rewrite Nat.leb_le in H; rewrite H in ...; discriminate`.
- **Date**: 2026-04-07

---

### `min_dl_job_none_iff`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma min_dl_job_none_iff : forall jobs l,
      min_dl_job jobs l = None <-> l = [].
  ```
- **Proof Strategy**: Induction on `l`. Base: `tauto`. Step: forward — case analysis on `min_dl_job rest` and comparison; always `Some _`, so `None = Some _` is `discriminate`. Backward: `discriminate` (j :: rest ≠ []).
- **Key Tactics**: `induction l`, `destruct (min_dl_job ...)`, `destruct (...<=?...); discriminate`, `discriminate`
- **Dependencies**: `min_dl_job`
- **Date**: 2026-04-07

---

### `min_dl_job_in`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma min_dl_job_in : forall jobs l j,
      min_dl_job jobs l = Some j -> In j l.
  ```
- **Proof Strategy**: Induction on `l`. Step: destruct on `min_dl_job rest` (eqn:Erest) and comparison (eqn:Ecmp). True branch: `injection Hsome; subst; left; reflexivity`. False branch: `injection Hsome; subst; right; apply IH; reflexivity`.
- **Key Tactics**: `induction l`, `destruct ... eqn:`, `injection Hsome as Heq`, `subst`, `apply IH; reflexivity`
- **Dependencies**: `min_dl_job`
- **Notes**: ⚠️ **Critical**: After `destruct (min_dl_job jobs rest) as [j'|] eqn:Erest`, the IH changes from `forall j, min_dl_job jobs rest = Some j -> In j rest` to `forall j, Some j' = Some j -> In j rest` (because Rocq rewrites the IH with Erest). Therefore, to apply IH, use `apply IH; reflexivity` (not `exact Erest`). Same issue applies to `min_dl_job_min`.
- **Date**: 2026-04-07

---

### `min_dl_job_min`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma min_dl_job_min : forall jobs l j,
      min_dl_job jobs l = Some j ->
      forall j', In j' l ->
      job_abs_deadline (jobs j) <= job_abs_deadline (jobs j').
  ```
- **Proof Strategy**: Induction on `l`. Step: destruct on `min_dl_job rest` (eqn:Erest) and comparison (eqn:Ecmp). True case (`j = j0`): `Nat.leb_le`; for `j' ∈ rest` use `pose proof (IH jmin eq_refl j' Hin'); lia`. False case (`j = jmin_orig`): `Bool.not_true_iff_false` + `Nat.leb_le`; for `j' = j0` use `lia`; for `j' ∈ rest` use `apply IH; reflexivity; exact Hin'`. None case: `min_dl_job_none_iff` shows rest is empty → contradiction.
- **Key Tactics**: `Nat.leb_le`, `Bool.not_true_iff_false`, `pose proof (IH jmin eq_refl j' Hin')`, `apply IH; reflexivity`, `min_dl_job_none_iff`, `lia`
- **Dependencies**: `min_dl_job`, `min_dl_job_none_iff`
- **Notes**: ⚠️ Same IH rewriting issue as `min_dl_job_in`. Use `eq_refl` (not the `eqn` hypothesis) when applying IH.
- **Date**: 2026-04-07

---

### `choose_edf_ready`
- **Type**: Theorem
- **Statement**:
  ```coq
  Theorem choose_edf_ready : forall jobs m sched t candidates j,
      choose_edf jobs m sched t candidates = Some j ->
      ready jobs m sched j t.
  ```
- **Proof Strategy**: Unfold `choose_edf`. Chain: `min_dl_job_in` → `filter_In` → `readyb_iff`.
- **Key Tactics**: `unfold choose_edf`, `min_dl_job_in`, `filter_In`, `readyb_iff`
- **Dependencies**: `choose_edf`, `min_dl_job_in`, `filter_In`, `readyb_iff`
- **Date**: 2026-04-07

---

### `choose_edf_min_deadline`
- **Type**: Theorem
- **Statement**:
  ```coq
  Theorem choose_edf_min_deadline : forall jobs m sched t candidates j,
      choose_edf jobs m sched t candidates = Some j ->
      forall j', In j' candidates ->
      ready jobs m sched j' t ->
      job_abs_deadline (jobs j) <= job_abs_deadline (jobs j').
  ```
- **Proof Strategy**: Unfold `choose_edf`. Apply `min_dl_job_min`. Show `j'` is in the filtered list via `filter_In` + `readyb_iff`.
- **Key Tactics**: `unfold choose_edf`, `min_dl_job_min`, `filter_In`, `readyb_iff`
- **Dependencies**: `choose_edf`, `min_dl_job_min`, `filter_In`, `readyb_iff`
- **Date**: 2026-04-07

---

### `choose_edf_some_if_exists`
- **Type**: Theorem
- **Statement**:
  ```coq
  Theorem choose_edf_some_if_exists : forall jobs m sched t candidates,
      (exists j, In j candidates /\ ready jobs m sched j t) ->
      exists j', choose_edf jobs m sched t candidates = Some j'.
  ```
- **Proof Strategy**: Show the filtered list is non-empty via `filter_In` + `readyb_iff`. Then destruct on `min_dl_job` result: `Some j'` gives witness; `None` contradicts `min_dl_job_none_iff`.
- **Key Tactics**: `filter_In`, `readyb_iff`, `destruct ... eqn:Hmin`, `min_dl_job_none_iff`, `contradiction`
- **Dependencies**: `choose_edf`, `filter_In`, `readyb_iff`, `min_dl_job_none_iff`
- **Date**: 2026-04-07

---

### `choose_edf_none_if_no_ready`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma choose_edf_none_if_no_ready : forall jobs m sched t candidates,
      (forall j, In j candidates -> ~ready jobs m sched j t) ->
      choose_edf jobs m sched t candidates = None.
  ```
- **Proof Strategy**: Unfold `choose_edf`. Apply `min_dl_job_none_iff` — it suffices to show the filtered list is `[]`. Induction on `candidates`: base is trivial; step destructs `readyb` on the head. If `readyb = true`, derive contradiction via `readyb_iff` and the hypothesis applied to `or_introl eq_refl`. If `readyb = false`, apply IH with `right`.
- **Key Tactics**: `unfold choose_edf`, `apply min_dl_job_none_iff`, `induction candidates`, `destruct (readyb ...) eqn:Erb`, `readyb_iff`, `or_introl eq_refl`
- **Dependencies**: `min_dl_job_none_iff`, `readyb_iff`
- **Notes**: No `filter_nil` stdlib lemma exists with exactly the right form — prove filter-yields-nil by inline induction on `candidates`. This is the opposite direction of `choose_edf_some_if_exists`.
- **Date**: 2026-04-07

---

### `choose_edf_complete`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma choose_edf_complete : forall jobs m sched t candidates,
      NoDup candidates ->
      (forall j, ready jobs m sched j t <-> In j candidates) ->
      (exists j, ready jobs m sched j t) ->
      exists j', choose_edf jobs m sched t candidates = Some j'.
  ```
- **Proof Strategy**: Trivial corollary of `choose_edf_some_if_exists`. Use the `<->` hypothesis to convert `ready ... j` to `In j candidates`. `NoDup` is in the precondition for interface uniformity but unused in this proof.
- **Key Tactics**: `apply choose_edf_some_if_exists`, `apply Href`
- **Dependencies**: `choose_edf_some_if_exists`
- **Date**: 2026-04-07

---

### `choose_edf_optimal`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma choose_edf_optimal : forall jobs m sched t candidates j,
      NoDup candidates ->
      (forall j', ready jobs m sched j' t <-> In j' candidates) ->
      choose_edf jobs m sched t candidates = Some j ->
      forall j', ready jobs m sched j' t ->
      job_abs_deadline (jobs j) <= job_abs_deadline (jobs j').
  ```
- **Proof Strategy**: Trivial corollary of `choose_edf_min_deadline`. Use `<->` to convert `ready ... j'` to `In j' candidates`. `NoDup` unused but included for interface uniformity.
- **Key Tactics**: `apply choose_edf_min_deadline`, `apply Href`
- **Dependencies**: `choose_edf_min_deadline`
- **Date**: 2026-04-07

---

### `choose_edf_unique_min`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma choose_edf_unique_min : forall jobs m sched t candidates j,
      In j candidates ->
      ready jobs m sched j t ->
      (forall j', In j' candidates -> ready jobs m sched j' t ->
                  j' <> j ->
                  job_abs_deadline (jobs j) < job_abs_deadline (jobs j')) ->
      choose_edf jobs m sched t candidates = Some j.
  ```
- **Proof Strategy**: Get witness `j'` from `choose_edf_some_if_exists`. Prove `j'` is ready (`choose_edf_ready`) and in candidates (`min_dl_job_in` + `filter_In`). Get `deadline(j') <= deadline(j)` from `choose_edf_min_deadline`. Case-split via `Nat.eq_dec j' j`. If `j' = j`: rewrite and done. If `j' ≠ j`: strict hypothesis gives `deadline(j) < deadline(j')`, contradiction with `<=` via `lia`.
- **Key Tactics**: `choose_edf_some_if_exists`, `choose_edf_ready`, `min_dl_job_in`, `filter_In`, `choose_edf_min_deadline`, `Nat.eq_dec`, `lia`
- **Dependencies**: `choose_edf_some_if_exists`, `choose_edf_ready`, `choose_edf_min_deadline`, `min_dl_job_in`, `filter_In`
- **Notes**: `Nat.eq_dec` available because `JobId = nat`. The strict inequality `<` in the hypothesis plus `<=` from `choose_edf_min_deadline` yields contradiction via `lia`.
- **Date**: 2026-04-07

---

### `edf_scheduler_spec`
- **Type**: Definition (Record instantiation)
- **Statement**:
  ```coq
  Definition edf_scheduler_spec : UniSchedulerSpec :=
    mkUniSchedulerSpec
      choose_edf
      choose_edf_ready
      choose_edf_min_deadline
      choose_edf_some_if_exists
      choose_edf_none_if_no_ready.
  ```
- **Proof Strategy**: Definitional — no `Proof`/`Qed` needed. Rocq verifies types match record fields automatically.
- **Key Tactics**: N/A (definitional)
- **Dependencies**: `UniSchedulerInterface`, `choose_edf`, all 4 spec lemmas
- **Notes**: `UniSchedulerSpec` is defined in `UniSchedulerInterface.v` as a `Record`. EDF imports it via `Require Import UniSchedulerInterface`. `choose_edf_unique_min` is intentionally excluded from the record — its strict-inequality hypothesis is EDF-specific and not universal.
- **Date**: 2026-04-07
