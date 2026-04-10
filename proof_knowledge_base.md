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
- **Proof Strategy**: `valid_schedule` is now a single `forall j t c, c < m -> sched t c = Some j -> ready jobs m sched j t`. Extract via `Hv j t c Hlt Hrun : ready ...`, then unfold `ready`/`waiting`/`released` and use `proj1`/`proj2`. `valid_running_implies_ready` is trivially `exact (Hv j t c Hlt Hrun)`.
- **Key Tactics**: `unfold valid_schedule, ready, waiting, released`, `proj1`, `proj2`, `exact (Hv j t c Hlt Hrun)`
- **Dependencies**: `valid_schedule`, `ready`, `waiting`, `released`
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
- **Notes**: not-feasible の証明（上界による矛盾）に有用。`service_le_m_mul_t 1 sched j 2` → `service ≤ 2`。
- **Date**: 2026-04-06

---

### `readyb_iff`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma readyb_iff : forall jobs m sched j t,
      readyb jobs m sched j t = true <-> ready jobs m sched j t.
  ```
- **Proof Strategy**: After `ready = runnable AND NOT running` refactor, `readyb` has 3 conjuncts: `released`, `NOT completed`, `cpu_count = 0`. Unfold all definitions, rewrite `Bool.andb_true_iff` (twice), `Nat.leb_le`, `Bool.negb_true_iff`, `Nat.eqb_eq`. Forward: for NOT-running, use `cpu_count_zero_iff_not_executed` to derive contradiction from the witness in `running`. Backward: for `cpu_count = 0`, use `proj2 (cpu_count_zero_iff_not_executed)` driven by `~running`.
- **Key Tactics**: `Bool.andb_true_iff` (applied twice), `Nat.leb_le`, `Bool.negb_true_iff`, `Nat.eqb_eq`, `cpu_count_zero_iff_not_executed`, `proj1`, `proj2`, `discriminate`
- **Dependencies**: `readyb`, `ready`, `runnable`, `running`, `released`, `completed`, `cpu_count_zero_iff_not_executed`
- **Notes**: ⚠️ `intro [c [Hlt Hc]]` fails with syntax error for negated existential (`~exists c, ...`); use `intros [c [Hlt Hc]]` instead. Bridge pattern: `running sched m j t = exists c, c < m /\ sched t c = Some j` ↔ `0 < cpu_count sched j t m` via `cpu_count_pos_iff_executed`; `cpu_count = 0` ↔ `forall c, c < m -> sched t c <> Some j` via `cpu_count_zero_iff_not_executed`.
- **Date**: 2026-04-08

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
- **Notes**: `UniSchedulerSpec` is defined in `UniSchedulerInterface.v` as a `Record`. EDF imports it via `Require Import UniSchedulerInterface`. `choose_edf_unique_min` is intentionally excluded from the record — its strict-inequality hypothesis is EDF-specific and not universal. Updated 2026-04-07: extended to 6-field record by adding `choose_in_candidates` (Spec 5), proved by `choose_edf_in_candidates` via `min_dl_job_in` + `filter_In` proj1.
- **Date**: 2026-04-07

---

### `choose_in_candidates` (UniSchedulerSpec field 5)
- **Type**: Spec field (interface extension)
- **Statement**:
  ```coq
  choose_in_candidates :
    forall jobs m sched t candidates j,
      choose jobs m sched t candidates = Some j ->
      In j candidates
  ```
- **Proof Strategy**: For EDF: `unfold choose_edf`, apply `min_dl_job_in`, then `filter_In` proj1.
- **Key Tactics**: `min_dl_job_in`, `filter_In`, `proj1`
- **Dependencies**: `min_dl_job_in`, `filter_In`
- **Notes**: Added to `UniSchedulerSpec` record as 5th field (after `choose_none_if_no_ready`). Previously missing from the interface — without it, `choose_some_implies_in_candidates` cannot be stated as a general lemma.
- **Date**: 2026-04-07

---

### `candidates_sound` / `candidates_complete` (UniSchedulerLemmas.v)
- **Type**: Definition (coverage predicates)
- **Statement**:
  ```coq
  Definition candidates_sound jobs m sched t candidates :=
    forall j, In j candidates -> ready jobs m sched j t.
  Definition candidates_complete jobs m sched t candidates :=
    forall j, ready jobs m sched j t -> In j candidates.
  ```
- **Proof Strategy**: Pure definitions — no proof needed.
- **Key Tactics**: N/A
- **Dependencies**: `ready`
- **Notes**: Defined outside the Section in `UniSchedulerLemmas.v` so they can be used as explicit parameters in coverage lemmas F3/F4. Bridge to `Partitioned.v`.
- **Date**: 2026-04-07

---

### `choose_none_implies_each_candidate_unreleased_or_completed` (E3)
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma choose_none_implies_each_candidate_unreleased_or_completed :
      spec.(choose) jobs m sched t candidates = None ->
      forall j, In j candidates ->
        ~released jobs j t \/ completed jobs m sched j t.
  ```
- **Proof Strategy**: Use `choose_none_implies_no_ready` to get `~ready j t`. Unfold `ready`/`waiting`. Use `classic (released j t)` from Classical: if released, use NNPP to derive completed; if not released, left branch directly.
- **Key Tactics**: `classic`, `NNPP`, `unfold ready, waiting`
- **Dependencies**: `choose_none_implies_no_ready`, `Classical`
- **Notes**: Requires `From Stdlib Require Import Classical.` — `~(A /\ ~B) -> ~A \/ B` is not constructively derivable. Use `destruct (classic (released ...))` pattern.
- **Date**: 2026-04-07

---

### `ready_implies_released` / `ready_implies_not_completed` (Schedule.v)
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma ready_implies_released : forall jobs m sched j t,
      ready jobs m sched j t -> released jobs j t.
  Lemma ready_implies_not_completed : forall jobs m sched j t,
      ready jobs m sched j t -> ~completed jobs m sched j t.
  ```
- **Proof Strategy**: `unfold ready, waiting` then `proj1`/`proj2`.
- **Key Tactics**: `unfold ready, waiting`, `proj1`, `proj2`
- **Dependencies**: `ready`, `waiting`, `released`, `completed`
- **Notes**: Simple decomposition lemmas. These were derivable from `choose_some_implies_runnable` in the lemmas section, but as standalone Schedule.v lemmas they are useful for other proofs.
- **Date**: 2026-04-07

---

### `waiting_not_eligible`, `waiting_not_ready`, `ready_implies_runnable`, `completed_not_runnable`, `runnable_after_release`, `ready_after_release`, `scheduled_implies_running` (Schedule.v Lv.0-4)
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma waiting_not_eligible : forall jobs m sched j t,
      waiting jobs j t -> ~eligible jobs m sched j t.
  Lemma waiting_not_ready : forall jobs m sched j t,
      waiting jobs j t -> ~ready jobs m sched j t.
  Lemma ready_implies_runnable : forall jobs m sched j t,
      ready jobs m sched j t -> runnable jobs m sched j t.
  Lemma completed_not_runnable : forall jobs m sched j t,
      completed jobs m sched j t -> ~runnable jobs m sched j t.
  Lemma runnable_after_release : forall jobs m sched j t,
      runnable jobs m sched j t -> job_release (jobs j) <= t.
  Lemma ready_after_release : forall jobs m sched j t,
      ready jobs m sched j t -> job_release (jobs j) <= t.
  Lemma scheduled_implies_running : forall sched j t c,
      sched t c = Some j -> running sched j t.
  ```
- **Proof Strategy**: All straightforward. `waiting_not_eligible`: unfold waiting/eligible/released, lia. `waiting_not_ready`: apply waiting_not_eligible + unfold ready. `ready_implies_runnable`: unfold ready, trivial (ready = runnable). `completed_not_runnable`: unfold, exact contradiction. `runnable_after_release`: unfold runnable/released, proj1. `ready_after_release`: via ready_implies_runnable + runnable_after_release. `scheduled_implies_running`: unfold running, exists c.
- **Key Tactics**: `unfold waiting, runnable, released`, `lia`, `proj1`, `exists c`
- **Dependencies**: `waiting` (Base.v), `runnable`, `ready`, `running`, `completed`, `released`
- **Notes**: `ready_implies_runnable` requires `intros jobs m sched j t H` not `intros _ _ _ _ _ H` (Rocq 9 rejects wildcard when variable is used in conclusion). `ready_after_release` needs explicit `apply (runnable_after_release jobs m sched j t)` — implicit arguments not inferred for `apply runnable_after_release`.
- **Date**: 2026-04-08

---

### State refactoring: waiting/runnable/running/ready (2026-04-08)
- **Type**: Definition (refactoring record)
- **Statement**: Added to Base.v and Schedule.v as part of state vocabulary expansion.
  ```coq
  (* Base.v — schedule-independent *)
  Definition waiting (jobs : JobId -> Job) (j : JobId) (t : Time) : Prop :=
    t < job_release (jobs j).

  (* Schedule.v *)
  Definition running (sched : Schedule) (j : JobId) (t : Time) : Prop :=
    exists c : CPU, sched t c = Some j.

  Definition runnable (jobs : JobId -> Job) (m : nat) (sched : Schedule)
      (j : JobId) (t : Time) : Prop :=
    released jobs j t /\ ~completed jobs m sched j t.

  Definition ready ... := runnable ...   (* currently equal *)
  ```
- **Proof Strategy**: N/A (refactoring, not a theorem)
- **Key Tactics**: N/A
- **Dependencies**: N/A
- **Notes**: The old `Schedule.v::pending` (= released AND NOT completed) was renamed to `runnable`. New `Base.v::waiting` = pre-release (t < job_release). `ready = runnable` (unchanged semantics). `ready = runnable AND NOT running` was considered but REJECTED because `valid_schedule: sched t c = Some j → ready j t` would be contradictory (sched t c = Some j implies running, which would require NOT running). Cascading renames: `valid_running_implies_pending` → `valid_running_implies_runnable`; `choose_some_implies_pending` → `choose_some_implies_runnable`; all `unfold ..., pending` in Schedule.v proofs → `unfold ..., runnable`.
- **Date**: 2026-04-08

---

### Interface refactoring: `UniSchedulerSpec` → `GenericSchedulerDecisionSpec` + `EDFSchedulerSpec` (2026-04-09)
- **Type**: Definition (refactoring record)
- **Statement**:
  ```coq
  (* UniSchedulerInterface.v *)
  Record GenericSchedulerDecisionSpec : Type := mkGenericSchedulerDecisionSpec {
    choose_g : (JobId -> Job) -> nat -> Schedule -> Time -> list JobId -> option JobId;
    choose_g_ready : ...;
    choose_g_some_if_ready : ...;
    choose_g_none_if_no_ready : ...;
    choose_g_in_candidates : ...;
  }.

  (* EDF.v *)
  Record EDFSchedulerSpec : Type := mkEDFSchedulerSpec {
    edf_generic :> GenericSchedulerDecisionSpec;   (* coercion *)
    edf_choose_min_deadline : ...;
  }.
  ```
- **Proof Strategy**: N/A (refactoring)
- **Key Tactics**: N/A
- **Dependencies**: N/A
- **Notes**: `UniSchedulerSpec` was removed and replaced by `GenericSchedulerDecisionSpec` (generic) in `UniSchedulerInterface.v`. `EDFSchedulerSpec` (EDF-specific) lives in `EDF.v`. The `:>` coercion on `edf_generic` lets `EDFSchedulerSpec` be passed wherever `GenericSchedulerDecisionSpec` is expected. `UniSchedulerLemmas.v` was updated to use `GenericSchedulerDecisionSpec`; EDF-specific lemmas A5/C1/C2 were moved to `EDFSchedulerLemmasSection` in `EDF.v`. Section name in `Partitioned.v` is `PartitionedSection` (not `Partitioned`) to avoid masking warning.
- **Date**: 2026-04-09

---

### `cpu_count_assigned_only` (Partitioned.v)
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma cpu_count_assigned_only :
    forall sched,
      respects_assignment sched ->
      forall j t,
        cpu_count sched j t m = if runs_on sched j t (assign j) then 1 else 0.
  ```
- **Proof Strategy**: Case split on `runs_on sched j t (assign j)`.
  - `true`: lower bound via `cpu_count_pos_iff_executed` (witness = assign j, use `valid_assignment j`); upper bound via `cpu_count_le_1` + `partitioned_implies_sequential`. Conclude by `lia`.
  - `false`: `cpu_count_zero_iff_not_executed`; any c < m with `sched t c = Some j` gives `assign j = c` via `respects_assignment`; then `runs_on_false_iff` + `rewrite Hassign` on `Erun : runs_on ... = false` to derive contradiction.
- **Key Tactics**: `destruct (runs_on ...) eqn:Erun`, `cpu_count_pos_iff_executed`, `cpu_count_le_1`, `partitioned_implies_sequential`, `cpu_count_zero_iff_not_executed`, `runs_on_true_iff`, `runs_on_false_iff`, `lia`
- **Dependencies**: `cpu_count_pos_iff_executed`, `cpu_count_le_1`, `cpu_count_zero_iff_not_executed`, `sequential_jobs`, `runs_on_true_iff`, `runs_on_false_iff`
- **Notes**: ⚠️ Do NOT try `induction m` inside a Section where `m` is a `Variable` — induction on Section variables is not possible in Rocq. Use existing lemmas (`cpu_count_le_1`, `cpu_count_pos_iff_executed`) for the case split instead. ⚠️ `Nat.lt_succ_of_lt` does not exist in Rocq stdlib; use `lia` for `c < m' → c < S m'` steps.
- **Date**: 2026-04-09

---

### `service_decomposition` (Partitioned.v, Theorem 3)
- **Type**: Theorem
- **Statement**:
  ```coq
  Theorem service_decomposition :
    forall sched,
      respects_assignment sched ->
      forall j t,
        service_job m sched j t =
          service_job 1 (cpu_schedule sched (assign j)) j t.
  ```
- **Proof Strategy**: Induction on `t`. Base: trivial. Step: `simpl; rewrite IH; f_equal; apply service_decomposition_step`. The bridge `service_decomposition_step` uses `runs_on_cpu_schedule` to show `cpu_count sched j t m = cpu_count (cpu_schedule sched (assign j)) j t 1`.
- **Key Tactics**: `induction t`, `simpl`, `f_equal`, `service_decomposition_step`
- **Dependencies**: `cpu_count_assigned_only`, `runs_on_cpu_schedule`
- **Notes**: `runs_on_cpu_schedule` (auxiliary): `runs_on (cpu_schedule sched c) j t 0 = runs_on sched j t c` — proved by `unfold runs_on, cpu_schedule; simpl; reflexivity`. Needed because `rewrite Nat.eqb_refl` alone fails after `simpl` (the `0 =? 0` pattern may already be reduced or not directly visible).
- **Date**: 2026-04-09

---

### `local_to_global_validity` (Partitioned.v, Theorem 2)
- **Type**: Theorem
- **Statement**:
  ```coq
  Theorem local_to_global_validity :
    forall jobs sched xs,
      valid_partitioned_schedule jobs sched xs ->
      (forall c, c < m -> valid_schedule jobs 1 (cpu_schedule sched c)) ->
      valid_schedule jobs m sched.
  ```
- **Proof Strategy**: Unfold `valid_schedule`. Given `sched t c = Some j`:
  1. `cpu_schedule sched c t 0 = Some j` via `unfold cpu_schedule; rewrite Nat.eqb_refl`.
  2. Per-CPU validity gives `eligible jobs 1 (cpu_schedule sched c) j t`.
  3. Release: direct from step 2.
  4. Non-completion: `rewrite completed_iff_on_assigned_cpu`, then `pose proof (Hresp j t c Hlt Hrun) as Hassign`, then `rewrite Hassign` to convert `assign j` to `c` in the goal.
- **Key Tactics**: `unfold valid_schedule, eligible`, `Nat.eqb_refl`, `completed_iff_on_assigned_cpu`, `rewrite Hassign`
- **Dependencies**: `completed_iff_on_assigned_cpu`, `respects_assignment`, `cpu_schedule`
- **Notes**: ⚠️ After `rewrite completed_iff_on_assigned_cpu`, the goal contains `assign j` (not `c`). Use `rewrite Hassign` (where `Hassign : assign j = c`) to convert — NOT `rewrite <- Hassign`. Using the wrong direction gives "Found no subterm matching c".
- **Date**: 2026-04-09

---

### `readyb` / `readyb_iff` (moved to Schedule.v)
- **Type**: Definition + Lemma
- **Statement**:
  ```coq
  Definition readyb (jobs : JobId -> Job) (m : nat) (sched : Schedule)
                     (j : JobId) (t : Time) : bool :=
    (job_release (jobs j) <=? t) &&
    negb (job_cost (jobs j) <=? service_job m sched j t) &&
    (cpu_count m sched j t =? 0).

  Lemma readyb_iff : forall jobs m sched j t,
      readyb jobs m sched j t = true <-> ready jobs m sched j t.
  ```
- **Proof Strategy**: Unfold all definitions, rewrite with `Bool.andb_true_iff`, `Nat.leb_le`, `Bool.negb_true_iff`, `Nat.eqb_eq`. Use `cpu_count_zero_iff_not_executed` to bridge `cpu_count = 0` and `~running`.
- **Key Tactics**: `Bool.andb_true_iff`, `Bool.negb_true_iff`, `Nat.eqb_eq`, `Nat.leb_le`, `cpu_count_zero_iff_not_executed`, `Bool.not_true_iff_false`
- **Dependencies**: `cpu_count_zero_iff_not_executed`
- **Notes**: Placed in `Schedule.v` AFTER `cpu_count_zero_iff_not_executed` (not near `ready` definition) because the proof depends on it. Previously in `EDF.v` only — now shared by all policies.
- **Date**: 2026-04-09

---

### `choose_fifo` (FIFO.v)
- **Type**: Definition
- **Statement**:
  ```coq
  Fixpoint choose_fifo (jobs : JobId -> Job) (m : nat) (sched : Schedule)
                        (t : Time) (candidates : list JobId) : option JobId :=
    match candidates with
    | []       => None
    | j :: rest =>
      if readyb jobs m sched j t then Some j
      else choose_fifo jobs m sched t rest
    end.
  ```
- **Proof Strategy**: Linear scan — return first `readyb`-true job.
- **Key Tactics**: Fixpoint, `readyb`
- **Dependencies**: `readyb`
- **Notes**: All 4 GenericSchedulerDecisionSpec lemmas proved by `induction candidates; simpl; destruct (readyb ...) eqn:Erb`.
- **Date**: 2026-04-09

---

### `choose_fifo_some_if_exists`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma choose_fifo_some_if_exists : forall jobs m sched t candidates,
      (exists j, In j candidates /\ ready jobs m sched j t) ->
      exists j', choose_fifo jobs m sched t candidates = Some j'.
  ```
- **Proof Strategy**: Induction on `candidates` BEFORE destructuring the existential. If done after, the IH type has `j` fixed and `apply IHc` + `exists j` fails with "Not an inductive definition".
- **Key Tactics**: `intros jobs m sched t. induction candidates as [| h rest IHc].`, then `intros [j [Hin Hready]]`
- **Dependencies**: `readyb_iff`, `Bool.not_true_iff_false`
- **Notes**: ⚠️ CRITICAL ORDER: Do `induction candidates` before `intros [j [Hin Hready]]`. If you intro the existential first, `IHc` gets `j` fixed and the later `apply IHc. exists j. split.` fails with "Not an inductive definition" because the goal after `apply IHc` is already `In j rest`, not an existential.
- **Date**: 2026-04-09

---

### `choose_fifo_first_ready`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma choose_fifo_first_ready : forall jobs m sched t candidates j,
      choose_fifo jobs m sched t candidates = Some j ->
      exists prefix suffix,
        candidates = prefix ++ j :: suffix /\
        forall j', In j' prefix -> ~ready jobs m sched j' t.
  ```
- **Proof Strategy**: Induction on candidates. Base: head is ready → `prefix = []`. Step: head not ready → prepend head to prefix of recursive call.
- **Key Tactics**: `induction candidates`, `destruct (readyb ...) eqn:Erb`, `injection H as Heq; subst`, `exists [], rest` / `exists (j0 :: prefix), suffix`, `Bool.not_true_iff_false`, `readyb_iff`
- **Dependencies**: `readyb_iff`, `Bool.not_true_iff_false`
- **Notes**: The prefix witness is built incrementally: start with `[]` when head is chosen, extend with `j0 :: prefix` in recursive case.
- **Date**: 2026-04-09

---

### `missed_deadline_iff_on_assigned_cpu`
- **Type**: Corollary
- **Statement**:
  ```coq
  Corollary missed_deadline_iff_on_assigned_cpu :
    forall jobs sched j,
      respects_assignment sched ->
      missed_deadline jobs m sched j <->
        missed_deadline jobs 1 (cpu_schedule sched (assign j)) j.
  ```
- **Proof Strategy**: Unfold `missed_deadline` to `~completed ...`, then instantiate `completed_iff_on_assigned_cpu` at `t := job_abs_deadline (jobs j)` via `pose proof`, then `tauto`.
- **Key Tactics**: `unfold missed_deadline`, `pose proof (completed_iff_on_assigned_cpu ... j (job_abs_deadline (jobs j)))`, `tauto`
- **Dependencies**: `completed_iff_on_assigned_cpu`, `missed_deadline`
- **Notes**: Do not try `rewrite completed_iff_on_assigned_cpu` directly — the `by` clause doesn't pattern-match well inside negation. Use `pose proof` + `tauto` instead.
- **Date**: 2026-04-09

---

### `local_feasible_implies_global_feasible_schedule`
- **Type**: Theorem
- **Statement**:
  ```coq
  Theorem local_feasible_implies_global_feasible_schedule :
    forall jobs sched,
      respects_assignment sched ->
      (forall c, c < m -> feasible_schedule jobs 1 (cpu_schedule sched c)) ->
      feasible_schedule jobs m sched.
  ```
- **Proof Strategy**: Unfold `feasible_schedule`. For any `j`, use `valid_assignment j` to get `assign j < m`, apply per-CPU hypothesis at `assign j`, unfold local `feasible_schedule`, extract `~missed_deadline` for `j`, then use `rewrite missed_deadline_iff_on_assigned_cpu by exact Hresp` to convert global goal to local.
- **Key Tactics**: `unfold feasible_schedule`, `pose proof (valid_assignment j)`, `rewrite missed_deadline_iff_on_assigned_cpu by exact Hresp`
- **Dependencies**: `missed_deadline_iff_on_assigned_cpu`, `valid_assignment`, `feasible_schedule`
- **Notes**: The `rewrite ... by` pattern works here because the goal is `~missed_deadline jobs m sched j` (not nested in another connective that would confuse rewriting).
- **Date**: 2026-04-09

---

### `local_valid_feasible_implies_global`
- **Type**: Corollary
- **Statement**:
  ```coq
  Corollary local_valid_feasible_implies_global :
    forall jobs sched xs,
      valid_partitioned_schedule jobs sched xs ->
      (forall c, c < m ->
        valid_schedule jobs 1 (cpu_schedule sched c) /\
        feasible_schedule jobs 1 (cpu_schedule sched c)) ->
      valid_schedule jobs m sched /\ feasible_schedule jobs m sched.
  ```
- **Proof Strategy**: Destruct `valid_partitioned_schedule` into `Hpart` and `Hresp`. Split goal. For validity: apply `local_to_global_validity with xs`, rebuild `valid_partitioned_schedule` via `conj`. For feasibility: apply `local_feasible_implies_global_feasible_schedule` with `Hresp` and projection of the local hypothesis.
- **Key Tactics**: `destruct Hvps as [Hpart Hresp]`, `split`, `apply local_to_global_validity with xs`, `exact (conj Hpart Hresp)`, `proj1`, `proj2`
- **Dependencies**: `local_to_global_validity`, `local_feasible_implies_global_feasible_schedule`, `valid_partitioned_schedule`
- **Notes**: Rebuild `valid_partitioned_schedule` from components via `exact (conj Hpart Hresp)` — `local_to_global_validity` expects it as a bundled argument.
- **Date**: 2026-04-09

---

### `partitioned_schedule_implies_respects_assignment` (Phase 3 refactor)
- **Type**: Theorem
- **Statement**:
  ```coq
  Theorem partitioned_schedule_implies_respects_assignment :
    forall jobs sched xs,
      partitioned_schedule jobs sched xs ->
      respects_assignment sched.
  ```
- **Proof Strategy**: Given `sched t c = Some j`, use `partitioned_schedule` to get `sched t c = dispatch ... (candidates_for c xs)`, so `dispatch ... = Some j`. Apply `dispatch_in_candidates` to get `j ∈ candidates_for c xs`, then `candidates_for_assign_sound` gives `assign j = c`.
- **Key Tactics**: `pose proof (Hpart t c Hlt)`, `rewrite Hrun in Heq`, `symmetry in Heq`, `eapply spec.(dispatch_in_candidates)`
- **Dependencies**: `partitioned_schedule`, `candidates_for_assign_sound`, `dispatch_in_candidates`
- **Notes**: After Phase 3 refactor, `respects_assignment` is no longer an axiom/conjunct — it is a derived theorem. `valid_partitioned_schedule` is now just `partitioned_schedule`.
- **Date**: 2026-04-09

---

### `partitioned_schedule_implies_valid_schedule` (Phase 3 refactor, replaces `local_to_global_validity`)
- **Type**: Theorem
- **Statement**:
  ```coq
  Theorem partitioned_schedule_implies_valid_schedule :
    forall jobs sched xs,
      partitioned_schedule jobs sched xs ->
      valid_schedule jobs m sched.
  ```
- **Proof Strategy**: Given `sched t c = Some j`: (1) derive `Hresp` via `partitioned_schedule_implies_respects_assignment`; (2) from `partitioned_schedule`, extract `dispatch ... = Some j`; (3) `dispatch_ready` gives `ready jobs 1 (cpu_schedule sched c) j t`; (4) unfold `ready` and `eligible` to get `released` and local `~completed`; (5) lift `~completed` globally via `completed_iff_on_assigned_cpu` + `assign j = c` from `Hresp`.
- **Key Tactics**: `symmetry in Heq`, `spec.(dispatch_ready)`, `unfold ready`, `unfold eligible`, `rewrite completed_iff_on_assigned_cpu by exact Hresp`, `rewrite Hassign`
- **Dependencies**: `partitioned_schedule_implies_respects_assignment`, `dispatch_ready`, `completed_iff_on_assigned_cpu`
- **Notes**: Old `local_to_global_validity` required external per-CPU `valid_schedule` hypotheses. This theorem needs only `partitioned_schedule` — validity is derived directly from `dispatch_ready`. ⚠️ Need `symmetry in Heq` after `rewrite Hrun in Heq` because `partitioned_schedule` equality is `sched t c = dispatch ...` not `dispatch ... = sched t c`.
- **Date**: 2026-04-09

---

### `single_cpu_dispatch_eq_cpu0`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma single_cpu_dispatch_eq_cpu0 :
      forall spec candidates_of jobs sched t,
        scheduler_rel (single_cpu_dispatch_schedule spec candidates_of) jobs 1 sched ->
        sched t 0 = spec.(dispatch) jobs 1 sched t (candidates_of jobs 1 sched t).
  ```
- **Proof Strategy**: Destruct the relation to get the `forall t` component, then `exact (proj1 (Hrel t))`.
- **Key Tactics**: `destruct Hrel as [_ Hrel]`, `exact (proj1 (Hrel t))`
- **Dependencies**: `single_cpu_dispatch_schedule`, `scheduler_rel`
- **Notes**: Direct read-out of the first component of the bridge relation.
- **Date**: 2026-04-09

---

### `single_cpu_dispatch_idle_on_other_cpus`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma single_cpu_dispatch_idle_on_other_cpus :
      forall spec candidates_of jobs sched t c,
        scheduler_rel (single_cpu_dispatch_schedule spec candidates_of) jobs 1 sched ->
        0 < c -> sched t c = None.
  ```
- **Proof Strategy**: `destruct Hrel as [_ Hrel]`, then `exact (proj2 (Hrel t) c Hc)`.
- **Key Tactics**: `destruct Hrel as [_ Hrel]`, `proj2 (Hrel t)`
- **Dependencies**: `single_cpu_dispatch_schedule`, `scheduler_rel`
- **Notes**: Direct read-out of the second component of the bridge relation.
- **Date**: 2026-04-09

---

### `local_candidates_spec`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma local_candidates_spec :
    forall c, c < m ->
      CandidateSourceSpec (local_jobset c) (local_candidates_of c).
  ```
- **Proof Strategy**: Use `refine (mkCandidateSourceSpec ...)` with three goals. Soundness: from `In j (local_candidates c)`, extract `In j enumJ` via `filter_In` then apply `enumJ_sound`. Completeness: apply `local_candidates_complete`. Prefix extensionality: `local_candidates_of` is constant, so `reflexivity`.
- **Key Tactics**: `refine (mkCandidateSourceSpec _ _ _)`, `filter_In`, `enumJ_sound`, `local_candidates_complete`, `reflexivity`
- **Dependencies**: `local_candidates_sound`, `local_candidates_complete`, `enumJ_sound` (Section hypothesis)
- **Notes**: ⚠️ Requires `enumJ_sound` hypothesis in the Section (not just `enumJ_complete`). `enumJ_complete` goes `J j → In j enumJ`; soundness needs `In j enumJ → J j` which is `enumJ_sound`.
- **Date**: 2026-04-09

---

### `partitioned_schedule_on_iff_local_rel`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma partitioned_schedule_on_iff_local_rel :
    forall jobs sched,
      partitioned_schedule_on jobs sched <->
      (forall c, c < m ->
        scheduler_rel (single_cpu_dispatch_schedule spec (local_candidates_of c))
          jobs 1 (cpu_schedule sched c)).
  ```
- **Proof Strategy**: Unfold `partitioned_schedule_on`, `scheduler_rel`, `local_candidates_of`, `cpu_schedule`. Forward: give `reflexivity` for `m = 1`, then `simpl` resolves `cpu_schedule sched c t 0 = sched t c` (the `if 0 =? 0` reduces). Other CPUs: destruct `c' =? 0`, use `lia` for the `true` branch, `reflexivity` for `false`. Backward: extract `Heq0` from `proj1 (Hstep t)` and `simpl in Heq0`.
- **Key Tactics**: `unfold`, `split`, `simpl`, `Nat.eqb_eq`, `lia`, `reflexivity`
- **Dependencies**: `partitioned_schedule_on`, `single_cpu_dispatch_schedule`, `cpu_schedule`, `local_candidates_of`
- **Notes**: ⚠️ Do NOT use `rewrite Nat.eqb_refl` — after `simpl`, the `0 =? 0` is already reduced. Using `rewrite Nat.eqb_refl` causes "no subterm matching" error.
- **Date**: 2026-04-09

---

### `local_feasible_on_implies_global_feasible_on`
- **Type**: Theorem
- **Statement**:
  ```coq
  Theorem local_feasible_on_implies_global_feasible_on :
    forall jobs sched,
      respects_assignment sched ->
      (forall c, c < m ->
        feasible_schedule_on (local_jobset c) jobs 1 (cpu_schedule sched c)) ->
      feasible_schedule_on J jobs m sched.
  ```
- **Proof Strategy**: Take `j` and `HJ`. Derive `Hlt : assign j < m` via `valid_assignment`. Apply local feasibility at `assign j`. Rewrite goal with `missed_deadline_iff_on_assigned_cpu` before applying `Hfeas` (to convert global missed_deadline to local). Provide `local_jobset` membership via `split; [exact HJ | reflexivity]`.
- **Key Tactics**: `rewrite missed_deadline_iff_on_assigned_cpu by exact Hresp`, `unfold local_jobset`, `split`
- **Dependencies**: `missed_deadline_iff_on_assigned_cpu`, `valid_assignment`, `local_jobset`
- **Notes**: ⚠️ Must `rewrite missed_deadline_iff_on_assigned_cpu` BEFORE applying `Hfeas` — applying `Hfeas` first gives a local missed_deadline goal that won't unify with the global form.
- **Date**: 2026-04-09

---

### `valid_partitioned_schedule_intro`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma valid_partitioned_schedule_intro :
    forall jobs sched,
      partitioned_schedule_on jobs sched ->
      valid_partitioned_schedule jobs sched.
  ```
- **Proof Strategy**: Trivial — `valid_partitioned_schedule` is currently definitionally equal to `partitioned_schedule_on`. Proof is `exact H`.
- **Key Tactics**: `exact H`
- **Dependencies**: `valid_partitioned_schedule`, `partitioned_schedule_on`
- **Notes**: This lemma exists as an abstraction boundary. Client code should use this instead of `unfold valid_partitioned_schedule` to minimize churn when the definition is later strengthened.
- **Date**: 2026-04-09

---

### `valid_partitioned_schedule_elim`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma valid_partitioned_schedule_elim :
    forall jobs sched,
      valid_partitioned_schedule jobs sched ->
      partitioned_schedule_on jobs sched.
  ```
- **Proof Strategy**: Trivial — `valid_partitioned_schedule` is currently definitionally equal to `partitioned_schedule_on`. Proof is `exact H`.
- **Key Tactics**: `exact H`
- **Dependencies**: `valid_partitioned_schedule`, `partitioned_schedule_on`
- **Notes**: For library-internal use. Client-facing code should prefer reasoning via `valid_partitioned_schedule` directly when possible.
- **Date**: 2026-04-09

---

### `service_between` (EDFLemmas Section 1)
- **Type**: Definition
- **Statement**:
  ```coq
  Definition service_between
      (m : nat) (sched : Schedule) (j : JobId) (t1 t2 : Time) : nat :=
    service_job m sched j t2 - service_job m sched j t1.
  ```
- **Proof Strategy**: N/A (definition)
- **Key Tactics**: N/A
- **Dependencies**: `service_job`
- **Notes**: Abbreviation for interval service. Used throughout EDF optimality proofs.
- **Date**: 2026-04-09

---

### `completed_iff_service_ge_cost`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma completed_iff_service_ge_cost :
    forall jobs m sched j t,
      completed jobs m sched j t <->
      job_cost (jobs j) <= service_job m sched j t.
  ```
- **Proof Strategy**: `unfold completed; lia`
- **Key Tactics**: `unfold`, `lia`
- **Dependencies**: `completed`
- **Notes**: Gateway lemma for converting between `completed` and numeric service comparisons.
- **Date**: 2026-04-09

---

### `not_completed_iff_service_lt_cost`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma not_completed_iff_service_lt_cost :
    forall jobs m sched j t,
      ~ completed jobs m sched j t <->
      service_job m sched j t < job_cost (jobs j).
  ```
- **Proof Strategy**: `rewrite completed_iff_service_ge_cost; lia`
- **Key Tactics**: `rewrite`, `lia`
- **Dependencies**: `completed_iff_service_ge_cost`
- **Notes**: Negation form of `completed_iff_service_ge_cost`. Used to connect `eligible` to service bounds.
- **Date**: 2026-04-09

---

### `missed_deadline_iff_not_completed_at_deadline`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma missed_deadline_iff_not_completed_at_deadline :
    forall jobs m sched j,
      missed_deadline jobs m sched j <->
      ~ completed jobs m sched j (job_abs_deadline (jobs j)).
  ```
- **Proof Strategy**: `unfold missed_deadline; tauto`
- **Key Tactics**: `unfold`, `tauto`
- **Dependencies**: `missed_deadline`, `completed`
- **Notes**: Simple unfold; use as a rewrite lemma.
- **Date**: 2026-04-09

---

### `missed_deadline_iff_service_lt_cost_at_deadline`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma missed_deadline_iff_service_lt_cost_at_deadline :
    forall jobs m sched j,
      missed_deadline jobs m sched j <->
      service_job m sched j (job_abs_deadline (jobs j)) < job_cost (jobs j).
  ```
- **Proof Strategy**: Chain `missed_deadline_iff_not_completed_at_deadline` and `not_completed_iff_service_lt_cost`, close with `tauto`.
- **Key Tactics**: `rewrite`, `tauto`
- **Dependencies**: `missed_deadline_iff_not_completed_at_deadline`, `not_completed_iff_service_lt_cost`
- **Notes**: Key entry point for EDF optimality: deadline miss = insufficient service at deadline.
- **Date**: 2026-04-09

---

### `service_between_0_r`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma service_between_0_r :
    forall m sched j t,
      service_between m sched j 0 t = service_job m sched j t.
  ```
- **Proof Strategy**: `unfold service_between; simpl; lia`
- **Key Tactics**: `unfold`, `simpl`, `lia`
- **Dependencies**: `service_between`, `service_job`
- **Notes**: ⚠️ `simpl` leaves `service_job m sched j t - 0`, which is NOT definitionally equal to `service_job m sched j t`. Must use `lia`, not `reflexivity`.
- **Date**: 2026-04-09

---

### `service_between_split`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma service_between_split :
    forall m sched j t1 t2 t3,
      t1 <= t2 -> t2 <= t3 ->
      service_between m sched j t1 t3 =
      service_between m sched j t1 t2 +
      service_between m sched j t2 t3.
  ```
- **Proof Strategy**: Unfold `service_between`, obtain both monotonicity facts via `service_job_monotone`, close with `lia`.
- **Key Tactics**: `unfold`, `pose proof service_job_monotone`, `lia`
- **Dependencies**: `service_between`, `service_job_monotone`
- **Notes**: Main tool for interval decomposition in prefix arguments.
- **Date**: 2026-04-09

---

### `service_before_release_zero`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma service_before_release_zero :
    forall jobs m sched j t,
      valid_schedule jobs m sched ->
      t <= job_release (jobs j) ->
      service_job m sched j t = 0.
  ```
- **Proof Strategy**: Induction on `t`. Base: `simpl; reflexivity`. Step: `rewrite service_job_step`, apply IH for `service_job t' = 0`, then show `cpu_count = 0` using `cpu_count_zero_iff_not_executed` and `valid_no_run_before_release`.
- **Key Tactics**: `induction t`, `rewrite service_job_step`, `cpu_count_zero_iff_not_executed`, `valid_no_run_before_release`, `lia`
- **Dependencies**: `service_job_step`, `cpu_count_zero_iff_not_executed`, `valid_no_run_before_release`
- **Notes**: Requires `valid_schedule` hypothesis. Foundational for prefix service arguments.
- **Date**: 2026-04-09

---

### `service_at_release_zero`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma service_at_release_zero :
    forall jobs m sched j,
      valid_schedule jobs m sched ->
      service_job m sched j (job_release (jobs j)) = 0.
  ```
- **Proof Strategy**: Apply `service_before_release_zero` with explicit arguments; supply `lia` for the `<= release` goal.
- **Key Tactics**: `apply (service_before_release_zero jobs m sched j ...)`, `lia`
- **Dependencies**: `service_before_release_zero`
- **Notes**: ⚠️ `apply service_before_release_zero` (without explicit args) fails with "Unable to find an instance for the variable jobs". Always provide explicit arguments: `apply (service_before_release_zero jobs m sched j (job_release (jobs j)))`.
- **Date**: 2026-04-09

---

### `agrees_before` (definition + basic lemmas)
- **Type**: Definition + Lemmas
- **Statement**:
  ```coq
  Definition agrees_before (s1 s2 : Schedule) (t : Time) : Prop :=
    forall t' c, t' < t -> s1 t' c = s2 t' c.

  Lemma agrees_before_weaken : forall s1 s2 t1 t2, t1 <= t2 -> agrees_before s1 s2 t2 -> agrees_before s1 s2 t1.
  Lemma agrees_before_refl  : forall s t, agrees_before s s t.
  Lemma agrees_before_sym   : forall s1 s2 t, agrees_before s1 s2 t -> agrees_before s2 s1 t.
  Lemma agrees_before_trans : forall s1 s2 s3 t, agrees_before s1 s2 t -> agrees_before s2 s3 t -> agrees_before s1 s3 t.
  ```
- **Proof Strategy**: All trivial by intro/apply/symmetry/rewrite; `weaken` uses `lia` to lift the `t' < t1` bound to `t' < t2`.
- **Key Tactics**: `lia`, `symmetry`, `apply Hagree`, `rewrite`
- **Dependencies**: `Schedule`, `Time`
- **Notes**: This definition exactly matches the condition in `CandidateSourceSpec.candidates_prefix_extensional`.
- **Date**: 2026-04-09

---

### `cpu_count_agrees_at`
- **Type**: Lemma (helper)
- **Statement**:
  ```coq
  Lemma cpu_count_agrees_at :
    forall m s1 s2 j t,
      (forall c, s1 t c = s2 t c) ->
      cpu_count m s1 j t = cpu_count m s2 j t.
  ```
- **Proof Strategy**: Induction on `m`. Step: `simpl`, `unfold runs_on`, then `rewrite (Heq m')` to equate the `if` branch, then `rewrite (IH ...)` for the recursive call, `reflexivity`.
- **Key Tactics**: `induction m as [| m' IH]`, `simpl`, `unfold runs_on`, `rewrite (Heq m')`, `IH`
- **Dependencies**: `cpu_count`, `runs_on`
- **Notes**: Used as helper in `agrees_before_service_job`. The key step is `unfold runs_on` followed by `rewrite (Heq m')` which equates the `match s1 t m' with ...` and `match s2 t m' with ...` branches.
- **Date**: 2026-04-09

---

### `agrees_before_service_job`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma agrees_before_service_job :
    forall m s1 s2 j t,
      agrees_before s1 s2 t ->
      service_job m s1 j t = service_job m s2 j t.
  ```
- **Proof Strategy**: Induction on `t`. Base: `simpl; reflexivity`. Step: `rewrite service_job_step` for both sides, assert `cpu_count` equality via `cpu_count_agrees_at` (using `Hagree` at `t'` with `lia`), weaken `Hagree` to `t'` via `agrees_before_weaken` for IH, then `rewrite IH; rewrite Hcpu; reflexivity`.
- **Key Tactics**: `induction t as [| t' IH]`, `service_job_step`, `cpu_count_agrees_at`, `agrees_before_weaken`, `lia`
- **Dependencies**: `service_job_step`, `cpu_count_agrees_at`, `agrees_before_weaken`
- **Notes**: Central lemma for prefix extensionality; all `completed`/`eligible`/`ready` variants follow from this.
- **Date**: 2026-04-09

---

### `agrees_before_completed` / `agrees_before_eligible`
- **Type**: Lemmas
- **Statement**:
  ```coq
  Lemma agrees_before_completed : forall jobs m s1 s2 j t, agrees_before s1 s2 t -> completed jobs m s1 j t <-> completed jobs m s2 j t.
  Lemma agrees_before_eligible  : forall jobs m s1 s2 j t, agrees_before s1 s2 t -> eligible jobs m s1 j t <-> eligible jobs m s2 j t.
  ```
- **Proof Strategy**: `completed`: unfold, `rewrite agrees_before_service_job`, `tauto`. `eligible`: unfold, `pose proof agrees_before_completed ... as Hcomp`, `tauto` (tauto can use an iff hypothesis).
- **Key Tactics**: `unfold completed/eligible`, `rewrite`, `pose proof`, `tauto`
- **Dependencies**: `agrees_before_service_job`
- **Notes**: `released` is schedule-independent (pure time comparison), so `eligible` reduces entirely to the `completed` part. `tauto` can use an `H : A <-> B` hypothesis directly.
- **Date**: 2026-04-09

---

### `agrees_before_ready`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma agrees_before_ready :
    forall jobs m s1 s2 j t,
      agrees_before s1 s2 (S t) ->
      ready jobs m s1 j t <-> ready jobs m s2 j t.
  ```
- **Proof Strategy**: Weaken `Hagree (S t)` to `t` for `eligible`. Extract `Hat : forall c, s1 t c = s2 t c` via `Hagree t c (lia: t < S t)`. Unfold `ready`; split; handle `eligible` via `proj1/proj2 Helig`, handle `¬ running` by unfolding, introducing the existential, `apply Hnrun`, supplying `exists c` and rewriting with `Hat`.
- **Key Tactics**: `agrees_before_weaken`, `agrees_before_eligible`, `proj1/proj2`, `unfold running`, `exists c`, `rewrite (Hat c)` / `rewrite <- (Hat c)`
- **Dependencies**: `agrees_before_weaken`, `agrees_before_eligible`, `running`
- **Notes**: ⚠️ `running m s j t` references `s t c` at time `t` directly — `agrees_before s1 s2 t` (strictly before) is INSUFFICIENT. Must use `agrees_before s1 s2 (S t)`. ⚠️ Rewrite directions are non-obvious: in the s1→s2 direction the goal is `s1 t c = Some j` so use `rewrite (Hat c)` (forward); in the s2→s1 direction the goal is `s2 t c = Some j` so use `rewrite <- (Hat c)` (backward).
- **Date**: 2026-04-09

---

### `eligibleb_agrees_before`
- **Type**: Lemma (helper)
- **Statement**:
  ```coq
  Lemma eligibleb_agrees_before :
    forall jobs m s1 s2 j t,
      agrees_before s1 s2 t ->
      eligibleb jobs m s1 j t = eligibleb jobs m s2 j t.
  ```
- **Proof Strategy**: `unfold eligibleb`, then `rewrite (agrees_before_service_job m s1 s2 j t Hagree)`, `reflexivity`. The `job_release <=? t` part is schedule-independent; only `service_job` needs to be equated.
- **Key Tactics**: `unfold eligibleb`, `rewrite agrees_before_service_job`, `reflexivity`
- **Dependencies**: `agrees_before_service_job`
- **Notes**: Used as the bridge between `agrees_before` and `filter` extensionality for `choose_edf`.
- **Date**: 2026-04-09

---

### `candidates_of_agrees_before`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma candidates_of_agrees_before :
    forall J candidates_of (cand_spec : CandidateSourceSpec J candidates_of)
           jobs s1 s2 t,
      agrees_before s1 s2 t ->
      candidates_of jobs 1 s1 t = candidates_of jobs 1 s2 t.
  ```
- **Proof Strategy**: `destruct cand_spec as [_ _ Hpx]` to extract `candidates_prefix_extensional`, then `exact (Hpx jobs 1 s1 s2 t Hagree)`.
- **Key Tactics**: `destruct cand_spec as [_ _ Hpx]`, `exact`
- **Dependencies**: `CandidateSourceSpec.candidates_prefix_extensional`, `agrees_before`
- **Notes**: ⚠️ `cand_spec.(candidates_prefix_extensional)` causes "expected 2 explicit parameters" because `CandidateSourceSpec` has 2 explicit record parameters `(J, candidates_of)`. Must use `destruct` instead of `.()` projection syntax. Contrast with `GenericDispatchSpec` (no parameters) where `.()` works fine.
- **Date**: 2026-04-09

---

### `choose_edf_agrees_before`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma choose_edf_agrees_before :
    forall jobs s1 s2 t candidates,
      agrees_before s1 s2 t ->
      choose_edf jobs 1 s1 t candidates = choose_edf jobs 1 s2 t candidates.
  ```
- **Proof Strategy**: `unfold choose_edf`, then `f_equal` to reduce to `filter f l = filter g l`, then `List.filter_ext` + `eligibleb_agrees_before`.
- **Key Tactics**: `unfold choose_edf`, `f_equal`, `List.filter_ext`, `eligibleb_agrees_before`
- **Dependencies**: `eligibleb_agrees_before`, `List.filter_ext`
- **Notes**: `List.filter_ext` is available via `From Stdlib Require Import List`. Signature: `(forall a, f a = g a) -> forall l, filter f l = filter g l`.
- **Date**: 2026-04-09

---

### `edf_dispatch_agrees_before`
- **Type**: Lemma
- **Statement**:
  ```coq
  Lemma edf_dispatch_agrees_before :
    forall J candidates_of (cand_spec : CandidateSourceSpec J candidates_of)
           jobs s1 s2 t,
      agrees_before s1 s2 t ->
      dispatch edf_generic_spec jobs 1 s1 t (candidates_of jobs 1 s1 t) =
      dispatch edf_generic_spec jobs 1 s2 t (candidates_of jobs 1 s2 t).
  ```
- **Proof Strategy**: `simpl` unfolds `dispatch edf_generic_spec` to `choose_edf`. Then `rewrite candidates_of_agrees_before` to equate the candidate lists, then `apply choose_edf_agrees_before`.
- **Key Tactics**: `simpl`, `rewrite candidates_of_agrees_before`, `apply choose_edf_agrees_before`
- **Dependencies**: `candidates_of_agrees_before`, `choose_edf_agrees_before`
- **Notes**: `dispatch edf_generic_spec` reduces via `simpl` because `edf_generic_spec = mkGenericDispatchSpec choose_edf ...` and `dispatch` is just the first field projection.
- **Date**: 2026-04-09

---

### `matches_choose_edf_at` / `matches_choose_edf_at_with` / `matches_choose_edf_before` / `respects_edf_priority_at` / `respects_edf_priority_at_on` / `edf_violation_at`
- **Type**: Definition (Section 4 definitions, EDFLemmas.v)
- **Statement**: Six definitions for canonical EDF match and priority violation:
  - `matches_choose_edf_at jobs sched t candidates`: `sched t 0 = choose_edf jobs 1 sched t candidates`
  - `matches_choose_edf_at_with jobs candidates_of sched t`: uses `candidates_of` to supply candidates
  - `matches_choose_edf_before jobs candidates_of sched H`: `forall t, t < H -> matches_choose_edf_at_with ...`
  - `respects_edf_priority_at jobs sched t`: no earlier-dl eligible job ignored at t
  - `respects_edf_priority_at_on J jobs sched t`: same with explicit job set J
  - `edf_violation_at jobs sched t`: `exists j j', sched t 0 = Some j /\ eligible ... j' t /\ dl j' < dl j`
- **Proof Strategy**: Direct definitions — no proof needed.
- **Key Tactics**: N/A
- **Dependencies**: `choose_edf`, `eligible`, `CandidateSource`
- **Notes**: `matches_choose_edf_at_with` can be false even for EDF-correct choices when a tie-deadline job is chosen instead. It expresses *canonical* agreement, not the EDF semantic property. The semantic property is `respects_edf_priority_at`.
- **Date**: 2026-04-09

---

### `canonical_non_edf_step_has_other_min_or_better_eligible_job`
- **Type**: Lemma (4-5, EDFLemmas.v)
- **Statement**:
  ```coq
  Lemma canonical_non_edf_step_has_other_min_or_better_eligible_job :
    forall J candidates_of (cand_spec : CandidateSourceSpec J candidates_of)
           jobs sched t j,
      valid_schedule jobs 1 sched ->
      sched t 0 = Some j ->
      J j ->
      ~ matches_choose_edf_at_with jobs candidates_of sched t ->
      exists j',
        In j' (candidates_of jobs 1 sched t) /\
        eligible jobs 1 sched j' t /\
        job_abs_deadline (jobs j') <= job_abs_deadline (jobs j) /\
        j' <> j.
  ```
- **Proof Strategy**: (1) `valid_running_implies_eligible` (c=0, lia for c<1) → `eligible j`. (2) `candidates_complete` → `In j candidates`. (3) `choose_edf_some_if_exists` → `Some j'`. (4) `choose_edf_in_candidates`, `choose_edf_eligible`, `choose_edf_min_deadline` give properties of j'. (5) `~ matches_choose_edf_at_with` + `Hsched : sched t 0 = Some j` + `Hchoose : choose_edf ... = Some j'`: if `j' = j` then `subst j'` + `rewrite Hsched; symmetry; exact Hchoose` contradicts `Hnot`.
- **Key Tactics**: `valid_running_implies_eligible`, `destruct cand_spec as [_ Hcomplete _]`, `choose_edf_some_if_exists`, `choose_edf_in_candidates`, `choose_edf_eligible`, `choose_edf_min_deadline`, `subst`, `symmetry`
- **Dependencies**: `valid_running_implies_eligible`, `CandidateSourceSpec`, `choose_edf_some_if_exists`, `choose_edf_in_candidates`, `choose_edf_eligible`, `choose_edf_min_deadline`
- **Notes**: ⚠️ `matches_choose_edf_at_with` is `sched t 0 = choose_edf ...`, so to derive contradiction from `Hnot : ~ matches_choose_edf_at_with` we need `sched t 0 = choose_edf ...`. After `subst j'`, `Hchoose : choose_edf ... = Some j`. Use `rewrite Hsched; symmetry; exact Hchoose` (not `rewrite Hchoose`). ⚠️ `CandidateSourceSpec` has 2 explicit parameters — use `destruct cand_spec as [_ Hcomplete _]` not `.()` projection.
- **Date**: 2026-04-09

---

### `exists_first_edf_violation_before`
- **Type**: Lemma (4-6, EDFLemmas.v)
- **Statement**:
  ```coq
  Lemma exists_first_edf_violation_before :
    forall jobs sched H,
      (exists t, t < H /\ edf_violation_at jobs sched t) ->
      exists t0,
        t0 < H /\
        edf_violation_at jobs sched t0 /\
        (forall t, t < t0 -> ~ edf_violation_at jobs sched t).
  ```
- **Proof Strategy**: Intro and destruct the witness `[t [HtH Hviol]]`. Revert `H HtH`. Apply `well_founded_induction lt_wf` on `t`. `classic` on `exists t', t' < t /\ edf_violation_at ... t'`. If yes: apply IH directly. If no: `t` itself is minimal — produce it as the witness.
- **Key Tactics**: `well_founded_induction lt_wf`, `classic`, `Nat.lt_trans`
- **Dependencies**: `edf_violation_at`, `Classical` (for `classic`)
- **Notes**: ⚠️ `well_founded_induction lt_wf` generalizes `Hviol : edf_violation_at ... t` into IH (since it depends on `t`). IH becomes `forall y, y < t -> edf_violation_at ... y -> forall H, y < H -> exists t0, ...`. So the call is `IH t' Hlt' Hviol' H (Nat.lt_trans _ _ _ Hlt' HtH)` — NOT `IH t' Hlt' H (Nat.lt_trans ...)`. ⚠️ Requires `From Stdlib Require Import ... Classical` in the file header.
- **Date**: 2026-04-09

---

### `edf_violation_exposes_exchange_pair`
- **Type**: Lemma (5-1, EDFLemmas.v)
- **Statement**:
  ```coq
  Lemma edf_violation_exposes_exchange_pair :
    forall jobs sched t j,
      sched t 0 = Some j ->
      edf_violation_at jobs sched t ->
      exists j',
        eligible jobs 1 sched j' t /\
        job_abs_deadline (jobs j') < job_abs_deadline (jobs j).
  ```
- **Proof Strategy**: Unfold `edf_violation_at` to get `exists j_run j', ...`. Use `injection` + `subst` on `sched t 0 = Some j` vs `sched t 0 = Some j_run` to identify `j_run = j`. Return `j'` directly.
- **Key Tactics**: `unfold edf_violation_at`, `destruct ... as [j_run [j' [...]]]`, `rewrite Hsched in Hrun`, `injection Hrun as Heq`, `subst`
- **Dependencies**: `edf_violation_at`
- **Notes**: Plan's statement had `J j` hypothesis and `J j'` conclusion, but `J j'` cannot be derived without `CandidateSourceSpec`. Simpler form (no `J`) is the correct provable version.
- **Date**: 2026-04-09

---

### `matches_choose_edf_at_with_no_earlier_eligible_job`
- **Type**: Lemma (5-2, EDFLemmas.v)
- **Statement**:
  ```coq
  Lemma matches_choose_edf_at_with_no_earlier_eligible_job :
    forall J candidates_of
           (cand_spec : CandidateSourceSpec J candidates_of)
           jobs sched t j,
      matches_choose_edf_at_with jobs candidates_of sched t ->
      sched t 0 = Some j ->
      forall j',
        J j' ->
        eligible jobs 1 sched j' t ->
        job_abs_deadline (jobs j') < job_abs_deadline (jobs j) ->
        False.
  ```
- **Proof Strategy**: `matches_choose_edf_at_with` + `sched t 0 = Some j` → `choose_edf ... = Some j` (by `symmetry`). `candidates_complete` + `J j'` + `eligible` → `In j' candidates`. `choose_edf_min_deadline` → `dl j <= dl j'`. `lia` contradicts `dl j' < dl j`.
- **Key Tactics**: `unfold matches_choose_edf_at_with`, `rewrite Hsched in Hmatch`, `symmetry`, `destruct cand_spec as [_ Hcomplete _]`, `choose_edf_min_deadline`, `lia`
- **Dependencies**: `matches_choose_edf_at_with`, `CandidateSourceSpec`, `choose_edf_min_deadline`
- **Notes**: Pattern `rewrite Hsched in Hmatch; symmetry. exact Hmatch` gives `choose_edf ... = Some j` from `Some j = choose_edf ...`.
- **Date**: 2026-04-09

---

### `matches_choose_edf_at_with_implies_respects_edf_priority_at_on`
- **Type**: Lemma (5-3, EDFLemmas.v)
- **Statement**:
  ```coq
  Lemma matches_choose_edf_at_with_implies_respects_edf_priority_at_on :
    forall J candidates_of
           (cand_spec : CandidateSourceSpec J candidates_of)
           jobs sched t,
      matches_choose_edf_at_with jobs candidates_of sched t ->
      respects_edf_priority_at_on J jobs sched t.
  ```
- **Proof Strategy**: Unfold `respects_edf_priority_at_on` (intros j j' _ HJj' Hsched Helig Hlt) then delegate to `matches_choose_edf_at_with_no_earlier_eligible_job`.
- **Key Tactics**: `unfold respects_edf_priority_at_on`, `exact (matches_choose_edf_at_with_no_earlier_eligible_job ...)`
- **Dependencies**: `matches_choose_edf_at_with_no_earlier_eligible_job`, `respects_edf_priority_at_on`
- **Notes**: The first `J j` hypothesis in `respects_edf_priority_at_on` (i.e., `J j` for the running job) is not needed here — use `_` to discard it.
- **Date**: 2026-04-09

---

### `service_increases_implies_executed_in_interval`
- **Type**: Lemma (6-1, EDFLemmas.v)
- **Statement**:
  ```coq
  Lemma service_increases_implies_executed_in_interval :
    forall m sched j t1 t2,
      t1 < t2 ->
      service_job m sched j t1 < service_job m sched j t2 ->
      exists t',
        t1 <= t' < t2 /\
        0 < cpu_count m sched j t'.
  ```
- **Proof Strategy**: Induction on `t2`. Base case `t2 = 0` contradicts `t1 < 0`. Step case `t2 = S t2'`: rewrite `service_job_step` to expose `cpu_count` at `t2'`. Case split via `Nat.eq_dec (cpu_count ... t2') 0`. If nonzero: `t' = t2'` is the witness. If zero: service didn't change at last step, so service must have increased over `[t1, t2')`. Use `Nat.eq_dec t1 t2'` to derive `t1 < t2'` (if `t1 = t2'` then `service_job t1 < service_job t1`, contradiction), then apply IH.
- **Key Tactics**: `induction t2`, `rewrite service_job_step in Hinc`, `Nat.eq_dec`, `lia`
- **Dependencies**: `service_job_step`, `cpu_count`, `service_job`
- **Notes**: ⚠️ `Nat.lt_or_eq` does not exist in Rocq 9. Use `Nat.eq_dec` to case-split on equality. ⚠️ `Nat.le_or_lt` and `le_or_lt` are not in scope; use `classic` from Classical for dichotomy on nat comparison.
- **Date**: 2026-04-10

---

### `eligible_feasible_implies_runs_later_before_deadline`
- **Type**: Lemma (6-2, EDFLemmas.v)
- **Statement**:
  ```coq
  Lemma eligible_feasible_implies_runs_later_before_deadline :
    forall J jobs sched j t,
      J j ->
      valid_schedule jobs 1 sched ->
      feasible_schedule_on J jobs 1 sched ->
      eligible jobs 1 sched j t ->
      exists t',
        t <= t' /\
        t' < job_abs_deadline (jobs j) /\
        sched t' 0 = Some j.
  ```
- **Proof Strategy**: Chain: (1) `eligible → ~completed → service < cost` via `not_completed_iff_service_lt_cost`; (2) `feasible_schedule_on + J j → ~missed_deadline → ~~completed → completed → service >= cost` via `NNPP + completed_iff_service_ge_cost`; (3) combine for service strictly increases from t to deadline; (4) `t < deadline` by `classic` + contrapositive via `service_job_monotone`; (5) apply `service_increases_implies_executed_in_interval`; (6) for m=1, `cpu_count_pos_iff_executed` gives `c < 1` so `c = 0` by `lia`, thus `sched t' 0 = Some j`.
- **Key Tactics**: `not_completed_iff_service_lt_cost`, `NNPP`, `unfold missed_deadline in Hfeas`, `completed_iff_service_ge_cost`, `lia`, `classic`, `service_job_monotone`, `service_increases_implies_executed_in_interval`, `cpu_count_pos_iff_executed`
- **Dependencies**: `service_increases_implies_executed_in_interval`, `not_completed_iff_service_lt_cost`, `completed_iff_service_ge_cost`, `service_job_monotone`, `cpu_count_pos_iff_executed`, `NNPP` (Classical), `classic` (Classical)
- **Notes**: ⚠️ `feasible_schedule_on J jobs 1 sched` provides `J j -> ~missed_deadline j`, i.e., `~~completed j (deadline j)`. To get `completed`, use `apply NNPP` + `unfold missed_deadline in Hfeas` to expose the double negation. ⚠️ Do NOT use `apply (Hfeas j HJj)` directly on a `completed` goal — the types won't unify without unfolding. ⚠️ `by_contra` is not in scope in Rocq 9 without extra imports; use `destruct (classic ...) as [H | H]` instead.
- **Date**: 2026-04-10
