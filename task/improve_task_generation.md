# Phase B: periodic release-pattern strengthening

## 実装プラン

### 目標
periodic task model について、同一 task 内での job index と release の対応を補題として明示し、以後の jitter・analysis・bridge の土台にする。

### TODO

- [ ] `theories/TaskModels/Periodic/PeriodicReleaseLemmas.v` を新設する
  - `expected_release_strict_mono`
  - `expected_release_eq_implies_same_index`
  - `expected_release_lt_implies_index_lt` またはその逆向き補題
  - `same_task_same_index_implies_same_expected_release`
  - `same_task_same_release_implies_same_index`
- [ ] `_CoqProject` に `theories/TaskModels/Periodic/PeriodicReleaseLemmas.v` を追加する
- [ ] `theories/TaskModels/Sporadic/SporadicPeriodicBridge.v` を更新し、新補題を使う形に整理する
  - periodic → sporadic bridge の証明依存を明示化する
  - 将来の jitter 拡張で再利用しやすい補題境界にする
- [ ] `theories/TaskModels/Periodic/PeriodicFiniteHorizon.v` に必要なら horizon 制約つき系を追加する
  - `release < H` からの index 境界と、新補題の接続
- [ ] `theories/Examples/PeriodicExamples.v` に回帰 proof を追加する
  - same-task same-release から same-index を導く例
  - finite horizon 上で index bound が動く例
- [ ] `plan/roadmap.md`, `plan/what_to_prove.md` を最小限更新する
  - B-1 の「stronger release-pattern lemmas」を完了扱いに近づける

## 実装ファイル

- 新規:
  - `theories/TaskModels/Periodic/PeriodicReleaseLemmas.v`
- 修正:
  - `_CoqProject`
  - `theories/TaskModels/Sporadic/SporadicPeriodicBridge.v`
  - `theories/TaskModels/Periodic/PeriodicFiniteHorizon.v`
  - `theories/Examples/PeriodicExamples.v`
  - `plan/roadmap.md`
  - `plan/what_to_prove.md`

## Rocq スケルトン

```coq
From Stdlib Require Import Arith Arith.PeanoNat Lia Bool.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.

Lemma expected_release_strict_mono :
  forall T tasks offset τ k1 k2,
    well_formed_periodic_tasks_on T tasks ->
    T τ ->
    k1 < k2 ->
    expected_release tasks offset τ k1 <
    expected_release tasks offset τ k2.
Proof.
Admitted.

Lemma expected_release_eq_implies_same_index :
  forall T tasks offset τ k1 k2,
    well_formed_periodic_tasks_on T tasks ->
    T τ ->
    expected_release tasks offset τ k1 =
    expected_release tasks offset τ k2 ->
    k1 = k2.
Proof.
Admitted.

Lemma generated_by_periodic_same_task_same_release_implies_same_index :
  forall T tasks offset jobs j1 j2,
    well_formed_periodic_tasks_on T tasks ->
    T (job_task (jobs j1)) ->
    generated_by_periodic_task tasks offset jobs j1 ->
    generated_by_periodic_task tasks offset jobs j2 ->
    job_task (jobs j1) = job_task (jobs j2) ->
    job_release (jobs j1) = job_release (jobs j2) ->
    job_index (jobs j1) = job_index (jobs j2).
Proof.
Admitted.
```

## 完了条件

- periodic 側で「index ↔ expected release」の基本補題が揃う
- sporadic bridge がその補題を経由して読める形になる
- examples で最小限の回帰確認ができる

