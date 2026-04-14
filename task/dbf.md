# Demand Bound Function (dbf) 層の導入

## 実装Plan

### 1. per-task dbf の核を追加する
**実装ファイル**
- `theories/Analysis/Uniprocessor/DemandBound.v`（新規）

**入れるもの**
- `periodic_dbf`
- `sporadic_dbf_bound`
- `jittered_periodic_dbf_bound`
- 基本補題:
  - `periodic_dbf_zero_before_deadline`
  - `periodic_dbf_at_deadline`
  - `periodic_dbf_monotone`
  - `sporadic_dbf_bound_eq_periodic_dbf`
  - `jittered_periodic_dbf_bound_eq_sporadic_dbf`
  - `periodic_dbf_le_periodic_rbf`

**方針**
- core `Task` / `Schedule` は変更しない
- dbf 側だけで `0 < task_period` を仮定し、必要なら `0 < task_relative_deadline` を analysis-side assumption として置く

### 2. deadline-bounded horizon を task-model 側に追加する
**実装ファイル**
- `theories/TaskModels/Periodic/PeriodicDemandBound.v`（新規）
- `theories/TaskModels/Sporadic/SporadicDemandBound.v`（新規）
- `theories/TaskModels/Jitter/JitteredPeriodicDemandBound.v`（新規）

**入れるもの**
- release `< H` ではなく、**absolute deadline `<= H`** を基準にした demand 用 jobset/hook
- explicit job list の総 demand を dbf で抑える補題
  - periodic: できれば per-task exact まで持っていく
  - sporadic/jittered: まずは upper bound として十分

**重要点**
- RBF 用 finite horizon と DBF 用 finite horizon は分ける
- 既存の `*_Workload.v` を壊さず、dbf 用の薄い橋を別ファイルで足す

### 3. 集約版 demand hook を追加する
**実装ファイル**
- `theories/Analysis/Common/WorkloadAggregation.v`（追記）または
- `theories/Analysis/Uniprocessor/DemandBound.v`（集約補題を同居）

**入れるもの**
- `total_dbf` 的な総和定義
- task ごとの dbf 上界から jobset 全体の demand 上界を得る補題
- 後の processor-demand theorem で再利用できる形にする

### 4. 例と回帰確認を追加する
**実装ファイル**
- `theories/Examples/DemandBoundExamples.v`（新規）
- `_CoqProject`（追記）

**例の内容**
- 単一 periodic task の具体計算
- `dbf <= rbf`
- sporadic / jittered が periodic 由来の上界に落ちる例
- 可能なら小さな EDF 向け processor-demand 前段例

### 5. 文書を同期する
**実装ファイル**
- `plan/roadmap.md`
- `plan/what_to_prove.md`

**反映内容**
- G-2 / Lv.6-5 の status を `RBF layer complete` から `DBF initial layer implemented` へ更新
- 「残りは processor-demand / response-time hook」であることを明記

## TODO

- [ ] `DemandBound.v` を新設し、`periodic_dbf` を定義する
- [ ] `periodic_dbf` の零化・単調性・`dbf <= rbf` を証明する
- [ ] `sporadic_dbf_bound` と `jittered_periodic_dbf_bound` を periodic 由来の上界として定義する
- [ ] periodic/sporadic/jittered ごとに deadline-bounded jobset bridge を追加する
- [ ] explicit job list の total demand を dbf で抑える補題を追加する
- [ ] `DemandBoundExamples.v` を追加する
- [ ] `_CoqProject` を更新する
- [ ] roadmap / proof inventory を同期する

## Rocqスケルトン

```coq
From Stdlib Require Import Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Analysis.Uniprocessor.RequestBound.

Definition periodic_dbf
    (tasks : TaskId -> Task) (τ : TaskId) (H : Time) : nat :=
  if H <? task_relative_deadline (tasks τ) then 0
  else
    (S ((H - task_relative_deadline (tasks τ))
         / task_period (tasks τ)))
    * task_cost (tasks τ).

Definition sporadic_dbf_bound
    (tasks : TaskId -> Task) (τ : TaskId) (H : Time) : nat :=
  periodic_dbf tasks τ H.

Lemma periodic_dbf_zero_before_deadline :
  forall tasks τ H,
    H < task_relative_deadline (tasks τ) ->
    periodic_dbf tasks τ H = 0.
Proof.
Admitted.

Lemma periodic_dbf_le_periodic_rbf :
  forall tasks τ H,
    0 < task_period (tasks τ) ->
    periodic_dbf tasks τ H <= periodic_rbf tasks τ H.
Proof.
Admitted.
```

## このタスクの完了条件

- dbf の定義と基本補題が入る
- periodic/sporadic/jittered の demand hook が揃う
- `dbf <= rbf` がライブラリとして使える
- 次段の processor-demand theorem に進める状態になる