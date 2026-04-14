# analysis-ready workload 抽象を共通化し、その上に request-bound foundation を追加

## 次タスクの方針

priority と実装状況の両方から見て、次は **Phase G-2 の入口として RBF 層を作る** のが最も自然である。

理由は 3 つである。

1. `BusyInterval` がすでに存在し、analysis 層の最初の足場がある
2. periodic / sporadic / jittered-periodic の workload hook がすでにある
3. 今のまま dbf/rbf に進むと、task-model 側に重複実装が増える

したがって、順序は次である。

1. workload 集約の共通化
2. horizon 内 job-count / workload 上界の tightening
3. request-bound theory の導入
4. その後に dbf へ進む

---

## 実装Plan

### 1. 共通 workload 集約モジュールを新設する

まず `PeriodicWorkload.v` と `SporadicWorkload.v` から重複部分を抜く。

**新規ファイル**
- `theories/Analysis/Common/WorkloadAggregation.v`

**ここに入れるもの**
- `total_job_cost`
- `total_job_cost_le_length_mul`
- list ベース workload 集約の基本補題

これにより、task-model ごとの workload 証明は
「そのモデル特有の count bound」を示すことに集中できるようになる。

---

### 2. periodic / sporadic の count bound を period-aware に強化する

現状の `H` 上界は analysis hook としては粗すぎるため、ここを強化する。

**修正ファイル**
- `theories/TaskModels/Periodic/PeriodicWorkload.v`
- `theories/TaskModels/Sporadic/SporadicWorkload.v`
- `theories/TaskModels/Jitter/JitteredPeriodicWorkload.v`

**やること**
- `PeriodicWorkload.v` では、`task_period` と `offset` を使った tighter count bound を導入する
- `SporadicWorkload.v` では、`earliest_sporadic_release` と separation から count bound を導く
- `JitteredPeriodicWorkload.v` では、sporadic 側の bound を再利用する

ここでは「最終的に最も鋭い bound」を最初から狙う必要はない。
まずは **`H` より明らかに良い、period-aware な bound** を導入することが重要である。

---

### 3. Request-bound theory を analysis 層として追加する

task-model 側の workload bound を、そのまま analysis の用語へ昇格させる。

**新規ファイル**
- `theories/Analysis/Uniprocessor/RequestBound.v`

**このファイルで定義するもの**
- periodic request bound
- sporadic request bound upper bound
- jittered-periodic request bound upper bound
- monotonicity
- basic algebraic lemmas
- workload lemma から RBF への橋渡し補題

ここで重要なのは、RBF を schedule semantics ではなく **task-generation / workload 側から供給される analysis interface** として置くことである。

---

### 4. example を追加して API を固定する

RBF 層は後で dbf や response-time analysis の土台になるため、先に使用例で API を固めるべきである。

**新規ファイル**
- `theories/Examples/RequestBoundExamples.v`

**例の内容**
- simple periodic task set に対する RBF 計算例
- sporadic bound の使用例
- jittered-periodic が sporadic upper bound に落ちる例

---

### 5. 文書を同期する

Analysis を増やすので、設計文書も同期対象である。

**修正ファイル**
- `design/ArchitecturalLayering.md`
- `plan/roadmap.md`
- `plan/what_to_prove.md`
- `_CoqProject`

`ArchitecturalLayering.md` では、`BusyInterval` に続く `RequestBound` を Analysis 層の正式な構成要素として明記するべきである。

---

## TODO リスト

- [ ] `theories/Analysis/Common/WorkloadAggregation.v` を追加する
- [ ] `PeriodicWorkload.v` の `total_job_cost` 重複を除去する
- [ ] `SporadicWorkload.v` の `total_job_cost` 重複を除去する
- [ ] periodic count/workload bound を period-aware に強化する
- [ ] sporadic count/workload bound を separation-aware に強化する
- [ ] jittered-periodic 側を sporadic upper bound 再利用に整理する
- [ ] `theories/Analysis/Uniprocessor/RequestBound.v` を追加する
- [ ] `theories/Examples/RequestBoundExamples.v` を追加する
- [ ] `_CoqProject` を更新する
- [ ] `design/ArchitecturalLayering.md` を更新する
- [ ] `plan/roadmap.md` を更新する
- [ ] `plan/what_to_prove.md` を更新する

---

## 実装ファイル一覧

**新規作成**
- `theories/Analysis/Common/WorkloadAggregation.v`
- `theories/Analysis/Uniprocessor/RequestBound.v`
- `theories/Examples/RequestBoundExamples.v`

**修正**
- `theories/TaskModels/Periodic/PeriodicWorkload.v`
- `theories/TaskModels/Sporadic/SporadicWorkload.v`
- `theories/TaskModels/Jitter/JitteredPeriodicWorkload.v`
- `_CoqProject`
- `design/ArchitecturalLayering.md`
- `plan/roadmap.md`
- `plan/what_to_prove.md`

---

## Rocq スケルトン

```coq
(* theories/Analysis/Common/WorkloadAggregation.v *)
From Stdlib Require Import Arith Arith.PeanoNat Lia List.
From RocqSched Require Import Foundation.Base.
Import ListNotations.

Fixpoint total_job_cost
    (jobs : JobId -> Job) (l : list JobId) : nat :=
  match l with
  | [] => 0
  | j :: l' => job_cost (jobs j) + total_job_cost jobs l'
  end.

Lemma total_job_cost_le_length_mul :
  forall jobs l c,
    (forall j, In j l -> job_cost (jobs j) <= c) ->
    total_job_cost jobs l <= length l * c.
Proof.
Admitted.
```

```coq
(* theories/Analysis/Uniprocessor/RequestBound.v *)
From Stdlib Require Import Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.

Definition periodic_rbf
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (τ : TaskId)
    (H : Time) : nat :=
  (* count bound × WCET *)
  0.

Definition sporadic_rbf_bound
    (tasks : TaskId -> Task)
    (τ : TaskId)
    (H : Time) : nat :=
  0.

Lemma periodic_rbf_monotone :
  forall tasks offset τ H1 H2,
    H1 <= H2 ->
    periodic_rbf tasks offset τ H1 <= periodic_rbf tasks offset τ H2.
Proof.
Admitted.
```
