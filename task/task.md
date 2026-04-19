## Update 2026-04-20

このタスクで意図していた common-layer の導入は、現時点で次まで実装済みである。

- `LabeledExecution.v`
- `DelayModel.v`
- `DelayBudget.v`
- `BoundedDelayRefinement.v`
- `OperationalDelayExamples.v`
- `_CoqProject` / `OperationalEntryPoints.v`

さらに今回の更新で、次を追加した。

- `DelayTrace`, `cumulative_delay`, `delay_budget_le`
- `cumulative_delay_zero_len`, `cumulative_delay_split`, `delay_budget_monotone_delta`
- `service_distance_le`
- `bounded_delay_projection_refinement`
- `bounded_delay_top_m_projection_refinement`
- actual / ideal semantic validity extraction lemmas
- `service_distance_zero_implies_service_eq`

したがって、この文書の「追加するファイル」「未着手」という表現は一部 stale であり、
残タスクは common boundary の新設ではなく、adapter / Awkernel / end-to-end
refinement 側の obligation を満たすことである。

次にいきなり

> `project_schedule` が ideal top-`m` schedule から高々 δ だけ遅れる

という本定理を証明しに行くのは早い。実装上の次タスクは、より小さく切って、**Operational 層に delay-aware obligation の共通インターフェースを導入すること**である。

理由は次の通りである。

* 前回予定していた `Operational -> project_schedule -> multicore_semantic_validity / placement` の橋は、実装上すでに入っている。

  * `ProjectionInvariants.v`
  * `ProjectionMulticoreValidity.v`
  * `StepLemmas.v`
  * `OperationalEntryPoints.v`
  * `Awkernel/MinimalProjection.v`
* 一方で、delay 関連はまだ未着手である。

  * delay source の型がない
  * event-labeled trace がない
  * delay budget の累積定義がない
  * actual schedule と ideal schedule の lag relation がない
  * top-`m` ideal schedule と operational projection を比較する refinement record がない
* 現在の `trace_stepwise` は `forall t, exists ev, ...` なので、**どの event が起きたかを後から delay accounting に使えない**。bounded-delay に進むには、まず event を trace に露出する必要がある。

研究方針としても、OS-like operational semantics に timer / wakeup / migration / IPI を入れて multicore scheduler refinement へ接続する方向は、このプロジェクトの太い新規性に合っている。既存手法では global EDF / top-`m` / migration correctness を concrete multicore scheduler まで end-to-end に接続する部分が薄い、という整理とも一致する。 また、OS 割込み・wakeup・migration を含む scheduler semantics は、multicore refinement の研究軸として有力である。

---

## 次に行うべきタスク

### Phase H-1a / H-2b / J-0

**Delay-aware operational obligation boundary の導入**

目的は、次の形の境界を作ることである。

```text
Operational labeled execution
  -> delay source trace
  -> cumulative delay budget
  -> project_schedule actual
  -> ideal top-m schedule
  -> bounded service lag / bounded projection lag
```

ここではまだ Awkernel の具体 scheduler 実装まで降りない。まず共通層で、後続の Awkernel refinement が満たすべき obligation の形を固定する。

---

## 重要な設計判断

### 1. `Schedule` に delay を埋め込まない

これは既存 roadmap の方針通りでよい。`Schedule` は理想化された semantic core として残し、delay は `Operational` / `Refinement` 側に置くべきである。

### 2. CPU ごとの pointwise equality ではなく service lag を主関係にする

global top-`m` では CPU の割当順序や migration があるため、

```text
actual t c = ideal t c
```

のような CPU-wise 比較は強すぎる。まずは job 単位の service 比較にするのがよい。

中心定義は次の形がよい。

```coq
Definition service_lag_le
    (m : nat) (ideal actual : Schedule) (delta : nat) : Prop :=
  forall j t,
    service_job m ideal j t <=
    service_job m actual j (t + delta).
```

これは「actual は ideal に対して高々 `delta` だけ service 上遅れる」という意味である。

### 3. `OpEvent` をすぐ拡張しすぎない

`OpEvent` に `EvIPI` や `EvMigrate` を直接足すと、既存の `op_step` 証明が広く壊れる可能性がある。最初は side-channel として delay source trace を置くのが安全である。

---

## 実装対象ファイル

追加するファイル:

* `theories/Operational/Common/LabeledExecution.v`
* `theories/Operational/Common/DelayModel.v`
* `theories/Operational/Common/DelayBudget.v`
* `theories/Refinement/BoundedDelayRefinement.v`
* `theories/Examples/OperationalDelayExamples.v`

更新するファイル:

* `_CoqProject`
* `theories/Operational/Common/OperationalEntryPoints.v`
* `design/Operational.md`
* `design/Refinement.md`
* `plan/roadmap.md`
* `plan/what_to_prove.md`

---

## 実装 Plan

### 1. event-labeled execution を追加する

現在の `execution` は event を existential に隠している。delay accounting では event 種別が必要なので、既存 `execution` は壊さず、別 record を追加する。

対象:

* `theories/Operational/Common/LabeledExecution.v`

```coq
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Operational.Common.State.
From RocqSched Require Import Operational.Common.Trace.
From RocqSched Require Import Operational.Common.Step.
From RocqSched Require Import Operational.Common.Invariants.
From RocqSched Require Import Operational.Common.Execution.

Record labeled_execution (m : nat) : Type := mkLabeledExecution {
  lex_trace : OpTrace;
  lex_event : Time -> OpEvent;
  lex_init : Prop;
  lex_stepwise :
    forall t, op_step (lex_trace t) (lex_event t) (lex_trace (S t));
  lex_struct_inv :
    forall t, op_struct_inv m (lex_trace t);
}.

Definition labeled_to_execution
    {m : nat} (ex : labeled_execution m) : execution m :=
  mkExecution
    m
    (lex_trace ex)
    (lex_init ex)
    (fun t => ex_intro _ (lex_event ex t) (lex_stepwise ex t))
    (lex_struct_inv ex).

Lemma labeled_to_execution_trace_eq :
  forall m (ex : labeled_execution m) t,
    ex_trace (labeled_to_execution ex) t = lex_trace ex t.
Proof.
  reflexivity.
Qed.
```

完了条件は、既存の `execution_multicore_projection_sound` が `labeled_to_execution ex` にそのまま使えることである。

---

### 2. delay source の分類を追加する

対象:

* `theories/Operational/Common/DelayModel.v`

```coq
From Stdlib Require Import List Arith Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Operational.Common.Step.
Import ListNotations.

Inductive op_delay_source : Type :=
| DelayDispatch
| DelayWakeup
| DelayTimer
| DelayMigration
| DelayIPI
| DelayNonpreemptive.

Record op_delay_bounds : Type := mkOpDelayBounds {
  odb_dispatch : nat;
  odb_wakeup : nat;
  odb_timer : nat;
  odb_migration : nat;
  odb_ipi : nat;
  odb_nonpreemptive : nat;
}.

Definition delay_bound_of
    (B : op_delay_bounds) (src : op_delay_source) : nat :=
  match src with
  | DelayDispatch => odb_dispatch B
  | DelayWakeup => odb_wakeup B
  | DelayTimer => odb_timer B
  | DelayMigration => odb_migration B
  | DelayIPI => odb_ipi B
  | DelayNonpreemptive => odb_nonpreemptive B
  end.

Definition default_event_delay_sources (ev : OpEvent) : list op_delay_source :=
  match ev with
  | EvDispatch _ _ => [DelayDispatch]
  | EvWakeup _ => [DelayWakeup]
  | EvResched _ => [DelayIPI]
  | EvTick => [DelayTimer]
  | EvBlock _ => []
  | EvComplete _ => []
  end.
```

ここでは migration を `OpEvent` に直接入れず、後続で extra delay source として足せるようにしておく。

---

### 3. delay budget の累積補題を作る

対象:

* `theories/Operational/Common/DelayBudget.v`

```coq
From Stdlib Require Import List Arith Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Operational.Common.DelayModel.
Import ListNotations.

Definition DelayTrace : Type := Time -> list op_delay_source.

Fixpoint sum_delay_sources
    (B : op_delay_bounds) (xs : list op_delay_source) : nat :=
  match xs with
  | [] => 0
  | x :: xs' => delay_bound_of B x + sum_delay_sources B xs'
  end.

Fixpoint cumulative_delay_from
    (B : op_delay_bounds) (dt : DelayTrace)
    (start len : nat) : nat :=
  match len with
  | 0 => 0
  | S len' =>
      sum_delay_sources B (dt start)
      + cumulative_delay_from B dt (S start) len'
  end.

Definition cumulative_delay
    (B : op_delay_bounds) (dt : DelayTrace)
    (t1 t2 : Time) : nat :=
  cumulative_delay_from B dt t1 (t2 - t1).

Definition delay_budget_le
    (B : op_delay_bounds) (dt : DelayTrace)
    (t1 t2 delta : Time) : Prop :=
  cumulative_delay B dt t1 t2 <= delta.
```

最初に証明すべき補題:

```coq
Lemma cumulative_delay_zero_len :
  forall B dt t,
    cumulative_delay B dt t t = 0.

Lemma delay_budget_monotone_delta :
  forall B dt t1 t2 d1 d2,
    delay_budget_le B dt t1 t2 d1 ->
    d1 <= d2 ->
    delay_budget_le B dt t1 t2 d2.

Lemma cumulative_delay_split :
  forall B dt t1 t2 t3,
    t1 <= t2 ->
    t2 <= t3 ->
    cumulative_delay B dt t1 t3 =
    cumulative_delay B dt t1 t2 +
    cumulative_delay B dt t2 t3.
```

---

### 4. bounded lag relation を Refinement 層に置く

対象:

* `theories/Refinement/BoundedDelayRefinement.v`

ここで初めて actual projected schedule と ideal top-`m` schedule を比較する。

```coq
From Stdlib Require Import Arith Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.TopMInterface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.TopMSchedulerBridge.
From RocqSched Require Import Multicore.Common.ValidityFacts.
From RocqSched Require Import Operational.Common.Execution.
From RocqSched Require Import Operational.Common.Projection.
From RocqSched Require Import Operational.Common.ProjectionMulticoreValidity.

Definition service_lag_le
    (m : nat) (ideal actual : Schedule) (delta : nat) : Prop :=
  forall j t,
    service_job m ideal j t <=
    service_job m actual j (t + delta).

Definition service_distance_le
    (m : nat) (s1 s2 : Schedule) (delta : nat) : Prop :=
  service_lag_le m s1 s2 delta /\
  service_lag_le m s2 s1 delta.

Record bounded_delay_projection_refinement
    (jobs : JobId -> Job)
    (m : nat)
    (ideal actual : Schedule)
    (delta : nat) : Prop := {
  bdpr_ideal_valid :
    multicore_semantic_validity jobs m ideal;
  bdpr_actual_valid :
    multicore_semantic_validity jobs m actual;
  bdpr_service_lag :
    service_lag_le m ideal actual delta;
}.
```

次に top-`m` ideal schedule との接続を置く。

```coq
Record bounded_delay_top_m_projection_refinement
    (spec : GenericTopMSchedulingAlgorithm)
    (candidates_of : CandidateSource)
    (jobs : JobId -> Job)
    (adm : admissible_cpu)
    (m : nat)
    (ex : execution m)
    (ideal : Schedule)
    (delta : nat) : Prop := {
  bdtmpr_actual_sound :
    execution_multicore_projection_sound jobs adm m ex;

  bdtmpr_ideal_top_m :
    scheduler_rel
      (top_m_algorithm_schedule spec candidates_of)
      jobs m ideal;

  bdtmpr_bounded :
    bounded_delay_projection_refinement
      jobs m ideal (project_schedule (ex_trace ex)) delta;
}.
```

最初の public theorem は、強い解析定理ではなく、境界を取り出す theorem でよい。

```coq
Lemma bounded_delay_top_m_actual_semantic_validity :
  forall spec candidates_of jobs adm m ex ideal delta,
    bounded_delay_top_m_projection_refinement
      spec candidates_of jobs adm m ex ideal delta ->
    multicore_semantic_validity
      jobs m (project_schedule (ex_trace ex)).

Lemma bounded_delay_top_m_ideal_semantic_validity :
  forall spec candidates_of jobs adm m ex ideal delta,
    bounded_delay_top_m_projection_refinement
      spec candidates_of jobs adm m ex ideal delta ->
    multicore_semantic_validity jobs m ideal.

Lemma service_lag_monotone_delta :
  forall m ideal actual d1 d2,
    service_lag_le m ideal actual d1 ->
    d1 <= d2 ->
    service_lag_le m ideal actual d2.
```

---

### 5. zero-delay special case を弱い形で入れる

「zero-delay なら CPU-wise exact schedule equality」と言うのは強すぎる。global scheduling では CPU permutation や migration があるためである。

最初は service equality までにするのがよい。

```coq
Lemma service_distance_zero_implies_service_eq :
  forall m s1 s2,
    service_distance_le m s1 s2 0 ->
    forall j t,
      service_job m s1 j t = service_job m s2 j t.
```

後で CPU-wise equality が必要なら、別途

```text
same running set at every time
```

を追加すればよい。

---

### 6. 小さい example を追加する

対象:

* `theories/Examples/OperationalDelayExamples.v`

入れる例:

* delay source の合計
* zero delay budget
* dispatch delay だけを持つ trace
* `service_lag_le` の単調性
* `bounded_delay_projection_refinement` の最小例

---

## TODO リスト

* [ ] `Operational/Common/LabeledExecution.v` を追加する
* [ ] `labeled_execution` を定義する
* [ ] `labeled_to_execution` を定義する
* [ ] `Operational/Common/DelayModel.v` を追加する
* [ ] `op_delay_source` を定義する
* [ ] `op_delay_bounds` を定義する
* [ ] `default_event_delay_sources` を定義する
* [ ] `Operational/Common/DelayBudget.v` を追加する
* [ ] `DelayTrace` を定義する
* [ ] `cumulative_delay` を定義する
* [ ] `delay_budget_monotone_delta` を証明する
* [ ] `cumulative_delay_split` を証明する
* [ ] `Refinement/BoundedDelayRefinement.v` を追加する
* [ ] `service_lag_le` を定義する
* [ ] `bounded_delay_projection_refinement` を定義する
* [ ] `bounded_delay_top_m_projection_refinement` を定義する
* [ ] actual / ideal semantic validity の取り出し lemma を証明する
* [ ] `service_lag_monotone_delta` を証明する
* [ ] `service_distance_zero_implies_service_eq` を証明する
* [ ] `Examples/OperationalDelayExamples.v` を追加する
* [ ] `_CoqProject` を更新する
* [ ] `OperationalEntryPoints.v` を更新する
* [ ] `roadmap.md` / `what_to_prove.md` の古い immediate task 表記を同期する
* [ ] `design/Operational.md` / `design/Refinement.md` に delay boundary を追記する

---

## 完了条件

このタスクは、少なくとも次の定義と補題が通った時点で完了である。

```coq
labeled_to_execution :
  forall {m}, labeled_execution m -> execution m.

cumulative_delay_split :
  forall B dt t1 t2 t3,
    t1 <= t2 ->
    t2 <= t3 ->
    cumulative_delay B dt t1 t3 =
    cumulative_delay B dt t1 t2 +
    cumulative_delay B dt t2 t3.

service_lag_monotone_delta :
  forall m ideal actual d1 d2,
    service_lag_le m ideal actual d1 ->
    d1 <= d2 ->
    service_lag_le m ideal actual d2.

bounded_delay_top_m_actual_semantic_validity :
  forall spec candidates_of jobs adm m ex ideal delta,
    bounded_delay_top_m_projection_refinement
      spec candidates_of jobs adm m ex ideal delta ->
    multicore_semantic_validity
      jobs m (project_schedule (ex_trace ex)).
```

---

## 次の次に進むこと

この boundary ができた後で、初めて次に進むべきである。

```text
Awkernel scheduler behavior
  -> labeled operational execution
  -> delay source trace
  -> delay budget <= δ
  -> bounded_delay_top_m_projection_refinement
```

つまり、今回の次タスクは **bounded-delay refinement theorem の本体**ではなく、**bounded-delay refinement theorem を述べるための共通 obligation interface** である。
