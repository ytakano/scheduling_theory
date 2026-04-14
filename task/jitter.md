# Phase B-3 の前半として release jitter layer を追加

具体的には、`Schedule` を汚さずに、既存の periodic / sporadic / finite-horizon / EDF・LLF・partitioned の流れへ接続できる **jittered periodic task model** を入れる。

## 実装方針

arrival offset は periodic 側では既に `offset : TaskId -> Time` で表現済みである。
したがって今の欠落は「期待 release に対する bounded actual release」であり、まず jitter を先に入れるべきである。
また、actual release は `(task, index)` だけでは復元できないため、**codec ではなく sporadic と同じ witness-based finite-horizon API** を採るのが自然である。

## TODO

1. **共通 jitter 述語を導入する**
   実装ファイル:
   - `theories/TaskModels/Jitter/ReleaseJitter.v`

   追加内容:
   - `within_jitter nominal actual delta`
   - bool 版と reflect 補題
   - 下界・上界取り出し補題

2. **jittered periodic job model を定義する**
   実装ファイル:
   - `theories/TaskModels/Jitter/JitteredPeriodicTasks.v`

   追加内容:
   - `generated_by_jittered_periodic_task`
   - `generated_by_jittered_periodic_task_b`
   - `jittered_periodic_job_model_on`
   - 基本補題:
     - release lower/upper bound
     - deadline consistency
     - cost bound
     - `generated_by_periodic_task -> generated_by_jittered_periodic_task`

3. **sporadic bridge を張る**
   実装ファイル:
   - `theories/TaskModels/Jitter/JitteredPeriodicSporadicBridge.v`

   追加内容:
   - `generated_by_jittered_periodic_implies_sporadic`
   - `jittered_periodic_model_implies_sporadic_model`
   - uniqueness / separation 用の補助補題

4. **finite-horizon jobset を witness-based で入れる**
   実装ファイル:
   - `theories/TaskModels/Jitter/JitteredPeriodicFiniteHorizon.v`
   - `theories/TaskModels/Jitter/JitteredPeriodicEnumeration.v`

   追加内容:
   - `jittered_periodic_jobset_upto`
   - bool 版
   - `JitteredPeriodicFiniteHorizonWitness`

   方針:
   - 自動 codec は作らない
   - `enumJ` の sound/complete witness を要求する

5. **既存 finite-optimality skeleton に接続する**
   実装ファイル:
   - `theories/TaskModels/Jitter/JitteredPeriodicFiniteOptimalityLift.v`
   - `theories/TaskModels/Jitter/JitteredPeriodicEDFBridge.v`
   - `theories/TaskModels/Jitter/JitteredPeriodicLLFBridge.v`

   追加内容:
   - sporadic 側と同型の lift 定理
   - EDF/LLF の thin wrapper
   - 必要なら `JitteredPeriodicPartitionedFiniteOptimalityLift.v` も追加

6. **example を追加する**
   実装ファイル:
   - `theories/Examples/JitteredPeriodicExamples.v`

   追加内容:
   - nominal release と actual release がずれる小例
   - witness enumeration
   - EDF / LLF schedulable example
   - 可能なら 2 CPU partitioned の小例

7. **プロジェクト登録と文書を更新する**
   実装ファイル:
   - `_CoqProject`
   - `plan/roadmap.md`
   - `plan/what_to_prove.md`

## 先頭で書くべき Rocq スケルトン

```coq
(* theories/TaskModels/Jitter/ReleaseJitter.v *)
Definition within_jitter (nominal actual delta : Time) : Prop :=
  nominal <= actual /\ actual <= nominal + delta.

Definition within_jitter_b (nominal actual delta : Time) : bool :=
  Nat.leb nominal actual && Nat.leb actual (nominal + delta).
```

```coq
(* theories/TaskModels/Jitter/JitteredPeriodicTasks.v *)
Definition generated_by_jittered_periodic_task
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jitter : TaskId -> Time)
    (jobs : JobId -> Job)
    (j : JobId) : Prop :=
  let τ := job_task (jobs j) in
  let k := job_index (jobs j) in
  within_jitter
    (expected_release tasks offset τ k)
    (job_release (jobs j))
    (jitter τ) /\
  job_abs_deadline (jobs j) =
    job_release (jobs j) + task_relative_deadline (tasks τ) /\
  job_cost (jobs j) <= task_cost (tasks τ).
```

```coq
(* theories/TaskModels/Jitter/JitteredPeriodicEnumeration.v *)
Record JitteredPeriodicFiniteHorizonWitness
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset jitter : TaskId -> Time)
    (jobs : JobId -> Job)
    (H : Time) : Type := mkJitteredPeriodicFiniteHorizonWitness {
  jittered_enumJ : list JobId;
  jittered_enum_complete :
    forall j, jittered_periodic_jobset_upto T tasks offset jitter jobs H j ->
              In j jittered_enumJ;
  jittered_enum_sound :
    forall j, In j jittered_enumJ ->
              jittered_periodic_jobset_upto T tasks offset jitter jobs H j
}.
```

## 着手順

- まず `ReleaseJitter.v` と `JitteredPeriodicTasks.v`
- 次に `JitteredPeriodicSporadicBridge.v`
- その後 `FiniteHorizon` / `Enumeration`
- 最後に EDF/LLF/partitioned bridge と example
