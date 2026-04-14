# Next Task Plan: Stabilize the sporadic witness-based finite-horizon layer

## Goal

sporadic finite-horizon 層を「実装済み」ではなく「build に正しく載った再利用可能な公開層」にすることである。
特に、manual witness を使う API を整理し、EDF / LLF / partitioned lift からの利用を簡潔にする。

## Why this next

- `_CoqProject` から `theories/TaskModels/Sporadic/SporadicEnumeration.v` が漏れている
- 現状の sporadic layer は理論上は揃っているが、manifest と API の両面で統合が甘い
- この不整合を放置したまま Phase C / D に進むと、後で import 構造と theorem entry point をやり直すことになる

## Target files

- `_CoqProject`
- `theories/TaskModels/Sporadic/SporadicEnumeration.v`
- `theories/TaskModels/Sporadic/SporadicFiniteOptimalityLift.v`
- `theories/TaskModels/Sporadic/SporadicEDFBridge.v`
- `theories/TaskModels/Sporadic/SporadicLLFBridge.v`
- `theories/TaskModels/Sporadic/SporadicPartitionedFiniteOptimalityLift.v`
- `theories/Examples/SporadicExamples.v`

新規追加候補:
- `theories/TaskModels/Sporadic/SporadicWitnessCandidates.v`

## TODO

- [ ] `_CoqProject` に `theories/TaskModels/Sporadic/SporadicEnumeration.v` を追加する
- [ ] sporadic witness から `CandidateSource` を作る薄い helper 層を追加する
- [ ] witness から得た candidate source が `sporadic_jobset_upto` に対して sound/complete であることを補題化する
- [ ] `SporadicFiniteOptimalityLift.v` を helper 経由に整理し、`enum_candidates_of (sporadic_enumJ ...)` の直書きを減らす
- [ ] EDF / LLF / partitioned bridge を同じ witness API で揃える
- [ ] `Examples/SporadicExamples.v` を新 API に合わせて簡約する
- [ ] build 再生成後に import 閉包が崩れていないことを確認する

## Concrete implementation steps

### 1. Build graph fix

`_CoqProject` に次を追加する。

```text
theories/TaskModels/Sporadic/SporadicEnumeration.v
```

helper file を切る場合はそれも追加する。

```text
theories/TaskModels/Sporadic/SporadicWitnessCandidates.v
```

### 2. Witness-to-candidate helper を導入する

`SporadicEnumeration.v` は witness record のみを保ち、
`EnumCandidates` 依存は新規 `SporadicWitnessCandidates.v` に分離するのがよい。

想定スケルトンは以下である。

```coq
From Stdlib Require Import List.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.EnumCandidates.
From RocqSched Require Import TaskModels.Sporadic.SporadicFiniteHorizon.
From RocqSched Require Import TaskModels.Sporadic.SporadicEnumeration.

Definition sporadic_witness_candidates_of
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (jobs : JobId -> Job)
    (H : Time)
    (w : SporadicFiniteHorizonWitness T tasks jobs H)
    : CandidateSource :=
  enum_candidates_of (sporadic_enumJ T tasks jobs H w).

Lemma sporadic_witness_candidates_spec :
  forall T tasks jobs H
         (w : SporadicFiniteHorizonWitness T tasks jobs H),
    CandidateSourceSpec
      (sporadic_jobset_upto T tasks jobs H)
      (sporadic_witness_candidates_of T tasks jobs H w).
Proof.
  intros.
  unfold sporadic_witness_candidates_of.
  apply enum_candidates_spec.
  - exact (sporadic_enum_complete T tasks jobs H w).
  - exact (sporadic_enum_sound T tasks jobs H w).
Qed.
```

## 3. Finite-optimality lift を helper API に寄せる

`SporadicFiniteOptimalityLift.v` の witness 版定理は、
内部で `sporadic_enumJ ...` を直接展開するのではなく helper を使う形に寄せる。

目標形は以下である。

```coq
Theorem sporadic_finite_optimality_lift_with_witness :
  forall (local_scheduler : CandidateSource -> Scheduler)
         ...
         (w : SporadicFiniteHorizonWitness T tasks jobs H),
    ... ->
    schedulable_by_on
      (sporadic_jobset_upto T tasks jobs H)
      (local_scheduler (sporadic_witness_candidates_of T tasks jobs H w))
      jobs 1.
```

これにより EDF / LLF / partitioned 側が同じ witness entry point を共有できる。

## 4. Bridge files を統一する

以下の各ファイルでは、`enum_candidates_of (sporadic_enumJ ...)` を直接書かず、
helper API のみを使うように揃える。

- `SporadicEDFBridge.v`
- `SporadicLLFBridge.v`
- `SporadicPartitionedFiniteOptimalityLift.v`

これにより sporadic witness abstraction の境界が明確になる。

## 5. Example を API regression test にする

`Examples/SporadicExamples.v` は単なる利用例ではなく、
sporadic witness API の end-to-end regression test として使う。

最低限、以下を維持する。

- witness から EDF schedulable を導く例
- witness から LLF schedulable を導く例
- witness から partitioned schedulable を導く例

## Definition of done

- `_CoqProject` に sporadic witness 関連ファイルが正しく登録されている
- sporadic witness から candidate source を作る helper が存在する
- sporadic finite-optimality / EDF / LLF / partitioned bridge が同じ helper API を使う
- `Examples/SporadicExamples.v` がその API で通る
- sporadic layer を「witness-based finite-horizon public API」として説明できる状態になる
