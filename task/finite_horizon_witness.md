# Next Task Plan: finite-horizon witness API の共通化と安定化

## 目的

`Sporadic` と `JitteredPeriodic` に存在する finite-horizon witness ベースの API を共通化し、
task-generation layer の公開インタフェースを安定化する。
これにより、以後の EDF / LLF / partitioned / analysis hook を薄い wrapper で追加できる状態にする。

---

## 現状認識

現状では以下が成立している。

- `Periodic` は `PeriodicFiniteHorizonCodec` による自動列挙経路を持つ
- `Sporadic` は manual witness による有限 horizon API を持つ
- `JitteredPeriodic` も manual witness による有限 horizon API を持つ
- EDF / LLF / partitioned への lift は既にある

しかし、以下の重複がある。

- witness record の構造が `SporadicEnumeration.v` と `JitteredPeriodicEnumeration.v` で重複している
- witness から `CandidateSourceSpec` を作る層が sporadic 側だけ独立ファイル化されている
- finite-optimality lift の witness 版が task model ごとにほぼ同型で並んでいる

したがって、次の一手は analysis を増やすことではなく、
**witness abstraction を共通 API として切り出すこと** である。

---

## 実装方針

### 1. 共通 witness record を導入する

新規ファイルを追加する。

- `theories/TaskModels/Common/FiniteHorizonWitness.v`

ここで、任意の jobset predicate `J : JobId -> Prop` に対する
有限列挙 witness を定義する。

Rocq スケルトンは次である。

```coq
Record FiniteHorizonWitness
    (J : JobId -> Prop) : Type := mkFiniteHorizonWitness {
  witness_enumJ : list JobId;
  witness_enum_complete :
    forall j, J j -> In j witness_enumJ;
  witness_enum_sound :
    forall j, In j witness_enumJ -> J j
}.
```

この record は task model 非依存にする。

---

### 2. witness から candidate source を作る共通 helper を導入する

新規ファイルを追加する。

- `theories/TaskModels/Common/WitnessCandidates.v`

ここで以下を定義する。

- `witness_candidates_of`
- `witness_candidates_spec`

Rocq スケルトンは次である。

```coq
Definition witness_candidates_of
    (J : JobId -> Prop)
    (w : FiniteHorizonWitness J)
    : CandidateSource :=
  enum_candidates_of (witness_enumJ J w).

Lemma witness_candidates_spec :
  forall J (w : FiniteHorizonWitness J),
    CandidateSourceSpec J (witness_candidates_of J w).
```

これにより、sporadic 専用の `SporadicWitnessCandidates.v` を薄い alias 層へ落とせる。

---

### 3. sporadic witness API を共通層の特殊化として再定義する

更新対象ファイルは次である。

- `theories/TaskModels/Sporadic/SporadicEnumeration.v`
- `theories/TaskModels/Sporadic/SporadicWitnessCandidates.v`
- `theories/TaskModels/Sporadic/SporadicFiniteOptimalityLift.v`
- `theories/TaskModels/Sporadic/SporadicEDFBridge.v`
- `theories/TaskModels/Sporadic/SporadicLLFBridge.v`
- `theories/TaskModels/Sporadic/SporadicPartitionedFiniteOptimalityLift.v`

方針は次である。

- `SporadicFiniteHorizonWitness` を新 record で再定義するのではなく、
  `Definition` もしくは薄い wrapper にして `FiniteHorizonWitness` へ寄せる
- `sporadic_witness_candidates_of` は `witness_candidates_of` の特殊化にする
- `sporadic_witness_candidates_spec` は共通補題の特殊化にする
- `..._with_witness` 系定理は witness 展開に依存しない形へ整理する

目標は、sporadic 層を「task-model specific predicate」と
「thin wrapper」だけにすることである。

---

### 4. jittered periodic witness API も同様に共通層へ寄せる

更新対象ファイルは次である。

- `theories/TaskModels/Jitter/JitteredPeriodicEnumeration.v`
- `theories/TaskModels/Jitter/JitteredPeriodicFiniteOptimalityLift.v`
- `theories/TaskModels/Jitter/JitteredPeriodicEDFBridge.v`
- `theories/TaskModels/Jitter/JitteredPeriodicLLFBridge.v`
- `theories/TaskModels/Jitter/JitteredPeriodicPartitionedFiniteOptimalityLift.v`

ここでは特に、jitter 側に sporadic 側と対称な helper 層がないため、
公開 API をそろえることが重要である。

必要なら新規に追加する。

- `theories/TaskModels/Jitter/JitteredPeriodicWitnessCandidates.v`

ただし、共通 `WitnessCandidates.v` だけで十分なら追加不要である。

---

### 5. finite-optimality witness lift 自体も共通化する

新規ファイル候補は次である。

- `theories/TaskModels/Common/WitnessFiniteOptimalityLift.v`

ここでは、jobset predicate `J`、その bool reflection、witness を受けて、
既存の uniprocessor finite-optimality theorem を適用する共通 theorem を置く。

スケルトンは概ね次である。

```coq
Theorem witness_finite_optimality_lift :
  forall (J : JobId -> Prop)
         (J_bool : JobId -> bool)
         (w : FiniteHorizonWitness J)
         (local_scheduler : CandidateSource -> Scheduler)
         ...
```

これが入ると、

- `SporadicFiniteOptimalityLift.v`
- `JitteredPeriodicFiniteOptimalityLift.v`

は bool-spec と predicate を渡すだけの薄い wrapper になる。

これは API 安定化の本体である。

---

## TODO

- [ ] `theories/TaskModels/Common/FiniteHorizonWitness.v` を追加する
- [ ] `theories/TaskModels/Common/WitnessCandidates.v` を追加する
- [ ] sporadic の witness record を共通 witness に寄せる
- [ ] sporadic の candidate helper を共通化する
- [ ] jittered periodic の witness record を共通 witness に寄せる
- [ ] jittered periodic の candidate helper を共通化する
- [ ] `WitnessFiniteOptimalityLift.v` を追加し、sporadic/jitter の witness lift を共通化する
- [ ] EDF / LLF / partitioned wrapper が依然として薄い wrapper だけで通ることを確認する
- [ ] example ファイルが新 API で自然に書けることを確認する
- [ ] `plan/roadmap.md` と `plan/what_to_prove.md` を「witness API stabilized」に更新する

---

## 完了条件

次の状態になれば完了である。

1. `Sporadic` と `JitteredPeriodic` の witness record 定義が共通抽象に乗る
2. witness → candidate source → finite-optimality lift の流れが task-model 共通になる
3. EDF / LLF / partitioned の各 bridge が task-model 固有部分だけを持つ薄い wrapper になる
4. example が新 API でそのまま書ける
5. roadmap / proof inventory にも共通 witness 層が明記される
