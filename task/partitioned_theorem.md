# Phase C: partitioned multicore の theorem layer completion

**partitioned 層を「定義はある」状態から、「再利用可能な定理ライブラリ」として安定化すること**。

---

## 実装Plan

### 1. partitioned theorem inventory の明文化
まず、partitioned 層で既に揃っている定理と、未整備の定理を分離する。

**対象ファイル**
- `plan/what_to_prove.md`
- `plan/roadmap.md`

**やること**
- `Lv.5 Partitioned` を以下に分解して明記する
  - local witness → global schedule
  - local schedulable_by_on → partitioned schedulable_by_on
  - service localization
  - policy wrappers
  - finite-optimality-based lift
- `EDF/LLF は local feasible → partitioned schedulable_by_on まである`
- `FIFO/RR は wrapper はあるが finite-optimality lift は未整備`
- 次に追加すべき定理を「delay-aware partitioned analysis の前提」として列挙する

---

### 2. policy wrapper の共通パターンをさらに固定化
現状でも `PartitionedPolicyLift.v` で共通化は進んでいるが、wrapper file ごとの記述パターンはまだかなり似通っている。
ここをもう一段整理し、policy file を「定義 + policy 名付き theorem 再公開」に寄せる。

**対象ファイル**
- `theories/Multicore/Partitioned/Policies/PartitionedPolicyLift.v`
- `theories/Multicore/Partitioned/Policies/PartitionedEDF.v`
- `theories/Multicore/Partitioned/Policies/PartitionedLLF.v`
- `theories/Multicore/Partitioned/Policies/PartitionedFIFO.v`
- `theories/Multicore/Partitioned/Policies/PartitionedRR.v`

**やること**
- generic theorem の naming を固定する
- 各 wrapper file では
  - `partitioned_*_scheduler`
  - local witness lift
  - local schedulable lift
  - 必要なら finite-optimality lift
  だけを薄く公開する構成に寄せる
- EDF/LLF と FIFO/RR の差分を「定理の欠如」で表し、wrapper 構造自体は揃える

---

### 3. partitioned finite-optimality lift の責務を明文化
`PartitionedFiniteOptimalityLift.v` はかなり重要な抽象層である。
ここを今のうちに「何を仮定し、何を返す generic theorem か」で固定しておくべきである。

**対象ファイル**
- `theories/Multicore/Partitioned/Policies/PartitionedFiniteOptimalityLift.v`

**やること**
- theorem header/comment を整理する
- `local_scheduler = single_cpu_algorithm_schedule spec`
- local finite optimality theorem
- `enum_local_candidates_of`
- local feasible_on
から global partitioned schedulability を得る、という責務を明示する
- 将来の policy 追加時に、ここへ載る条件をコメントで固定する

---

### 4. partitioned major result 用の利用例を 1 本追加
理論層が揃っていても、入口定理の使い方が見えにくい。
そのため、**partitioned が multicore の最初の major result である**ことを示すサンプルを 1 本置く価値が高い。

**対象ファイル候補**
- `theories/Examples/AffinityExamples.v`
- または新規 `theories/Examples/PartitionedExamples.v`

**やること**
- assignment
- local candidate source
- per-CPU feasible assumption
- partitioned EDF or LLF schedulability conclusion
の流れを 1 つの例にする

---

## TODO リスト

- [ ] `plan/what_to_prove.md` の `Lv.5 Partitioned` を現状コードに合わせて更新する
- [ ] `plan/roadmap.md` の Phase C を「wrapper 実装済み / theorem layer 整備中」として明確化する
- [ ] `PartitionedPolicyLift.v` の共通 pattern を再点検し、wrapper file の責務を薄くする
- [ ] `PartitionedEDF.v` と `PartitionedLLF.v` の finite-optimality lift の位置づけをコメントで固定する
- [ ] `PartitionedFIFO.v` と `PartitionedRR.v` は「wrapper-only」であることを明示する
- [ ] `PartitionedFiniteOptimalityLift.v` に policy 追加時の必要仮定を明記する
- [ ] partitioned major result を示す example を 1 本追加する

---

## 実装ファイル名

優先度順に触るべきファイルは以下である。

1. `plan/what_to_prove.md`
2. `plan/roadmap.md`
3. `theories/Multicore/Partitioned/Policies/PartitionedPolicyLift.v`
4. `theories/Multicore/Partitioned/Policies/PartitionedFiniteOptimalityLift.v`
5. `theories/Multicore/Partitioned/Policies/PartitionedEDF.v`
6. `theories/Multicore/Partitioned/Policies/PartitionedLLF.v`
7. `theories/Multicore/Partitioned/Policies/PartitionedFIFO.v`
8. `theories/Multicore/Partitioned/Policies/PartitionedRR.v`
9. `theories/Examples/PartitionedExamples.v`（新規候補）

---

## Rocq スケルトン案

`PartitionedPolicyLift.v` 側で、wrapper の責務をさらに固定するなら、例えば次のような補助定理の形に寄せるとよい。

```coq
Theorem mk_partitioned_policy_schedulable_by_on_intro :
  forall (local_scheduler : CandidateSource -> Scheduler)
         (spec : GenericSchedulingAlgorithm),
    (forall cands,
       local_scheduler cands =
       single_cpu_algorithm_schedule spec cands) ->
    forall (assign : JobId -> CPU) (m : nat)
           (valid_assignment : forall j, assign j < m)
           (J : JobId -> Prop)
           (cands : CPU -> CandidateSource)
           (cands_spec : forall c, c < m ->
             CandidateSourceSpec (local_jobset assign J c) (cands c))
           (jobs : JobId -> Job),
      (forall c, c < m ->
        schedulable_by_on
          (local_jobset assign J c)
          (local_scheduler (cands c))
          jobs 1) ->
      schedulable_by_on
        J
        (partitioned_scheduler m spec cands)
        jobs m.
```

finite-optimality lift の入口条件も、コメント上は次の形で固定しておくとよい。

```coq
(* Required policy-side obligations for partitioned finite lift:
   1. local scheduler is definitionally [single_cpu_algorithm_schedule spec]
   2. local finite-job optimality theorem is available
   3. enumJ sound/complete for the global finite job set
   4. each local projected job set is feasible on one CPU
*)
```
