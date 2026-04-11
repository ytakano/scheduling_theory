# Plan

これは、[toward_llf_optimality.md](toward_llf_optimality.md)中にある、「先にやると得なリファクタリング」のタスクです。

## Goal

LLF optimality の前に、EDF 側にある「終盤の橋渡し部分」と「prefix 安定性部分」を共通化し、

* EDF と LLF が同じ canonicalization 骨格を共有できる
* `LLFLemmas.v` / `LLFOptimality.v` を短く書ける
* 今後 FIFO / RR / 他の metric-based policy にも流用できる

状態にする。

---

# Phase 1. `choose_*_agrees_before` の共通層を分離する

## 1-1. 新しい共通ファイルを作る

新規ファイル案:

* `theories/UniPolicies/MetricChooserLemmas.v`

ここに、EDF/LLF 共通で使う prefix 安定性補題を置く。

### このファイルに入れるもの

まずは次の 2 つ。

#### A. `candidates_of_agrees_before`

今は `EDFLemmas.v` にあるが、EDF 固有ではないので共通層へ移す。

```coq
Lemma candidates_of_agrees_before :
  forall J candidates_of
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs s1 s2 t,
    agrees_before s1 s2 t ->
    candidates_of jobs 1 s1 t = candidates_of jobs 1 s2 t.
```

#### B. metric chooser の wrapper

`MetricChooser.v` にすでにある

* `choose_min_metric_agrees_before`

を、そのまま policy-specific wrapper から使えるようにする。

ここでは新しい大きな補題を作る必要はなく、**wrapper を置く場所を整理する**だけでよい。

---

## 1-2. EDF 側 wrapper を薄くする

`EDFLemmas.v` では次だけを残す。

* `choose_edf_agrees_before`
* `edf_dispatch_agrees_before`

ただし、`candidates_of_agrees_before` は新共通ファイルから import する。

### 目標

`EDFLemmas.v` を

* EDF 固有の canonical 定義
* EDF 固有の priority violation
* EDF 固有の抽出補題

だけに近づける。

---

## 1-3. LLF 側 wrapper を追加する

新規ファイル案:

* `theories/UniPolicies/LLFLemmas.v`

まずはこの最小セットを入れる。

```coq
Lemma choose_llf_agrees_before :
  forall jobs s1 s2 t candidates,
    agrees_before s1 s2 t ->
    choose_llf jobs 1 s1 t candidates =
    choose_llf jobs 1 s2 t candidates.
```

```coq
Lemma llf_dispatch_agrees_before :
  forall J candidates_of
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs s1 s2 t,
    agrees_before s1 s2 t ->
    dispatch llf_generic_spec jobs 1 s1 t (candidates_of jobs 1 s1 t) =
    dispatch llf_generic_spec jobs 1 s2 t (candidates_of jobs 1 s2 t).
```

これで EDF/LLF 両方が同じ prefix 安定性の形になります。

---

## 1-4. 必要なら prefix 補題を追加する

この段階で、LLF canonicalization で必要になりそうなら `SchedulePrefix.v` に次を追加する。

* `agrees_before_remaining_cost`
* `agrees_before_laxity`

`choose_llf_agrees_before` 自体は `choose_min_metric_agrees_before` で足りますが、
後で LLF repair 証明を書くとき、`laxity` を prefix agreement で書き換えたくなるので、ここで入れておくと楽です。

---

# Phase 2. `canonical + idle -> scheduler_rel` を generic 化する

## 2-1. generic 補題の置き場所を決める

おすすめは新規ファイルです。

* `theories/SchedulingAlgorithmCanonicalBridge.v`

理由は、この補題は EDF/LLF 固有ではなく、

* `GenericSchedulingAlgorithm`
* `CandidateSource`
* `single_cpu_algorithm_schedule`

に関する bridge だからです。

`SchedulingAlgorithmSchedulerBridge.v` に足してもよいですが、
canonicalization 由来の補題群として分けた方が見通しが良いです。

---

## 2-2. generic canonical predicate を定義する

EDF 版では `matches_choose_edf_before` が使われていますが、これを generic にします。

追加する定義案:

```coq
Definition matches_dispatch_at_with
    (alg : GenericSchedulingAlgorithm)
    (jobs : JobId -> Job)
    (candidates_of : CandidateSource)
    (sched : Schedule)
    (t : Time) : Prop :=
  sched t 0 = dispatch alg jobs 1 sched t (candidates_of jobs 1 sched t).
```

```coq
Definition matches_dispatch_before
    (alg : GenericSchedulingAlgorithm)
    (jobs : JobId -> Job)
    (candidates_of : CandidateSource)
    (sched : Schedule)
    (H : Time) : Prop :=
  forall t, t < H ->
    matches_dispatch_at_with alg jobs candidates_of sched t.
```

これで EDF/LLF 固有の `matches_choose_*` は thin wrapper にできます。

---

## 2-3. generic bridge 補題を作る

EDF 専用の `canonical_and_idle_implies_scheduler_rel` を一般化します。

狙う statement はこれです。

```coq
Lemma canonical_and_idle_implies_scheduler_rel_generic :
  forall alg J enumJ candidates_of
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched,
    (forall j, J j -> In j enumJ) ->
    valid_schedule jobs 1 sched ->
    feasible_schedule_on J jobs 1 sched ->
    single_cpu_only sched ->
    matches_dispatch_before alg jobs candidates_of sched (deadline_horizon jobs enumJ) ->
    (forall t, deadline_horizon jobs enumJ <= t -> sched t 0 = None) ->
    scheduler_rel (single_cpu_algorithm_schedule alg candidates_of) jobs 1 sched.
```

### 証明方針

EDF 版とほぼ同じです。

* `t < H` なら canonical 仮定から一致
* `t >= H` なら idle 仮定で `sched t 0 = None`
* あとは `choose = None` を示すため、
  `cand_spec` と `feasible_schedule_on` から horizon 以後に `J` job は eligible でないことを使う

この最後の部分は EDF 特有ではなく、job deadline に関する一般事実なのでそのまま generic にできます。

---

## 2-4. EDF 側を generic bridge 利用に置き換える

`EDFOptimality.v` の既存補題

* `canonical_and_idle_implies_scheduler_rel`

は削除するか、thin wrapper に置き換える。

例えば:

```coq
Lemma canonical_and_idle_implies_scheduler_rel :
  ...
Proof.
  eapply canonical_and_idle_implies_scheduler_rel_generic; ...
Qed.
```

これで既存 theorem への影響を最小化できます。

---

## 2-5. EDF の canonical predicate も thin wrapper 化する

将来 LLF と形を揃えるために、EDF 側の

* `matches_choose_edf_at_with`
* `matches_choose_edf_before`

も、generic 定義の wrapper として書き直すとよいです。

---

# Phase 3. 依存関係を整理してコンパイルを安定化する

## 3-1. import の整理

共通化後の依存は次のようにするのがよいです。

### `MetricChooserLemmas.v`

依存:

* `SchedulePrefix`
* `SchedulingAlgorithmInterface`
* `MetricChooser`
* `SchedulingAlgorithmSchedulerBridge` まわり

### `EDFLemmas.v`

依存:

* `MetricChooserLemmas`
* `EDF`
* EDF 固有定義

### `LLFLemmas.v`

依存:

* `MetricChooserLemmas`
* `LLF`

### `SchedulingAlgorithmCanonicalBridge.v`

依存:

* `ScheduleModel`
* `SchedulePrefix`
* `SchedulingAlgorithmInterface`
* `SchedulingAlgorithmSchedulerBridge`
* `SchedulerInterface`
* `SchedulerValidity`
* generic canonical predicate

---

## 3-2. 既存定理が壊れないことを確認

この段階では LLF optimality にはまだ入らず、まず次だけを通す。

* `EDFLemmas.v`
* `EDFOptimality.v`

つまり、**EDF の既存最適性証明がそのまま通る状態**を最初の完了条件にする。

---

# Phase 4. LLF 側の受け皿を作る

共通化が終わったら、LLF 側はかなり短く書けます。

## 4-1. `LLFLemmas.v` に canonical 定義を追加

最低限入れるもの:

* `matches_choose_llf_at_with`
* `matches_choose_llf_before`
* `is_llf_canonical_at_b` と iff 補題
* `choose_llf_agrees_before`
* `llf_dispatch_agrees_before`

ただし `matches_choose_llf_*` は、できれば generic predicate の wrapper にする。

---

## 4-2. LLF optimality のための足場を作る

この時点で、LLF 側は

* prefix 安定性
* generic bridge
  を再利用できるので、残りは LLF 固有の repair layer だけになる。

つまり、LLF optimality の難所を
**“swap / repair のみ”**
に局所化できます。

---

# 実行順

## Step 1

`MetricChooserLemmas.v` 新設
`candidates_of_agrees_before` を移す。

## Step 2

`EDFLemmas.v` を軽量化
`choose_edf_agrees_before` と `edf_dispatch_agrees_before` だけ残す。

## Step 3

`LLFLemmas.v` 新設
`choose_llf_agrees_before` / `llf_dispatch_agrees_before` を追加。

## Step 4

`SchedulingAlgorithmCanonicalBridge.v` 新設
generic canonical predicate と generic bridge 補題を追加。

## Step 5

`EDFOptimality.v` を generic bridge 使用に差し替える。
EDF の既存最適性が通ることを確認。

## Step 6

EDF/LLF の `matches_choose_*` を wrapper 化して、canonicalization 層の API を揃える。

---

# 完了条件

この refactoring が完了したと言える条件は次です。

1. `candidates_of_agrees_before` が EDF 専用ファイルから外れている
2. `choose_edf_agrees_before` と `choose_llf_agrees_before` が同じ構造で並ぶ
3. `canonical_and_idle_implies_scheduler_rel` が generic 補題へ集約されている
4. `EDFOptimality.v` がその generic 補題で通る
5. LLF 側で canonical / normalization の骨格を書き始められる

---

# この Plan の狙い

この順にやると、

* 先に EDF を壊さずに共通化できる
* LLF 側では prefix/canonical/bridge を新規実装しなくてよくなる
* 残る難所が「LLF repair 補題」に限定される

ので、LLF optimality への最短経路になります。
