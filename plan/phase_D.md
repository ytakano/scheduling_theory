# Roadmap: Phase D

## D-1. top-`m` の public semantic boundary を固定

**実装ファイル**

* `theories/Multicore/Common/MultiCoreBase.v`
* `theories/Multicore/Common/TopMAdmissibilityBridge.v`
* `theories/Multicore/Common/AdmissibleCandidateSource.v`
* `theories/Multicore/Global/GlobalEntryPoints.v`

**Status: Implemented**

**実装済み inventory**

* `MultiCoreBase.v` に `running_set_at` / `machine_full_at` /
  `subset_eligible_at` / `subset_admissible_somewhere_at` を追加
* `TopMAdmissibilityBridge.v` に
  `top_m_selected_from` を public な set-level boundary として追加
* `AdmissibleCandidateSource.v` に
  `AdmissibleCandidateSourceSpec` /
  `StrongAdmissibleCandidateSourceSpec` を置き、
  admissibility と candidate source の依存方向を固定
* `TopMAdmissibilityBridge.v` で public theorem と internal helper lemma を分離
* `GlobalEDF.v` / `GlobalLLF.v` に
  `top_m_selected_from` を満たす thin wrapper theorem を追加
* `GlobalEntryPoints.v` が stable downstream import として
  top-`m` theorem inventory を再 export

**狙い**
現状は top-`m` が scheduler bridge と lemma 群に散っている。
ここで **「ある時刻の running 集合が ready 集合の top-`m` である」** を policy-generic に固定する。

## D-2. multicore semantic invariant を追加

**実装ファイル**

* `theories/Multicore/Common/ServiceFacts.v`
* `theories/Multicore/Common/CompletionFacts.v`
* `theories/Multicore/Common/RemainingCostFacts.v`
* `theories/Multicore/Common/LaxityFacts.v`

**Status: Implemented**

**実装済み inventory**

* `ServiceFacts.v` に machine supply の semantic 定義と基本補題を移設
* `service_sum_on_cpus_monotone`
* `machine_full_at_implies_total_cpu_service_at_eq_m`
* ready/eligible だが non-running な job から `machine_full_at` を出す標準補題
* admissibility-aware な parallel 補題
* `remaining_cost_step_bounds_mc`
* `remaining_cost_monotone_mc`
* `laxity_step_bounds_mc`
* fairness client 向け `Public downstream theorems in this file:` inventory comment

**狙い**
Phase H/J で operational trace を abstract schedule に射影した後、すぐ D 側の theorem を使えるようにする。

## D-3. common semantics entry point を作る

**新規ファイル**

* `theories/Multicore/Common/MulticoreSemanticsEntryPoints.v`

**Status: Implemented**

**実装済み inventory**

* `MultiCoreBase`
* `Admissibility`
* `AdmissibleCandidateSource`
* `TopMAdmissibilityBridge`
* `ServiceFacts`
* `CompletionFacts`
* `RemainingCostFacts`
* `LaxityFacts`
  を common semantic boundary として再 export する

**位置づけ**

* policy-independent な multicore semantic theorem layer の canonical import
* `GlobalEntryPoints.v` や `PartitionedEntryPoints.v` の代替ではなく、
  その下にある common boundary を 1 import で使うための packaging

**狙い**
Phase H/J や downstream client から D の public boundary を
1 import で使えるようにし、global / partitioned policy wrapper import と
policy-independent multicore semantics import を分離する。

## 現時点の残作業

* multicore validity を current minimal base からどう拡張するかを整理する
* migration-aware な fairness / interference-facing 補題を強化する
* richer affinity / candidate-source instantiation examples を足す
* top-`m` set-level boundary の上に置く次段の generic abstraction を見極める
