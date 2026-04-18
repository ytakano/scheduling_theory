# Roadmap: Phase D

## D-1. top-`m` の public semantic boundary を固定

**実装ファイル**

* `theories/Multicore/Common/MultiCoreBase.v`
* `theories/Multicore/Common/TopMAdmissibilityBridge.v`
* `theories/Multicore/Common/AdmissibleCandidateSource.v`
* `theories/Multicore/Global/GlobalEntryPoints.v`

**TODO**

* `running_set_at` を明示定義する
* `top_m_selected_from` に相当する set-level predicate を追加する
* `admissible` と `candidate source` の依存方向を固定する
* global EDF / LLF がこの predicate を満たすことを wrapper theorem として出す
* public theorem と helper lemma を分離する

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

## D-3. optional common entry point を作る

**新規ファイル**

* `theories/Multicore/Common/MulticoreSemanticsEntryPoints.v`

**Status: Not required for D-2**

**候補**

* `MultiCoreBase`
* `Admissibility`
* `AdmissibleCandidateSource`
* `TopMAdmissibilityBridge`
* `ServiceFacts`
* `CompletionFacts`
* `RemainingCostFacts`
* `LaxityFacts`
  を再 export する

**狙い**
Phase H/J から D の public boundary を 1 import で使いたくなった時の
任意の packaging とする。D-2 完了条件には含めない。
