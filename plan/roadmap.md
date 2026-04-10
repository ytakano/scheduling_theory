# ロードマップ

現在の実装では、共通基盤はすでにかなり整ってきている。
特に、

* `Task / Job / Schedule`
* `released / pending / ready / completed`
* `valid_schedule / valid_jobs`
* `service_job` とその基本補題
* periodic task 拡張に向けた Task/Job 接続の受け皿

が入っている。

したがって、今後は
**「基盤定義を増やす」段階から、「単一CPU抽象 interface を安定化し、policy ごとの局所仕様と partitioned への持ち上げを整理する」段階**
へ移っているとみなすのが自然である。

また、将来の拡張として入れたい **周期タスク** と **DAG タスク** は性質が異なる。

* **周期タスク**は主として **job 生成規則の拡張**
* **DAG タスク**は主として **job 内部構造の拡張**

である。
したがって、周期タスクは単一CPU EDF 系の延長に、DAG は multicore / global 基盤の後段に置く。

---

# 全体方針

最初から 1 本の巨大モデルで全部扱うのではなく、次の 4 層に分ける。

## 層A: 共通基盤

* Job / Task /（将来）Node
* `service_job`
* `completed / released / pending / ready`
* `valid_schedule / valid_jobs`
* deadline miss / feasibility

## 層B: 単一CPU scheduler 抽象

* chooser
* validity
* refinement
* preemptive / non-preemptive
* tie-break

## 層C: 単一CPU policy と partitioned への持ち上げ

* FIFO
* RR
* prioritized FIFO
* EDF
* per-CPU lifting
* partitioned composition

## 層D: global / OS 寄り / refinement

* global ready-set / top-`m`
* multicore work-conserving / determinism
* migration / wakeup / timer / IPI
* operational semantics
* refinement

この分け方にすると、

1. 既存の共通基盤を固定する
2. 単一CPU scheduler 抽象を安定化する
3. 単一CPU policy 群をその抽象に載せる
4. partitioned scheduling でマルチコアへ自然に持ち上げる
5. その後に global / OS モデルへ進む

という順になる。

---

# 現在地の整理

## ほぼ完了

### Phase 0. 基本設計方針
* 離散時刻 `nat`
* `CPU := nat`
* multicore schedule を前提にした `Schedule`
* Task 拡張・DAG 拡張を見据えたコメント整理

### Phase 1. 共通理論基盤
* `Task`, `Job`, `Schedule`
* `service_job`
* `released`, `pending`, `ready`, `completed`
* `valid_schedule`, `valid_jobs`
* sequential-job 制約
* `service_job` の単調性・増加性・実行との対応
* ready/completed/valid_schedule の基本補題

## 進行中

### Phase 2. 単一CPU scheduler 抽象化
単なる policy 個別実装ではなく、共通 interface の形で

* chooser
* validity
* refinement
* scheduler 固有仕様

を分離して表現する。

### Phase 3. 単一CPU policy の interface への載せ替え
対象:

* FIFO
* RR
* prioritized FIFO
* EDF

ここでは「choose が何を保証するか」を局所仕様として明示する。

### Phase 4. EDF を中心とした単一CPU補題の整理
特に:

* EDF 局所仕様
* tie-case を含む order 仕様
* `service_between` など再利用補題の切り出し
* 単一CPU trace / dispatch の共通補題化

## 次の明確な山

### Phase 5. partitioned scheduling
ここが次の主要マイルストーン。

* `assign : JobId -> CPU`
* CPU ごとの単一CPU scheduler
* global schedule への持ち上げ
* service / completion / validity の合成
* scheduler-specific lifting
  * partitioned EDF
  * partitioned RR
  * partitioned prioritized FIFO

---

# 修正版ロードマップ概要

## Phase 0. 設計方針の固定
## Phase 1. 共通理論基盤
## Phase 2. 単一CPU scheduler interface
## Phase 3. 単一CPU policy 実装の interface への統合
## Phase 4. 単一CPU 共通補題・EDF 補題の整理
## Phase 5. partitioned scheduling
## Phase 6. multicore 共通性質
## Phase 7. global scheduling interface
## Phase 8. global EDF / prioritized FIFO
## Phase 9. busy interval / interference / response-time
## Phase 10. schedulability / optimality
## Phase 11. OS 寄り multicore operational semantics
## Phase 12. refinement
## Phase 13. 発展テーマ（周期タスク / DAG タスク）

---

# Phase 0. 設計方針の固定

ここで固定する。

## 0.1 時間
* 離散時刻 `nat`

## 0.2 CPU 集合
* `CPU := nat`
* 実際には有限集合 `0 .. m-1`

## 0.3 実行単位
* 現在は job
* 将来は DAG 導入により node-level 実行へ拡張可能

## 0.4 発展方向の分離
* 周期タスク = job 生成規則の拡張
* DAG タスク = job 内部構造の拡張

---

# Phase 1. 共通理論基盤

ここはかなり実装済み。

## 1.1 基本データ
* `Task`
* `Job`
* `Schedule`

## 1.2 実行量
* `service_job`

## 1.3 状態述語
* `released`
* `pending`
* `ready`
* `completed`

## 1.4 妥当性
* `valid_schedule`
* `valid_jobs`
* sequential-job 制約

## 1.5 基本補題
* service 単調性
* 1 step 増加上界
* 実行 iff service 増加
* completed / ready の整合性
* valid schedule の基本補題

---

# Phase 2. 単一CPU scheduler interface

ここでは単一CPU scheduler の共通 interface を整える。

## 2.1 interface の役割
各 scheduler について少なくとも次を分ける。

* chooser
* validity
* refinement

## 2.2 interface が表現すべきこと
* ready 集合から次に実行すべき 1 job を選ぶ
* idle を許す条件
* non-preemptive / preemptive の差
* tie-break の方針
* policy 固有仕様を載せる拡張点

## 2.3 目標
policy ごとの「choose 関数の実装」と「正しさの命題」を分離し、
後段の partitioned lifting で再利用可能にする。

---

# Phase 3. 単一CPU policy 実装の interface への統合

対象はまず次の 4 つ。

* FIFO
* RR
* prioritized FIFO
* EDF

ここでは単なる定義だけでなく、各 policy を interface の instance / spec として整える。

## 3.1 FIFO
* queue 先頭を選ぶ
* overtaking がない
* non-preemptive 版なら current 継続

## 3.2 RR
* quantum 消費
* requeue の順序
* 巡回性

## 3.3 prioritized FIFO
* priority 尊重
* 同 priority 内 FIFO

## 3.4 EDF
* deadline 最小の ready job を選ぶ
* tie-case を含めた順序仕様

---

# Phase 4. 単一CPU 共通補題・EDF 補題の整理

ここは次の再利用のための整理フェーズ。

## 4.1 共通補題
* running → ready / pending
* choose の健全性
* no-loss
* dispatch consistency
* service と実行の対応

## 4.2 EDF 補題
* 最小 deadline 選択
* tie-case を含む respects-EDF 系仕様
* 逸脱ステップから earlier eligible job を抽出する補題
* `service_between` などの共通補題化

## 4.3 目的
EDF の個別証明に埋まっている補題を、
他 policy や partitioned でも使える形へ持ち上げる。

---

# Phase 5. partitioned scheduling

ここが次の主要マイルストーン。

## 5.1 モデル
* 各 job / task は特定 CPU に固定
* 各 CPU 上では単一CPU scheduler を使う

## 5.2 必要定義
* `assign : JobId -> CPU`
* CPU view of global schedule
* per-CPU validity
* global composition

## 5.3 証明対象
* per-CPU valid → global valid
* service が割当先 CPU の service と一致
* per-CPU completion / deadline 性質の全体への持ち上げ
* migration がないこと
* scheduler-specific lifting
  * partitioned EDF
  * partitioned RR
  * partitioned prioritized FIFO

## 5.4 意義
partitioned は単一CPU 理論を最も自然に再利用できるため、
最初の multicore 成果として最適。

---

# Phase 6. multicore 共通性質

partitioned を踏まえて multicore で一般に必要な性質を整理する。

* no-duplication
* idle / busy core
* local/global runnable notions
* multicore work-conserving
* determinism
* one-copy invariant

---

# Phase 7. global scheduling interface

ここで初めて「top-`m` を選ぶ」抽象に進む。

* global ready set
* high-level dispatch relation
* distinct selection
* CPU assignment consistency

---

# Phase 8. global EDF / prioritized FIFO

対象:

* global EDF
* global prioritized FIFO

必要なら後で:

* global FIFO
* global RR

ここでは

* top-`m` correctness
* no-duplication
* global work-conserving
* dispatch consistency

を揃える。

---

# Phase 9. busy interval / interference / response-time

ここから本格的な realtime 理論へ進む。

* partitioned response-time
* global interference 基本補題
* multicore busy interval / busy window
* tardiness / response-time bound

---

# Phase 10. schedulability / optimality

* partitioned EDF schedulability
* fixed-priority / prioritized FIFO の十分条件
* global EDF の bounded tardiness / speedup
* scheduler 間比較定理

---

# Phase 11. OS 寄り multicore operational semantics

* per-CPU current
* runqueue(s)
* wakeup / block / completion
* timer / IPI / migration
* state trace から schedule 導出

---

# Phase 12. refinement

* partitioned refinement
* global refinement
* service refinement
* schedule refinement

---

# Phase 13. 発展テーマ

## 13.1 周期タスク
周期タスクは job 生成規則の拡張なので、
単一CPU EDF 系と partitioned EDF の後に入れるのが自然。

### やること
* `Task -> Job` 生成
* well-formedness
* utilization
* periodic EDF / RM の理論

## 13.2 DAG タスク
DAG は job 内部構造の拡張なので、
multicore / global の後に入れるのが自然。

### やること
* `Node`
* precedence
* `ready_node / completed_node / service_node`
* node-level semantics と job-level completion の接続
* makespan / span / work の基本補題