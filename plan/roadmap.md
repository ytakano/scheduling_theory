# roadmap.md 追記・修正版

# ロードマップ

単一CPU・マルチコア・OS寄りモデル・refinement を一度に混ぜると見通しが悪くなる。特にマルチコアでは、

* **単一CPUで成り立つ直感がそのまま使えない**
* **partitioned / global / clustered** で理論が分かれる
* **work-conserving, fairness, interference, schedulability** の定義が複雑になる
* OS 寄りモデルでは **migration, per-CPU runqueue, load balancing, wakeup, timer, IPI** が入る

ため、最初から 1 本の巨大モデルで扱うのではなく、**共通基盤 → 単一CPU理論 → マルチコア理論 → OS operational model → refinement** の順に積み上げるのがよい。

さらに、将来の拡張として入れたい **周期タスク** と **DAG タスク** は性質が異なる。

* **周期タスク**は主として **job 生成規則の拡張**
* **DAG タスク**は主として **job 内部構造の拡張**

である。したがって、両者は同じ「発展テーマ」ではあっても、導入のタイミングと必要な基盤が異なることを最初に明示しておく。

加えて、単一CPU policy の中では、**deadline-based policy** を EDF だけでなく **laxity-based policy** まで含めて整理する。
ここで laxity は典型的には

* `laxity(j,t) = job_abs_deadline(j) - t - remaining_cost(j,t)`

で与える。
EDF が「絶対デッドラインだけ」を見るのに対し、laxity-based policy は「残り余裕時間」を見るため、
同じ deadline-based 系でも、より実行状態依存の policy である。

---

# 全体方針

最初から 1 本のモデルで全部扱うのではなく、次の 4 層に分ける。

## 層A: 共通基盤

* Job / Task /（将来）Node
* service
* completion
* remaining cost
* laxity
* ready / pending
* deadline miss

## 層B: 単一CPU policy

* FIFO
* RR
* prioritized FIFO
* EDF
* laxity-based scheduling（LLF / LST など）

## 層C: マルチコア policy

* partitioned scheduling
* global scheduling
* clustered scheduling
* per-CPU queue / global queue

## 層D: OS 寄り operational model

* per-CPU current
* per-CPU runqueue / global runqueue
* migration
* balancing
* wakeup / preemption / timer / IPI

この分け方にすると、

1. まず共通理論の核を作る
2. 単一CPU scheduler 理論を完成させる
3. その後マルチコア固有要素を載せる
4. 最後に OS モデルへ接続する

という自然な順序になる。

---

# 修正版ロードマップ概要

## Phase 0. 設計方針の固定

## Phase 1. 共通理論基盤

## Phase 2. 単一CPU scheduler 抽象化

## Phase 3. 単一CPU policy 実装

## Phase 4. 単一CPU 共通性質

## Phase 5. マルチコア固有基盤

## Phase 6. マルチコア scheduler 抽象化

## Phase 7. partitioned / global / clustered policy

## Phase 8. マルチコア共通性質

## Phase 9. マルチコア schedulability / response-time 理論

## Phase 10. OS 寄りマルチコア operational semantics

## Phase 11. refinement

## Phase 12. 発展テーマ（周期タスク / DAG タスク）

---

# Phase 1. 共通理論基盤

ここでは CPU 数や具体 policy に依存しない、共通の抽象定義を整える。

## 1.1 Job / Task 基本属性

Job 基本属性:

* release time
* execution cost
* absolute deadline
* static priority（必要なら）
* affinity / allowed CPUs（将来用）

Task 基本属性（将来の周期タスク用）:

* cost
* period
* relative deadline

この段階では Task はまだ補助的でよいが、後で周期タスクへ進むための受け皿として定義しておく。

## 1.2 Schedule

単一CPUでは

* `time -> option JobId`

マルチコアでは

* `time -> CPU -> option JobId`

を使う。

ただしこの段階では、「CPU が複数ある」という型だけ導入し、マルチコア固有の制約はまだ後段に分ける。

## 1.3 service / remaining cost / laxity

`service sched j t` は

> 区間 `[0,t)` において、job `j` が受けた累積実行量

を表す。

加えて、deadline-based policy を EDF 以外にも拡張するために、

* `remaining_cost jobs m sched j t`
* `laxity jobs m sched j t`

を導入する。

典型的には

* `remaining_cost = job_cost - service`
* `laxity = deadline - now - remaining_cost`

とするが、Rocq では nat / Z のどちらで定義するかを早めに固定する。
最初は「deadline miss の直前で 0 以上を仮定できる範囲」の補題を揃え、
必要なら後で signed slack に拡張する。

## 1.4 completed / pending / ready

* `completed`
* `released`
* `pending`
* `ready`

を定義する。

ここでの `ready` はまずは job-level の抽象概念として置く。将来 DAG を入れる場合には node-level ready が別に必要になる。

## 1.5 deadline miss

* `missed_deadline`
* `feasible_schedule`
* `feasible`

を定義する。

ここで

* **feasible_schedule** = ある具体 schedule が締切違反を起こさない
* **feasible** = 条件を満たす schedule が存在する

を区別しておくと、後の理論が整理しやすい。

## 1.6 この段階の成果物

* `Task`
* `Job`
* `Schedule`
* `service`
* `remaining_cost`
* `laxity`
* `completed / pending / ready`
* `missed_deadline / feasible_schedule / feasible`

---

# Phase 2. 単一CPU scheduler 抽象化

ここでは単一CPU scheduler の抽象インターフェースを整える。

対象はまず

* FIFO
* RR
* prioritized FIFO
* EDF
* laxity-based scheduling

である。

この段階では

* ready set から次に実行すべき 1 job を選ぶ
* idle を返してもよい / 返してはいけない条件
* tie-break の扱い
* preemptive / non-preemptive の差
* state-dependent key（deadline, priority, laxity）の違い

を明示する。

特に laxity-based scheduling では、EDF と違って鍵が `t` と `sched` に依存するため、
chooser のインターフェースが

* static key 型
ではなく
* `jobs -> sched -> t -> candidate -> metric`

を許せるようにしておく。

---

# Phase 3. 単一CPU policy 実装

ここでは具体 policy を単一CPU上で実装・定式化する。

* non-preemptive FIFO
* RR quantum = 1
* prioritized FIFO
* EDF
* LLF / LST などの laxity-based scheduler

この段階で policy 固有の基本補題を揃える。

## 3.x laxity-based policy

最低限、以下のどちらか一方を最初の対象にする。

* **LLF (Least Laxity First)**: laxity 最小の ready job を選ぶ
* **LST (Least Slack Time)**: 実質的には同系統として扱う

まずは preemptive 単一CPU版から始める。
non-preemptive laxity-based は意味づけがやや不自然になりやすいので後回しでよい。

必要な論点:

* `remaining_cost` の定義
* laxity の時刻依存性
* 同一 laxity の tie-break
* 0-laxity job の扱い
* negative laxity をどう表現するか

---

# Phase 4. 単一CPU 共通性質

ここでは単一CPU scheduler 一般に成り立つ性質を整理する。

* dispatch 健全性
* determinism
* work-conserving
* no-loss
* service と trace の一致
* FIFO / RR / EDF / LLF の局所仕様

## 4.x deadline-based / laxity-based 共通補題

EDF と laxity-based をまとめるために、以下の共通補題層を設ける。

* metric-min chooser の一般補題
* tie-break を含む determinism
* ready でない job は metric 比較対象に入らない
* 最小 metric job が選ばれることの健全性

この層を先に置くと、EDF は
`metric = absolute deadline`
LLF は
`metric = laxity`
として再利用できる。

---

# Phase 7. partitioned / global / clustered policy

## 7.1 Partitioned scheduling

### 証明対象

* partitioned EDF schedulability
* partitioned laxity-based progress / bounded waiting
* partitioned fixed-priority / prioritized FIFO response time
* FIFO / RR の completion or bounded waiting per CPU

## 7.2 Global scheduling

### policy 候補

* global EDF
* global laxity-based scheduling
* global FIFO
* global prioritized FIFO
* global RR は定義できるがやや不自然で重い

### 新しく必要な概念

* top-`m` selection
* carry-in interference
* idle CPU があるのに他 job が待つ、という状況の排除
* work-conserving の multicore 版
* dynamic metric の top-`m` 選択

### 証明対象

* top-`m` の正しさ
* same job not duplicated
* global work-conserving
* dispatch consistency
* deadline-based / laxity-based top-`m` chooser の健全性

---

# Phase 8. マルチコア共通性質

## 8.5 progress / fairness

* finite ready jobs なら idle core があれば何かが進む
* global RR 系では巡回性
* global priority 系では starvation 条件付き議論
* global / partitioned laxity-based では 0-laxity / minimum-laxity job の進行性

---

# Phase 9. マルチコア schedulability / response-time 理論

## 9.1 Partitioned schedulability

### 証明対象

* partitioned EDF schedulability
* partitioned laxity-based sufficient conditions
* partitioned fixed-priority / prioritized FIFO response time
* FIFO / RR の completion or bounded waiting per CPU

## 9.2 Global schedulability

### 代表テーマ

* global EDF
* global laxity-based scheduling
* bounded tardiness
* speedup bound
* workload / interference bound

### 必要概念

* carry-in tasks / jobs
* top-`m` interference
* busy window の multicore 版
* lag / fluid schedule 比較
* dynamic-priority / dynamic-laxity interference

### 注意

最初から exact schedulability を狙わず、まずは

* work-conserving
* no-duplication
* bounded interference
* simple sufficient conditions

あたりから始めるのが現実的。

---

# Phase 12. 発展テーマ

## 12.5 周期タスク (Periodic Tasks)

### 前提条件

* Phase 3–4（単一CPU EDF / RM / laxity-based の基盤）完了
* 最初は **independent implicit-deadline periodic tasks** から始める

### 証明対象

* 生成規則の well-formedness（release 単調増加など）
* 生成された job 列が `valid_jobs` を満たすこと
* 利用率上限定理 (Liu & Layland): `Σ(cost_i / period_i) ≤ 1`
* EDF の周期タスクに対する最適性
* RM (Rate Monotonic) の schedulability 条件（必要なら）
* laxity-based policy に対する基本健全性・反例整理・十分条件（必要なら）

### 進め方

まず `Task -> Job` 生成関数を定義し、生成された job 列が共通基盤と整合することを示す。
その上で利用率計算と EDF/RM schedulability を証明する。
laxity-based については、最初から大定理を狙うより、

* laxity 定義の整合性
* 0-laxity job の扱い
* EDF と一致する条件
* 反例や非最適性の整理

を先に行うのがよい。
