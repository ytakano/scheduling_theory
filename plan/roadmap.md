# ロードマップ

* **単一CPUで成り立つ直感がそのまま使えない**
* **global / partitioned / clustered** で理論が分かれる
* **work-conserving, fairness, interference, schedulability** の定義が複雑になる
* OS 寄りモデルでは **migration, per-CPU runqueue, load balancing, IPI** が入る

ので、最初から「単一CPUの一般化」ではなく、**単一CPU層とマルチコア層を分けて積み上げる**のが重要です。

---

# 全体方針の修正

最初から 1 本のモデルで全部扱うのではなく、次の 4 層に分けるのがよいです。

## 層A: 共通基盤

* Job
* service
* completion
* ready / pending
* deadline miss

## 層B: 単一CPU policy

* FIFO
* RR
* prioritized FIFO
* EDF

## 層C: マルチコア policy

* partitioned scheduling
* global scheduling
* clustered scheduling
* per-CPU queue / global queue

## 層D: OS 寄り operational model

* per-CPU current
* per-CPU runqueue
* migration
* balancing
* wakeup / preemption / timer / IPI

この分け方にすると、

* まず単一CPUで理論の核を作る
* その後マルチコア固有要素を載せる
* 最後に OS モデルへ行く

という自然な順序になります。

---

# 修正版ロードマップ概要

## Phase 0. 設計方針の固定

## Phase 1. 共通理論基盤

## Phase 2. 単一CPU scheduler 抽象化

## Phase 3. 単一CPU policy 実装

## Phase 4. 単一CPU 共通性質

## Phase 5. マルチコア基盤モデル

## Phase 6. マルチコア scheduler 抽象化

## Phase 7. partitioned / global / clustered policy

## Phase 8. マルチコア共通性質

## Phase 9. マルチコア schedulability / response-time 理論

## Phase 10. OS 寄りマルチコア operational semantics

## Phase 11. refinement

## Phase 12. 発展テーマ

---

# Phase 0. 設計方針の固定

ここで、マルチコア込みで最初に決めるべきことを明確化します。

## 0.1 時間

引き続き **離散時刻 `nat`** でよいです。

理由:

* 単一CPUと共通にできる
* 各 tick で各 CPU が高々 1 job 実行、というモデルが自然
* RR や per-CPU timer と相性がよい

## 0.2 CPU 集合

CPU を抽象化しておく。

* `CPU := nat`
* ただし実際には有限集合 `0 .. m-1`

を想定する。

## 0.3 どのマルチコア方式を扱うかを分ける

最初から全部混ぜず、明示的に区別する。

* **partitioned**: job/task は最初から CPU に固定
* **global**: 1つの全体 ready set から任意 CPU へ
* **clustered**: CPU クラスタごとに queue

これは理論がかなり違います。

## 0.4 migration の扱い

global/clustered では migration の有無を明示する。

* migration allowed
* migration forbidden
* restricted migration

---

# Phase 1. 共通理論基盤

最初からマルチコアへ持ち上げやすい形にします。

## 1.1 Job 属性

Job 基本属性:

* release time
* execution cost
* deadline
* static priority（必要なら）
* affinity / allowed CPUs（将来用）

最初から affinity フィールドを入れるか、後で拡張でもよいです。

## 1.2 Schedule の一般化

単一CPUでは

* `time -> option JobId`

でしたが、マルチコアでは

* `time -> CPU -> option JobId`

にします。

これは

> 時刻 `t` に CPU `c` で何が走るか

です。

## 1.3 service

`service sched j t` は引き続き

> 区間 `[0,t)` において、全CPU上で job `j` が受けた累積実行量

にします。

マルチコアで migration を許すなら、各時刻の全CPUを見て合計します。

ただし単一 job が同時に複数 CPU で走らない、という制約が必要です。

## 1.4 valid multicore schedule

単一CPU版に加えて必要なのは:

* 同じ時刻に同じ job が複数 CPU で走らない
* affinity 制約があれば守る
* release 前に走らない
* completed 後に走らない

## 1.5 この段階の成果物

* `CPU`
* multicore schedule
* multicore service
* valid multicore schedule
* 単一CPU版が special case として埋め込めること

---

# Phase 2. 単一CPU scheduler 抽象化

単一CPU policy をまず完成させます。

* FIFO
* RR
* prioritized FIFO
* EDF

を単一CPU上で定式化する段階です。

---

# Phase 3. 単一CPU policy 実装

* non-preemptive FIFO
* RR quantum=1
* prioritized FIFO
* EDF

ここで policy 層の基本補題を揃えます。

---

# Phase 4. 単一CPU 共通性質

* dispatch 健全性
* determinism
* work-conserving
* no-loss
* service と trace の一致
* FIFO/RR/EDF の局所仕様

この単一CPU部分は、後の partitioned scheduling の再利用にも効きます。

---

# Phase 5. マルチコア基盤モデル

ここからマルチコア固有部分です。

---

## 5.1 multicore execution の基本制約

新しく必要な述語:

* 同時刻に 1 job は高々 1 CPU でしか実行されない
* 1 CPU では高々 1 job
* job は allowed CPU 上でのみ実行

## 5.2 multicore service の基本補題

単一CPUの補題に加えて、

* 1ステップで service は高々 1 増える
  これは「同時多重実行なし」仮定のもとで成り立つ
* migration があっても service 定義は壊れない
* CPU をまたいだ実行履歴の合計が進捗になる

## 5.3 ready / pending の multicore 化

ready は本質的には job 単位で変わりませんが、
OS 寄りには

* globally ready
* CPU-local ready
* runnable on CPU c

を分けると便利です。

## 5.4 idle core / busy core

マルチコアでは core ごとの idle/busy を定義する必要があります。

* `Idle(c,t)`
* `Busy(c,t)`

これが後の work-conserving 定義に必要です。

---

# Phase 6. マルチコア scheduler 抽象化

ここで単一CPU scheduler interface を一般化します。

## 6.1 2種類の抽象化を分ける

### A. per-CPU scheduler

各 CPU が独立に選ぶ

* partitioned scheduling に向く

### B. global scheduler

全CPUの current / idle 状態を見て job 集合から複数個選ぶ

* global EDF や global FIFO などに向く

## 6.2 multicore choose の形

単一CPUでは「1個選ぶ」でしたが、マルチコアでは

* 各時刻に各 CPU へ割当てる
* idle CPU には仕事を置かない / 置けない

ので、choose は本質的に

> ready 集合から高々 `m` 個選び、各 CPU に割り当てる

操作になります。

## 6.3 抽象インターフェースの分離

おすすめは分けることです。

* `UniprocessorScheduler`
* `PartitionedScheduler`
* `GlobalScheduler`

1つに詰め込まない方が見通しがよいです。

---

# Phase 7. partitioned / global / clustered policy

ここでマルチコアの政策ごとの理論を入れます。

---

## 7.1 Partitioned scheduling

### モデル

* 各 job/task は特定 CPU に固定
* 各 CPU 上では単一CPU scheduler を実行

### 利点

* 単一CPU理論の再利用がしやすい
* FIFO/RR/priority/EDF を CPU ごとに独立に適用できる

### やるべきこと

* 割当て関数 `assign : JobId -> CPU`
* CPU ごとの valid schedule
* 全体 schedule は CPU ごとの合成
* service/completion が全体でも正しい

### 証明対象

* 各 CPU が valid なら全体も valid
* 各 CPU が schedulable なら全体も schedulable
* migration がないこと

---

## 7.2 Global scheduling

### モデル

* 全 job が 1つの global ready set に入る
* 各時刻に最大 `m` 個選んで CPU に置く
* migration 可能

### policy 候補

* global EDF
* global FIFO
* global prioritized FIFO
* global RR は定義できるが少し不自然で重い

### 新しく必要な概念

* top-`m` selection
* carry-in interference
* idle CPU があるのに他 job が待つ、という状況の排除
* work-conserving の multicore 版

### 証明対象

* top-`m` の正しさ
* same job not duplicated
* global work-conserving
* dispatch consistency

---

## 7.3 Clustered scheduling

### モデル

* CPU をクラスタに分ける
* 各クラスタ内では global、クラスタ間では partitioned

### 意義

* 実 OS / 実機の NUMA, cache locality, per-socket 設計に近い
* later stage に向く

最初からやらなくてよいですが、拡張点として残しておくとよいです。

---

# Phase 8. マルチコア共通性質

ここで「マルチコアで一般に証明すべきこと」を整理します。

---

## 8.1 multicore validity

* release 前に走らない
* completed 後に走らない
* 同時実行重複なし
* affinity 違反なし

## 8.2 multicore work-conserving

単一CPU版より定義が難しいです。

典型的には:

> ある時刻に runnable job があり、かつそれを受け入れられる idle CPU があるなら、その CPU を idle のままにしない

global と partitioned で定義が異なるので分けるべきです。

## 8.3 determinism

* 同じ global state なら同じ割当て結果
* tie-break を含めて一意

## 8.4 no-duplication

* 同じ job が同時刻に複数CPUへ置かれない

## 8.5 progress/fairness

* finite ready jobs なら idle core があれば何かが進む
* global RR 系では巡回性
* global priority 系では starvation 条件付き議論

---

# Phase 9. マルチコア schedulability / response-time 理論

ここから理論的に一気に難しくなります。

---

## 9.1 Partitioned schedulability

これは比較的やりやすいです。

### 基本方針

* 各 CPU で単一CPU解析
* 全体 schedulability は各 CPU の conjunction

### 証明対象

* partitioned EDF schedulability
* partitioned fixed-priority / prioritized FIFO response time
* FIFO/RR の completion or bounded waiting per CPU

---

## 9.2 Global schedulability

これはかなり難しいです。

### 代表テーマ

* global EDF
* bounded tardiness
* speedup bound
* workload / interference bound

### 必要概念

* carry-in tasks/jobs
* top-`m` interference
* busy window の multicore 版
* lag / fluid schedule 比較など

### 注意

最初から exact schedulability を狙わず、
まずは

* work-conserving
* no-duplication
* bounded interference
* simple sufficient conditions

あたりから始めるのが現実的です。

---

## 9.3 fairness / starvation on multicore

global priority 系では starvation 議論が繊細です。

証明対象の例:

* 強い仮定の下で starvation-freedom
* bounded waiting under finite ready-set assumptions
* RR 系での bounded service gap

---

# Phase 10. OS 寄りマルチコア operational semantics

ここが最終的な橋渡しです。

---

## 10.1 per-CPU machine state

最低限:

* `current[c]`
* `runqueue[c]` or global runqueue
* blocked set
* completed set
* clock
* pending wakeups
* pending IPIs / resched flags

## 10.2 イベント

単一CPU版に加えて:

* `Arrival j`
* `Tick c`
* `Completion c j`
* `Block c j`
* `Wakeup j`
* `IPI from c1 to c2`
* `Migrate j c1 c2`

## 10.3 load balancing / migration

global/clustered では重要です。

証明対象:

* migration で job を lost しない
* migration 先/元の queue 整合性
* one-copy invariant
* balancing が affinity を壊さない

## 10.4 reschedule / preemption

各 CPU で独立に reschedule が起こるので、

* local reschedule
* remote wakeup
* IPI-driven preemption

をモデル化できるようにする

## 10.5 trace から multicore schedule 生成

operational state trace から

* `sched t c = ...`

を導出し、Phase 1 の service/completion と接続する

---

# Phase 11. refinement

ここでは抽象 multicore policy と具体 OS-like machine の一致を示します。

---

## 11.1 partitioned refinement

* per-CPU queue 実装が abstract partitioned scheduler を実現する

## 11.2 global refinement

* global heap / global queue 実装が abstract global choose を実現する

## 11.3 clustered refinement

* cluster-level scheduler + per-CPU execution が abstract clustered model を実現する

## 11.4 service refinement

* operational trace で数えた実行量 = abstract service

---

# Phase 12. 発展テーマ

マルチコアを入れると、将来の発展先も変わります。

## 12.1 affinity / locality

* allowed CPU set
* cache locality aware scheduling
* cluster confinement

## 12.2 overhead

* migration cost
* IPI cost
* load balancing cost
* remote wakeup latency

## 12.3 blocking / shared resources

* multiprocessor locking
* blocking bound
* spinning / suspension

## 12.4 mixed-criticality

* per-core or global mixed-criticality scheduling

## 12.5 周期タスク (Periodic Tasks)

### 前提条件

* Phase 3–4（単一CPU EDF）完了

### モデル拡張

* `Task` レコードの `task_period` / `task_cost` / `task_deadline` を活用
* 周期的 job 生成規則: task τ の k 番目 job の release = τ.arrival + k * τ.period
* hyperperiod: 全タスクの period の lcm

### 証明対象

* 生成規則の well-formedness（release 単調増加など）
* 利用率上限定理 (Liu & Layland): Σ(cost_i / period_i) ≤ 1 ならば EDF で schedulable
* EDF の周期タスクに対する最適性（feasible な job set を EDF がすべてスケジュール可能）
* RM (Rate Monotonic) の schedulability 条件（オプション）

### 進め方

まず `Task -> Job` 生成関数を定義し、生成された job 列が `valid_jobs` を満たすことを示す。
その上で利用率計算と EDF schedulability を証明する。
骨格（生成規則・valid_jobs との整合）を先に入れ、schedulability 証明は後。

## 12.6 DAG タスク (DAG Tasks)

### 前提条件

* Phase 5–8（マルチコア基盤・partitioned/global scheduling）完了

### モデル拡張（3層化）

* `NodeId := nat` を導入
* `Node` レコード: 所属 job、実行コスト、先行 node 集合
* `Schedule` の移行候補: `Time -> CPU -> option (JobId * NodeId)`
* node-level ready: `ready_node n t = pending_node n t /\ preds_completed n t`
* node-level service / completed を job-level と分離

### no_duplication の変更

現在の「同じ job は同時に複数 CPU で走らない」を
「同じ node は同時に複数 CPU で走らない」に置き換える。
（同じ job の異なる ready node は別 CPU で同時に走ってよい）

### 証明対象

* precedence relation の well-formedness（DAG、循環なし）
* critical path / span の定式化
* node-level service の monotonicity・整合性
* parallel speedup の下界: span ≤ makespan ≤ work
* federated / work-stealing scheduling の健全性（オプション）

### 進め方

まず sequential job の証明群を固め、node レベルの定義を導入してから
job-level 性質との整合性補題を積み上げる。
一気に DAG 全体を入れず、node / ready_node / completed_node を段階的に追加する。
抽象化の骨格（コメント）はすでに `scheduling.v` に記載済み。

---

# 難易度順に見る実装・証明順序

マルチコア込みでも、実際にはこの順が現実的です。

---

## 第1段階: 単一CPU基盤

* Job / service / completed / ready
* valid schedule
* FIFO / RR / prioritized FIFO / EDF
* 共通性質

## 第2段階: multicore 共通基盤

* `Schedule := time -> CPU -> option JobId`
* multicore service
* no-duplication
* multicore validity

## 第3段階: partitioned scheduling

* assign function
* per-CPU scheduler lifting
* 各 CPU 性質から全体性質へ

これは最初のマルチコアとして最もおすすめです。

## 第4段階: global scheduling 基盤

* global ready set
* top-`m` choose
* global work-conserving
* no-duplication / determinism

## 第5段階: global EDF / prioritized FIFO

* 局所選択性
* multicore fairness/progress
* 干渉の基本補題

## 第6段階: OS 寄り multicore machine

* per-CPU current
* runqueue(s)
* wakeup / migration / IPI
* trace semantics

## 第7段階: refinement と解析

* abstract policy ⇔ machine
* response-time / schedulability / bounded tardiness

---

# 修正版ファイル構成案

## `Base.v`

* time, CPU, JobId
* job attributes
* single/multi-core common notions

## `Schedule.v`

* uniprocessor schedule
* multicore schedule
* service
* completed / ready / valid

## `UniSchedulerInterface.v`

* 単一CPU scheduler interface

## `UniPolicies/`

* `FIFO.v`
* `RoundRobin.v`
* `PrioritizedFIFO.v`
* `EDF.v`

## `MultiCoreBase.v`

* multicore validity
* no-duplication
* per-core / global idle/busy

## `Partitioned.v`

* assignment
* per-CPU lifting
* global composition

## `GlobalSchedulerInterface.v`

* top-`m` dispatch
* global ready sets

## `GlobalPolicies/`

* `GlobalEDF.v`
* `GlobalPrioritizedFIFO.v`
* 必要なら `GlobalFIFO.v`, `GlobalRR.v`

## `TraceSemantics.v`

* state traces
* derived schedules

## `OSModel/`

* per-CPU state
* runqueue/global queue
* wakeup/block/completion
* migration/IPI

## `Refinement/`

* queue/heap/ring-buffer refinements
* abstract ↔ operational

---

# どこまで最初にやるべきか

最初から全部やるとかなり大きいので、次の順がおすすめです。

## 最初に完成させるべき核

1. 単一CPU共通基盤
2. 単一CPU policy 群
3. multicore schedule / service / validity
4. partitioned scheduling

ここまでで、
**単一CPU理論 + マルチコアへの自然な拡張**
ができます。

## 次にやるべき核

5. global ready-set abstraction
6. global EDF または global prioritized FIFO
7. multicore work-conserving / no-duplication

## 最後に OS 寄り

8. per-CPU operational machine
9. migration / wakeup / IPI
10. refinement

---

# まとめ

マルチコア込みに修正すると、ロードマップはこう変わります。

1. **共通基盤**
   Job, multicore schedule, service, completion, valid schedule

2. **単一CPU policy 層**
   FIFO, RR, prioritized FIFO, EDF

3. **マルチコア policy 層**
   partitioned, global, clustered

4. **マルチコア共通性質**
   no-duplication, multicore work-conserving, determinism, fairness/progress

5. **マルチコア理論解析**
   partitioned schedulability, global interference, response-time / tardiness

6. **OS 寄り operational model**
   per-CPU current, runqueue, migration, wakeup, IPI, balancing

7. **refinement**
   abstract scheduling theory と concrete OS state machine の接続

いちばん大事なのは、**partitioned と global を最初から分けること**と、**service/completion の共通基盤を先に作ること**です。
