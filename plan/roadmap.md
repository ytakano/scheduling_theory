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

---

# 全体方針

最初から 1 本のモデルで全部扱うのではなく、次の 4 層に分ける。

## 層A: 共通基盤

* Job / Task /（将来）Node
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

# Phase 0. 設計方針の固定

ここで、今後の拡張を見据えて最初に固定すべき設計方針を明確化する。

## 0.1 時間

引き続き **離散時刻 `nat`** を使う。

理由:

* 単一CPUとマルチコアで共通に使いやすい
* 各 tick で各 CPU が高々 1 実行単位を処理するモデルと相性がよい
* RR や timer tick、per-CPU timer の表現がしやすい

## 0.2 CPU 集合

CPU は抽象的には

* `CPU := nat`

としつつ、実際には有限集合 `0 .. m-1` を想定する。

## 0.3 どのマルチコア方式を扱うかを最初から分ける

最初から全部混ぜず、明示的に区別する。

* **partitioned**: job/task は最初から CPU に固定
* **global**: 1つの全体 ready set から任意 CPU へ割り当てる
* **clustered**: CPU クラスタごとに queue / scheduler を持つ

これらは理論も invariants もかなり異なる。

## 0.4 migration の扱い

global / clustered では migration の有無を明示する。

* migration allowed
* migration forbidden
* restricted migration

## 0.5 拡張の種類を最初に分ける

今後入れたい拡張は少なくとも 2 種類ある。

### A. job 生成規則の拡張

例: **周期タスク**

* task から job 列をどう生成するか
* release pattern
* relative deadline から absolute deadline をどう定めるか

### B. job 内部構造の拡張

例: **DAG タスク**

* 1 つの job を node 群へ分解
* precedence 制約
* node-level ready / completed / service

この違いを最初に明示することで、周期タスクを単一CPU理論の延長に置き、DAG タスクをマルチコア理論の延長に置く理由が明確になる。

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

## 1.3 service

`service sched j t` は

> 区間 `[0,t)` において、job `j` が受けた累積実行量

を表す。

マルチコアでは全 CPU 上の実行量の和として定義する。
ただし、「同一 job が同時に複数 CPU で走らない」という制約はこの段階では定義に含めず、後でマルチコア固有制約として追加する。

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

である。

この段階では

* ready set から次に実行すべき 1 job を選ぶ
* idle を返してもよい / 返してはいけない条件
* tie-break の扱い
* preemptive / non-preemptive の差

を明示する。

---

# Phase 3. 単一CPU policy 実装

ここでは具体 policy を単一CPU上で実装・定式化する。

* non-preemptive FIFO
* RR quantum = 1
* prioritized FIFO
* EDF

この段階で policy 固有の基本補題を揃える。

---

# Phase 4. 単一CPU 共通性質

ここでは単一CPU scheduler 一般に成り立つ性質を整理する。

* dispatch 健全性
* determinism
* work-conserving
* no-loss
* service と trace の一致
* FIFO / RR / EDF の局所仕様

この層は後の partitioned scheduling にそのまま再利用できる。

---

# Phase 5. マルチコア固有基盤

ここでは Phase 1 の共通基盤の上に、**マルチコア特有の制約・不変条件** を追加する。

---

## 5.1 multicore execution の基本制約

新しく必要な述語:

* 同じ時刻に 1 job は高々 1 CPU でしか実行されない
* 1 CPU では高々 1 job
* affinity がある場合は allowed CPU 上でのみ実行される

## 5.2 multicore service の基本補題

単一CPUの補題に加えて、

* 1ステップで service は高々 1 増える
  （同時多重実行なし仮定のもと）
* migration があっても service 定義は壊れない
* CPU をまたいだ実行履歴の合計が進捗になる

を示す。

## 5.3 ready / pending の multicore 化

ready は job-level では基本的に変わらないが、OS 寄りモデルを見据えると、

* globally ready
* CPU-local ready
* runnable on CPU `c`

を分けておくと便利である。

## 5.4 idle core / busy core

マルチコアでは core ごとの idle / busy を定義する必要がある。

* `Idle(c,t)`
* `Busy(c,t)`

これは後の multicore work-conserving の定義に必要。

## 5.5 この段階の成果物

* no-duplication
* affinity-aware validity
* idle / busy
* multicore service 基本補題
* local/global runnable notions

---

# Phase 6. マルチコア scheduler 抽象化

ここで単一CPU scheduler interface を一般化する。

## 6.1 2種類の抽象化を分ける

### A. per-CPU scheduler

各 CPU が独立に選ぶ。

* partitioned scheduling に向く

### B. global scheduler

全 CPU の current / idle 状態を見て、ready 集合から複数個選ぶ。

* global EDF や global prioritized scheduling に向く

## 6.2 multicore choose の形

単一CPUでは「1個選ぶ」だったが、マルチコアでは

> ready 集合から高々 `m` 個を選び、各 CPU に割り当てる

操作になる。

## 6.3 抽象インターフェースの分離

おすすめは次のように分けること。

* `UniprocessorScheduler`
* `PartitionedScheduler`
* `GlobalScheduler`

1つに詰め込まない方が見通しがよい。

---

# Phase 7. partitioned / global / clustered policy

ここでマルチコア policy ごとの理論を入れる。

---

## 7.1 Partitioned scheduling

### モデル

* 各 job / task は特定 CPU に固定
* 各 CPU 上では単一CPU scheduler を実行

### 利点

* 単一CPU理論の再利用がしやすい
* FIFO / RR / priority / EDF を CPU ごとに独立に適用できる

### やるべきこと

* 割当て関数 `assign : JobId -> CPU`
* CPU ごとの valid schedule
* 全体 schedule は CPU ごとの合成
* service / completion が全体でも正しい

### 証明対象

* 各 CPU が valid なら全体も valid
* 各 CPU が feasible_schedule なら全体も feasible_schedule
* 各 CPU が feasible なら全体も feasible
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
* global RR は定義できるがやや不自然で重い

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
* 各クラスタ内では global
* クラスタ間では partitioned

### 意義

* 実 OS / 実機の NUMA, cache locality, per-socket 設計に近い

最初からやらなくてもよいが、拡張先として残しておく価値がある。

---

# Phase 8. マルチコア共通性質

ここで「マルチコアで一般に証明すべきこと」を整理する。

---

## 8.1 multicore validity

* release 前に走らない
* completed 後に走らない
* 同時実行重複なし
* affinity 違反なし

## 8.2 multicore work-conserving

単一CPU版より定義が難しい。

典型的には:

> ある時刻に runnable job があり、かつそれを受け入れられる idle CPU があるなら、その CPU を idle のままにしない

ただし global と partitioned では定義が異なるので分けるべき。

## 8.3 determinism

* 同じ global state なら同じ割当て結果
* tie-break を含めて一意

## 8.4 no-duplication

* 同じ job が同時刻に複数 CPU へ置かれない

## 8.5 progress / fairness

* finite ready jobs なら idle core があれば何かが進む
* global RR 系では巡回性
* global priority 系では starvation 条件付き議論

---

# Phase 9. マルチコア schedulability / response-time 理論

ここから理論的に一気に難しくなる。

---

## 9.1 Partitioned schedulability

比較的やりやすい。

### 基本方針

* 各 CPU で単一CPU解析
* 全体 schedulability は各 CPU の conjunction

### 証明対象

* partitioned EDF schedulability
* partitioned fixed-priority / prioritized FIFO response time
* FIFO / RR の completion or bounded waiting per CPU

---

## 9.2 Global schedulability

かなり難しい。

### 代表テーマ

* global EDF
* bounded tardiness
* speedup bound
* workload / interference bound

### 必要概念

* carry-in tasks / jobs
* top-`m` interference
* busy window の multicore 版
* lag / fluid schedule 比較

### 注意

最初から exact schedulability を狙わず、まずは

* work-conserving
* no-duplication
* bounded interference
* simple sufficient conditions

あたりから始めるのが現実的。

---

## 9.3 fairness / starvation on multicore

global priority 系では starvation 議論が繊細。

証明対象の例:

* 強い仮定の下で starvation-freedom
* bounded waiting under finite ready-set assumptions
* RR 系での bounded service gap

---

# Phase 10. OS 寄りマルチコア operational semantics

ここが最終的な橋渡し。

---

## 10.1 per-CPU machine state

最低限:

* `current[c]`
* `runqueue[c]` または global runqueue
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

global / clustered では重要。

証明対象:

* migration で job を lost しない
* migration 元/先の queue 整合性
* one-copy invariant
* balancing が affinity を壊さない

## 10.4 reschedule / preemption

各 CPU で独立に reschedule が起こるので、

* local reschedule
* remote wakeup
* IPI-driven preemption

をモデル化できるようにする。

## 10.5 trace から multicore schedule 生成

operational state trace から

* `sched t c = ...`

を導出し、Phase 1 の `service` / `completed` と接続する。

---

# Phase 11. refinement

ここでは抽象 multicore policy と具体 OS-like machine の一致を示す。

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

ここでは、共通基盤の上に載せる task model 拡張を整理する。

---

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

### 拡張の性質

周期タスクは **job 生成規則の拡張** である。
つまり中心は「task から job をどう生成するか」であり、job 自体の completed / ready / deadline semantics は基本的に既存の job-level 理論を再利用できる。

### 前提条件

* Phase 3–4（単一CPU EDF / RM の基盤）完了
* 最初は **independent implicit-deadline periodic tasks** から始める

最初から arbitrary deadline や複雑な到着モデルを狙わない。

### モデル拡張

* `Task` レコードの `task_period` / `task_cost` / `task_relative_deadline` を活用
* 周期的 job 生成規則: task `τ` の `k` 番目 job の release = `τ.offset + k * τ.period`
* absolute deadline = release + relative deadline
* hyperperiod: 全タスクの period の lcm

### 証明対象

* 生成規則の well-formedness（release 単調増加など）
* 生成された job 列が `valid_jobs` を満たすこと
* 利用率上限定理 (Liu & Layland): `Σ(cost_i / period_i) ≤ 1`
* EDF の周期タスクに対する最適性
* RM (Rate Monotonic) の schedulability 条件（必要なら）

### 進め方

まず `Task -> Job` 生成関数を定義し、生成された job 列が共通基盤と整合することを示す。
その上で利用率計算と EDF/RM schedulability を証明する。
骨格（生成規則・well-formedness・valid_jobs との整合）を先に入れ、schedulability 証明は後に回してよい。

---

## 12.6 DAG タスク (DAG Tasks)

### 拡張の性質

DAG タスクは **job 内部構造の拡張** である。
つまり中心は「1 つの job を node 群へ分解し、precedence 制約を導入すること」であり、周期タスクとは拡張の方向が異なる。

### 前提条件

* Phase 5–8（マルチコア基盤・partitioned/global scheduling）完了
* sequential job の共通補題群が十分に整備されていること

### モデル拡張（3層化）

* `NodeId := nat` を導入
* `Node` レコード: 所属 job、実行コスト、先行 node 集合
* `Schedule` の移行候補: `Time -> CPU -> option (JobId * NodeId)` または `option NodeId`
* node-level ready:
  * `ready_node n t = pending_node n t /\ preds_completed n t`
* node-level service / completed を job-level と分離

### no_duplication の変更

現在の「同じ job は同時に複数 CPU で走らない」を
「同じ node は同時に複数 CPU で走らない」に置き換える。

同じ job の異なる ready node は、別 CPU で同時に走ってよい。

### 証明対象

* precedence relation の well-formedness（DAG、循環なし）
* node-level service の monotonicity・整合性
* critical path / span の定式化
* work と span に基づく基本境界
* node-level semantics と job-level completion / deadline miss の接続
* parallel speedup の基本下界 / 上界
* federated / work-stealing scheduling の健全性（必要なら）

### 進め方

まず sequential job の証明群を固め、次に node レベルの定義を導入する。
その後、

* `ready_node`
* `completed_node`
* `service_node`

を段階的に追加し、最後に **node-level semantics と job-level deadline semantics の整合性補題** を積み上げる。
一気に DAG 全体を入れず、node / ready_node / completed_node を段階的に追加する。

---

# 難易度順に見る実装・証明順序

マルチコア込みでも、実際には次の順が現実的。

---

## 第1段階: 単一CPU基盤

* Job / service / completed / ready
* valid schedule
* FIFO / RR / prioritized FIFO / EDF
* 単一CPU 共通性質

## 第2段階: 周期タスク基盤

* `Task`
* `Task -> Job` 生成規則
* release / deadline の well-formedness
* EDF / RM に必要な task model 前提の固定

周期タスクは **job 生成規則の拡張** なので、この段階で入れるのが自然。

## 第3段階: multicore 共通基盤

* `Schedule := time -> CPU -> option JobId`
* multicore service
* no-duplication
* multicore validity
* idle / busy
* local/global runnable notions

## 第4段階: partitioned scheduling

* assign function
* per-CPU scheduler lifting
* 各 CPU 性質から全体性質へ

これは最初のマルチコアとして最もおすすめ。

## 第5段階: global scheduling 基盤

* global ready set
* top-`m` choose
* global work-conserving
* no-duplication / determinism

## 第6段階: DAG node-level 基盤

* `Node`
* `ready_node`
* `completed_node`
* precedence well-formedness
* node-level service

DAG タスクは **job 内部構造の拡張** なので、multicore / global 基盤の後に入れるのが自然。

## 第7段階: global EDF / prioritized FIFO / DAG 上の基本性質

* multicore fairness / progress
* 干渉の基本補題
* node-level semantics と job-level completion の接続
* DAG 上の makespan / span / work の基本補題

## 第8段階: OS 寄り multicore machine

* per-CPU current
* runqueue(s)
* wakeup / migration / IPI
* trace semantics

## 第9段階: refinement と解析

* abstract policy ⇔ machine
* response-time / schedulability / bounded tardiness

---

# 修正版ファイル構成案

## `Base.v`

* time, CPU, JobId, TaskId
* job attributes
* task attributes
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

## `PeriodicTasks.v`

* task-to-job generation
* periodic well-formedness
* utilization definitions

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

## `DAGBase.v`

* node definitions
* precedence
* ready_node / completed_node / service_node

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

最初から全部やるとかなり大きいので、次の順がおすすめ。

## 最初に完成させるべき核

1. 単一CPU共通基盤
2. 単一CPU policy 群
3. 周期タスク生成規則の骨格
4. multicore schedule / service / validity
5. partitioned scheduling

ここまでで、

* 単一CPU理論
* 周期タスクの入り口
* マルチコアへの自然な拡張

ができる。

## 次にやるべき核

6. global ready-set abstraction
7. global EDF または global prioritized FIFO
8. multicore work-conserving / no-duplication
9. DAG の node-level 基盤

## 最後に OS 寄り

10. per-CPU operational machine
11. migration / wakeup / IPI
12. refinement

---

# まとめ

このロードマップは、次の 3 種類の拡張を明確に分離して進める構成になっている。

1. **共通基盤**
   * Job, Task, multicore schedule, service, completion, valid schedule

2. **policy の拡張**
   * FIFO, RR, prioritized FIFO, EDF
   * partitioned, global, clustered

3. **task model の拡張**
   * 周期タスク = job 生成規則の拡張
   * DAG タスク = job 内部構造の拡張

その上で最終的に、

4. **OS 寄り operational model**
   * per-CPU current, runqueue, migration, wakeup, IPI, balancing

5. **refinement**
   * abstract scheduling theory と concrete OS state machine の接続

へ進む。

いちばん大事なのは、

* **partitioned と global を最初から分けること**
* **service / completion の共通基盤を先に作ること**
* **周期タスクと DAG タスクを別種の拡張として扱うこと**

である。