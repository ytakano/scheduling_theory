結論から言うと、**Awkernel の実トレースを取っただけでは「EDF schedulable」とは言えない**。まったく、ログを眺めて「動いてるからヨシ」は一番危ないやつよ。

言えるようにするには、主張を次の3段階に分ける必要がある。

## 1. まず有限トレースについて言えること

実トレースから直接言えるのは、せいぜいこれ。

```text
この実行 prefix は
  1. trace well-formed
  2. schedule に射影可能
  3. EDF choice に適合
  4. 観測範囲内では deadline miss がない
```

つまり、

```text
observed trace conforms to EDF and has no observed deadline miss
```

であって、

```text
task set is schedulable under Awkernel EDF
```

ではない。

有限 trace だけでは、FIFO、priority、EDF、RR など複数モデルが同じ trace を説明できる場合がある。だから EDF だと識別するには、deadline 順と arrival 順がズレるような **distinguishing workload** が必要になる。これは既存レビューでも、有限 trace はモデルを一意に決めず、model inference + certified conformance checking + distinguishing workloads が必要だと整理している。

## 2. 実トレースから作るべきもの

Awkernel trace から次を構成する。

```text
Awkernel raw trace
  -> normalized event trace
  -> scheduler-facing event trace
  -> schedule : Time -> CPU -> option JobId
  -> service / completed / deadline_miss
```

必要なイベントは最低限これ。

```text
release / runnable
choose
dispatch
preempt
complete
sleep / block
wakeup
timer
IPI
migration, multicore の場合
```

そして各 job について次を持つ。

```text
job_id
task_id
release_time
absolute_deadline
execution_cost または observed_service
CPU / allowed CPU set
```

実装上は、すでに話していたように `LkRunnable`, `LkChoose`, `LkDispatch`, `LkSleep`, `LkComplete` 系を scheduler-facing event に畳み込む形でよい。ただし EDF を言うなら、**choose 時点の ready set と absolute deadline が復元できること**が必須。

## 3. EDF conformance checker で見ること

単一CPUまたは partitioned EDF なら、各 `choose` / `dispatch` 点で次を検査する。

```text
chosen job ∈ ready jobs
forall j ∈ ready jobs,
  deadline(chosen) <= deadline(j)
```

tie-break を固定しているなら、

```text
chosen = canonical_min_deadline_job ready_set
```

まで見る。

global EDF なら単一 job ではなく、

```text
chosen_set = top-m jobs among global ready set
```

を見る必要がある。マルチコアではさらに、

```text
same job not duplicated
one CPU runs at most one job
release 前に走らない
completion 後に走らない
affinity を破らない
idle CPU があるのに runnable job を放置しない
```

を検査する。ロードマップでも、マルチコアでは `service`, `valid multicore schedule`, no-duplication, affinity, global top-`m` selection を分けて積む方針になっている。

## 4. schedulability と言うための本体

本当に言いたい定理はこれ。

```text
TaskSet T passes EDF schedulability analysis
Awkernel trace refines abstract EDF schedule
------------------------------------------------
Awkernel execution has no deadline miss
```

したがって必要なのは二本立て。

### A. task set 側の解析

周期タスクなら、入力として次を固定する。

```text
period_i
offset_i
relative_deadline_i
cost_i / WCET_i
release_jitter_i, 必要なら
CPU assignment, partitioned の場合
```

そして Rocq 側で、

```text
DBF / busy-window / prefix checker
```

などを通して、

```text
abstract EDF schedule has no deadline miss
```

を示す。

ここで注意。**period や jitter を実トレースから逆算するだけでは弱い**。それは「候補モデルの推定」にすぎない。schedulability の証明に使うなら、benchmark manifest や task spec として与え、trace はそれに合っているかを検査する方が健全。

### B. Awkernel trace 側の refinement

実トレースから復元した schedule が abstract EDF schedule に一致、または OS overhead を含めて bounded-delay refinement になっていることを示す。

理想形はこれ。

```text
project_schedule(normalize(awkernel_trace))
  refines
abstract_edf_schedule
```

現実の OS では dispatch / wakeup / timer / IPI delay があるので、最初から完全一致より、

```text
高々 δ 遅れる
```

という形が自然。

```text
project_schedule(trace) <=δ abstract_edf_schedule
```

この δ を schedulability analysis 側に overhead / release jitter / dispatch delay として吸収する。

## 5. 最終的に主張できる形

弱い順に並べるとこう。

### レベル1: 有限ログ検査

```text
この Awkernel trace は、観測範囲内で EDF に適合し、
deadline miss を含まない。
```

これはすぐ狙える。

### レベル2: benchmark instance の実行検証

```text
与えた periodic task set T について、
Awkernel の実行 trace は task spec と整合し、
EDF choice に適合し、
観測範囲内で deadline miss がない。
```

これも現実的。

### レベル3: abstract EDF schedulability との接続

```text
T は RocqSched の EDF schedulability checker を通る。
また、Awkernel trace から復元した schedule は abstract EDF schedule に適合する。
したがって、この実行は T の EDF schedulability 証明と矛盾しない。
```

ここから研究として意味が出る。

### レベル4: Awkernel EDF implementation の refinement

```text
Awkernel scheduler implementation は、
任意の well-formed task set / trace に対して、
abstract EDF scheduler の bounded-delay refinement である。
```

これが最終目標。これは trace だけでは無理で、Awkernel の operational semantics か、少なくとも trace-generation rules の健全性が必要。

## 実際の作業 plan

まずはこれでよい。

```text
Step 1. EDF 用 workload を作る
  - deadline 順と arrival 順がズレる task set
  - preemption が必要な task set
  - 同 deadline tie-break を含む task set
  - partitioned/global を区別できる task set

Step 2. Awkernel trace schema を固定
  - event_id
  - real_time
  - cpu_id
  - kind
  - subject job/task
  - related job/task
  - absolute_deadline
  - release / dispatch / complete reason

Step 3. normalizer を作る
  - raw trace を event_id 順に整列
  - low-level event を scheduler event に畳み込む
  - invalid transition を検出

Step 4. schedule projector を作る
  - dispatch/preempt/complete から
    sched : Time -> CPU -> option JobId
    を復元
  - service / completed / deadline_miss を計算

Step 5. EDF recognizer/checker を Rocq で定義し Haskell extraction
  - chosen job is earliest-deadline
  - global なら top-m
  - work-conserving
  - no-duplication
  - ready-set consistency

Step 6. task model checker を足す
  - trace releases match periodic generation
  - offset / period / relative deadline / jitter bound を検査
  - observed execution <= declared WCET を検査

Step 7. schedulability checker と接続
  - DBF / busy-window / prefix witness を生成
  - Rocq checker で検査
  - trace conformance theorem と接続
```

## いま最初に狙うべき定理名

まずはこのあたり。

```coq
Theorem checked_awkernel_trace_edf_conformant :
  check_awkernel_edf_trace tr = true ->
  edf_conformant_trace (project_trace tr).

Theorem checked_awkernel_trace_no_observed_miss :
  check_awkernel_edf_trace tr = true ->
  no_deadline_miss_on_prefix (project_schedule tr) horizon.

Theorem periodic_taskset_dbf_checked_schedulable :
  check_periodic_edf_dbf tasks = true ->
  abstract_edf_schedulable tasks.

Theorem awkernel_trace_edf_schedulability_bridge :
  trace_refines_edf tr tasks ->
  abstract_edf_schedulable tasks ->
  no_deadline_miss_on_projected_trace tr.
```

bounded-delay まで行くなら最後はこう。

```coq
Theorem awkernel_bounded_delay_edf_schedulability :
  bounded_delay_refines_edf delta tr tasks ->
  jitter_aware_edf_schedulable delta tasks ->
  no_deadline_miss_on_projected_trace tr.
```

## まとめ

Awkernel の実トレースを取得して EDF schedulability を主張するには、単に deadline miss が無いことを見るのでは足りない。

必要なのはこれ。

```text
1. trace を scheduler-facing event に正規化する
2. trace から schedule / service / completed を復元する
3. 各 choose/dispatch が EDF 最小 deadline 選択であることを検査する
4. task set の period / offset / deadline / WCET / jitter を固定する
5. Rocq の EDF schedulability analysis で task set を通す
6. projected Awkernel schedule が abstract EDF または bounded-delay EDF に refine することを示す
```

最初に言える安全な表現は、

```text
この Awkernel 実トレースは、与えた task model に対して、
観測範囲内で EDF conformance と no deadline miss を満たす。
```

その次に、

```text
この task set は RocqSched の EDF schedulability theorem により schedulable であり、
Awkernel trace はその abstract EDF 実行に適合している。
```

まで持っていく。ここまで来て初めて、かなりまともに「Awkernel の実トレースを通じて EDF schedulability を示した」と言える。理解してる？「ログが通った」だけと「schedulability theorem に接続した」は、全然別物よ。
