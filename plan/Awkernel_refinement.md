# Awkernel Refinement Boundary

## Goal

Awkernel refinement の次段では、Awkernel の concrete runtime behavior を
common operational interface に射影し、その射影から semantic schedule に
接続する境界を固定する。

この計画の目的は Awkernel 全体の実装状態機械を common 層へ持ち込むことではない。
目的は、proof-facing public API と downstream adapter obligation を
最小限で固定することである。

## Common Layer

common layer が公開するのは、proof-relevant scheduler view だけである。
`OpState` は concrete OS state そのものではなく、scheduler projection のための
最小観測面である。
同じ層は projected execution 上の generic scheduling-causality package も提供し、
abstract lifecycle と scheduling-control の因果列を OS 非依存に固定する。
さらに、running job だけでなく scheduler-visible job についても、
release / not-completed を回収する generic package を提供する。
さらに、`op_need_resched` と `op_dispatch_target` を pending scheduler work として
扱う scheduler handoff package も提供する。

共通 state:

- `op_current : CPU -> option JobId`
- `op_runnable : list JobId`
- `op_need_resched : CPU -> bool`
- `op_dispatch_target : CPU -> option JobId`

`op_runnable` は concrete runqueue そのものではなく、adapter が export する
proof-facing runnable view である。
`op_dispatch_target` も concrete dispatch pipeline そのものではなく、
proof-facing dispatch candidate view である。

共通 event:

- `EvWakeup`
- `EvBlock`
- `EvComplete`
- `EvRequestResched`
- `EvHandleResched`
- `EvChoose`
- `EvDispatch`
- `EvPreempt`
- `EvStutter`
- `EvTick`

Common event meanings:

- `EvWakeup` は job が released として scheduler view に現れる
  lifecycle event である
- `EvComplete` は job が completed として scheduling semantics に達する
  lifecycle event である
- `EvHandleResched` は pending な reschedule condition を処理に進める
  global interface event である
- `EvChoose` は dispatch target を選ぶ global interface event である
- `EvDispatch` / `EvPreempt` / `EvBlock` / `EvComplete` は pending target を
  consume しうる abstract event である
- これらの event 意味は concrete hook を規定しない

この層が意図的に除外する runtime detail:

- runqueue の内部構造
- timer record や hardware timer の具象状態
- IPI device detail
- lock 実装
- migration の詳細手順
- policy 固有 queue order

## Adapter Layer

Awkernel adapter は concrete execution から abstract events への射影を提供する。
common layer は global common package を提供し、Awkernel adapter はそれに対する
local adapter contract を満たす。
local contract は Awkernel 固有の hook 対応と projection obligation であり、
common operational interface そのものではない。
common layer 側は local contract から generic scheduling-causality fact を
回収するが、その concrete witness path 自体は adapter 側に残す。
同様に、common layer 側は scheduler-visible job package により
`op_current` / `op_runnable` / `op_dispatch_target` に現れる job から
release / not-completed を回収するが、その witness path は adapter 側に残す。
さらに、common layer 側は scheduler handoff package により
pending scheduling-control obligation と pending switch candidate の保存・消費を
回収するが、その concrete scheduling point は adapter 側に残す。

adapter が構成する対象:

- `RUNNING` と per-CPU current task から `op_current` を構成する
- runqueue と wake 済み task から `op_runnable` を構成する
- `op_runnable` と `op_dispatch_target` に現れる job が abstract scheduling
  semantics 上で released かつ not completed であることを保証する
- wakeup path を `EvWakeup` に対応づけるのは、release semantics と整合する
  abstract lifecycle point に限る
- completion path を `EvComplete` に対応づけるのは、completion semantics と
  整合する abstract lifecycle point に限る
- `need_sched`、preemption pending、`wake_cpu()` から reschedule request / delivery を構成する
- Awkernel local adapter contract はどの concrete control path が
  `EvHandleResched` を実現するかを説明する
- scheduler の choose 点と actual dispatch を `EvChoose` / `EvDispatch` に対応づける
- Awkernel local adapter contract はどの concrete scheduler point が
  `EvChoose` を実現するかを説明する
- scheduler-relevant でない raw concrete step は `EvStutter` に対応づける
- sleep timeout は raw timer interrupt ではなく adapter-side proxy として扱う

Awkernel local adapter contract:

- downstream adapter must provide a projection from concrete execution to abstract events
- downstream adapter must discharge the obligations needed to recover validity, admissibility, and placement from the projected execution

`EvHandleResched` は raw hardware IPI reception そのものではなく、preemption
delivery 側の generic proxy event として扱う。Awkernel では interrupt handler と
voluntary preemption の両方をこの event に射影する。
それは raw interrupt, flag set, IPI reception 自体ではなく、
abstract handling step である。
`EvStutter` は scheduler view が不変な raw concrete step を表し、delay budget に
寄与しない silent event として扱う。
common scheduling-causality package は
`EvWakeup -> EvHandleResched -> EvChoose -> EvDispatch/EvPreempt -> EvComplete`
という generic control chain を扱うが、どの hook がそれを実現するかは
Awkernel や Linux ごとの adapter contract の責務である。

## Runtime Layer

Awkernel runtime 側で refinement の projection point になるのは以下の hook である。

- `Task::wake()`
- scheduler の enqueue point
- `get_next_task()` / scheduler の `get_next()`
- `run_main()`
- `wake_cpu()`
- sleep timeout の wake path

ただし、これらは concrete runtime hook であり、common interface の意味そのものではない。
初回 adapter では `get_next()` を choose と dispatch の合成点として扱う暫定対応を許す。
proof-facing separation としての `dispatch_target` は common interface 側で先に固定し、
Rust 側の finer hook は後段で拡張する。
choose/dispatch の分離は global common package の責務であり、
Awkernel がそれをどの concrete hook で実現するかは local adapter contract の責務である。

## Next Tasks

1. baseline milestone は完了した。
   faithful な 2 CPU cross-core baseline trace を canonical captured artifact
   として固定し、QEMU と Linux KVM の両 backend がそれを再現し、
   Rocq 側の baseline witness がその trace に一致することを確認済みである
2. handoff-aware な 2 CPU multicore adapter witness は完了した。
   これは common 層の新しい semantics ではなく、既存 interface を使う
   trace-backed adapter milestone である。
   captured handoff trace と fully proved な Rocq replay witness が
   active milestone の authoritative witness source になっている
3. この milestone で witness する event slice は次とする
   - `EvWakeup`
   - `EvRequestResched`
   - `EvHandleResched`
   - `EvChoose`
   - `EvDispatch`
   - `EvComplete`
   - optional `EvStutter`
4. CPU 0 は scheduler-side witness source、CPU 1 は worker-side execution
   witness source とする。
   scheduler-core から worker-core への handoff と cross-CPU wakeup /
   reschedule propagation は adapter/runtime witness 側で説明し、
   common operational interface には新 event を足さない
5. Rocq 側では、captured 2 CPU trace が既存の
   `OSProjection` / `OSLabeledProjection` / `OSLocalAdapterContract`
   family をそのまま instantiate し、validity / placement /
   scheduler-visible / handoff package を再利用できることを示した。
   synthetic baseline replay は smoke proof として残し、
   handoff-aware replay を active milestone の witness にしている
6. 次の中間目標は、単発 artifact ではなく trace family を受ける
   adapter-local 生成規則である。
   現在の captured handoff trace は canonical な seed instance として維持し、
   次段ではその 1 本専用の replay から離れて、captured rows の family に対する
   well-formedness / prefix / row-to-state / row-to-label の生成規則を与える
7. Rocq 側では、その生成規則から既存の
   `OSProjection` / `OSLabeledProjection` / `OSLocalAdapterContract`
   family を再利用できる replay witness を導く。
   目標は別の handwritten `state0`, `state1`, ... を増やすことではなく、
   長い trace でも induction で閉じる adapter-local infrastructure を作ること
8. runtime 側では、deterministic な handoff-aware 2 CPU trace を出すのに
   必要な narrow observables だけを追加する。
   human-readable な `BASELINE_TRACE` 行は backend validation に残しつつ、
   Rocq-encoded witness block も同じ trace から出力する。
   broad tracing system、full interrupt coverage、migration、
   timer-driven slice、`EvPreempt` は trace-family generation rules の
   milestone でも扱わない
9. current concrete trace capture method は runtime-local に固定した。
   各 CPU は fixed-capacity buffer に row を append し、global atomic
   `event_id` が canonical replay order を与える。
   synchronized TSC は debug metadata として残してよいが、proof-facing
   order には使わない。dump 時には `event_id` 順に merged row list を作り、
   同じ row 列から human-readable trace と Rocq witness block を出力する。
   overflow した run は canonical witness として reject する
10. common 層はこの次段でも変えない。
   new `OpState`、new `OpEvent`、new common contract family は追加せず、
   生成規則は adapter 層の責務に留める
11. candidate-source, scheduler-relation, algorithm-adapter, delay-adapter は
   trace-family generation rules の次段で追加する

## Trace-Based Validation Boundary

この段階で必要なのは common 層の新しい semantics ではない。
必要なのは、既存の common interface が concrete backend trace から
実際に instantiate できることを示す最小 witness である。

minimal trace とは、現在の common contract を成立させるのに必要な最小の
concrete state-and-step 列であり、少なくとも次の proof-facing view を
回復できなければならない。

- `op_current`
- `op_runnable`
- `op_need_resched`
- `op_dispatch_target`

初回の target event は次でよい。

- `EvWakeup`
- `EvChoose`
- `EvDispatch`
- `EvComplete`
- `EvStutter`

`EvTick` は distinct な timer proxy observation が必要になるまで必須ではない。
preemption, timer-driven wakeup, migration, raw IPI detail も初回 trace slice には
含めない。

baseline witness 自体は 2 CPU runtime 上で取得し、CPU 0 の scheduler-side
slice と CPU 1 の execution-side slice を組み合わせた cross-core witness として
使う。Awkernel 自体は 2 CPU 以上を対象とし、1 CPU は interrupt/scheduler 専用、
他 CPU は async/await task 実行用である。
したがって、baseline は common interface を validate する最小 witness slice として
完了し、次段では scheduler-core / worker-core interaction を handoff-aware な
multicore adapter witness として追加する。

current concrete trace capture は runtime-local method として次で固定している。

- 各 CPU は自分の fixed-capacity buffer にだけ row を append する
- global atomic `event_id` が cross-CPU replay order を与える
- synchronized TSC は optional な debug metadata に留める
- dump 時に `event_id` 順で canonical merged row list を作る
- 同じ merged row list から `BASELINE_TRACE` 行と Rocq witness block を出力する
- overflow した run は canonical witness として reject する

この ordering metadata は replay/reconstruction のための runtime detail であり、
semantic time や common-layer causality を定義するものではない。

## Common / Adapter / Runtime Split For The Trace

Common layer:

- `OpState`, `OpEvent`, `OSProjection`, `OSLabeledProjection`,
  `OSLocalAdapterContract` をそのまま使う
- QEMU や Linux KVM の trace format, tracepoint, hook 名は規定しない

Adapter layer:

- QEMU trace と Linux KVM trace を同じ projected interface に写す
- その前段で 2 backend の serial trace が 1 つの canonical captured artifact と
  一致することを確認する
- runtime が per-CPU capture substrate から作った merged row list を受け取り、
  それを proof-facing captured artifact として扱う
- backend ごとの capture path の違いを隠蔽し、同じ local contract family に属する
  witness をそれぞれ与える
- scheduler-irrelevant step を `EvStutter` に写す
- Awkernel の multicore topology 自体は adapter witness 側で扱い、
  common operational interface には持ち込まない

Runtime layer:

- 実際の trace source, hook placement, timer/IRQ/IPI capture, queue state
  extraction を持つ
- per-CPU buffer、global atomic `event_id`、optional debug `TSC`、
  overflow detection、dump-time merge を持つ
- これらは common interface の一部ではない

## Non-goals

- Awkernel の full operational semantics を与えない
- schedulability theorem を与えない
- hardware timer / interrupt routing / queue layout の仕様を固定しない
