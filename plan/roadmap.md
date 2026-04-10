# ロードマップ（scheduler semantics / dispatcher refinement 中心版）

このロードマップは、現在の実装構成を踏まえつつ、今後の重心を

- **解析結果を増やすこと**
ではなく、
- **実行可能な scheduler semantics を整備すること**
- **abstract policy と concrete dispatcher の refinement を証明すること**
- **single-CPU から multicore / OS semantics へ自然に拡張すること**

に移した版である。

単一CPUの抽象化と具体 policy、subset-aware な bridge、partitioned scheduling の基盤、periodic task model の骨格まではすでに整備されている。
したがって今後は、**EDF 最適性定理そのもの**を中心定理として保ちつつも、それを

- 実行可能な dispatcher
- scheduler validity
- multicore semantics
- OS 寄り operational model

へ接続する方向で発展させる。

---

## 現在地の要約

現状の実装は、概ね次の段階まで到達している。

- 共通基盤 (`Base.v`, `ScheduleModel.v`, `SchedulerInterface.v`)
- dispatch 抽象 (`DispatchInterface.v`, `DispatchLemmas.v`, `DispatchClassicalLemmas.v`)
- single-CPU bridge (`DispatchSchedulerBridge.v`)
- single-CPU concrete policy (`UniPolicies/EDF.v`, `UniPolicies/FIFO.v`)
- partitioned scheduling の基礎 (`Partitioned.v`)
- periodic task model の骨格 (`PeriodicTasks.v`)

したがって、次の中核マイルストーンは

- **single-CPU scheduler semantics の整理**
- **dispatcher refinement の導入**
- **EDF 最適性定理の完成**
- **multicore / OS semantics への接続**

である。

---

# Phase 0: 共通基盤
**状態: ほぼ完了**

## 目的
以後の理論・実装の共通土台を安定化する。

## 対応ファイル
- `theories/Base.v`
- `theories/ScheduleModel.v`
- `theories/SchedulerInterface.v`

## 実装済み
- `Time`, `CPU`, `TaskId`, `JobId`
- `Task`, `Job`
- `Schedule`
- `released`, `pre_release`
- `service_job`, `cpu_count`, `runs_on`
- `completed`, `eligible`, `ready`
- `valid_schedule`
- `missed_deadline`, `feasible_schedule`, `feasible`
- `feasible_schedule_on`, `feasible_on`
- `Scheduler`, `schedulable_by`, `schedulable_by_on`

## 到達点
- 単一CPU/マルチCPUの両方に使える共通基盤がある
- `feasible` と `schedulable` の整理が入っている
- subset 版の述語も導入済み

## 今後の補強候補
- `completed` / `service_job` / `runs_on` に関する基本補題の追加整理
- `valid_schedule` の使い方に関する補題の体系化
- `service` と `completion` の抽象的な比較補題の整理

---

# Phase 1: dispatch 抽象
**状態: 完了**

## 目的
policy 非依存な dispatch 抽象を与える。

## 対応ファイル
- `theories/DispatchInterface.v`
- `theories/DispatchLemmas.v`
- `theories/DispatchClassicalLemmas.v`

## 実装済み
- `GenericDispatchSpec`
- `candidates` ベースの dispatch 抽象
- chosen job の eligible 性
- `Some/None` の一般補題
- `candidates_sound`
- `candidates_complete`
- 古典論理依存補題の分離

## 到達点
- concrete policy は generic dispatch spec を満たすものとして定義できる
- bridge 層や partitioned 層がこの抽象を再利用できる

## 今後の補強候補
- tie を許す一般化
- policy 間比較に使う一般補題
- executable chooser のための有限候補集合ベースの補題整理

---

# Phase 2: scheduler validity と bridge の整理
**状態: 完了、ただし再整理の余地あり**

## 目的
dispatch 抽象から単一CPU scheduler 抽象へ接続し、
「policy」と「schedule がその policy を満たすこと」を分けて整理する。

## 対応ファイル
- `theories/DispatchSchedulerBridge.v`

## 実装済み
- `CandidateSource`
- `CandidateSourceSpec`
- `single_cpu_dispatch_schedule`
- `single_cpu_dispatch_valid`
- `single_cpu_dispatch_scheduler_on`
- inspection lemmas
  - `single_cpu_dispatch_eq_cpu0`
  - `single_cpu_dispatch_idle_on_other_cpus`
  - `single_cpu_dispatch_in_subset`
  - `single_cpu_dispatch_some_if_subset_eligible`
  - `single_cpu_dispatch_none_if_no_subset_eligible`
- `single_cpu_dispatch_schedulable_by_on_intro`

## 到達点
- dispatch spec から subset-aware な single-CPU scheduler を構成できる
- 現状の bridge 層が、単一CPU scheduler semantics の入口になっている

## 今後の補強候補
- `respects_policy_at` のような「局所的に policy を満たす」述語の明示化
- `valid_schedule` と `respects_policy_at` の役割分担の整理
- 将来的な `SchedulerValidity.v` / `PolicyValidity.v` 相当の層への分離検討

---

# Phase 3: single-CPU executable scheduler semantics
**状態: EDF/FIFO は着手済み、理論化はこれから**

## 目的
単一CPU上で、
- abstract policy
- concrete dispatcher
- scheduler validity
を分けつつ、相互関係を明示する。

## 対応ファイル
- `theories/UniPolicies/EDF.v`
- `theories/UniPolicies/FIFO.v`

## 実装済み

### EDF
- `min_dl_job`
- `choose_edf`
- `choose_edf_eligible`
- `choose_edf_min_deadline`
- `choose_edf_some_if_exists`
- `choose_edf_complete`
- `choose_edf_optimal`
- `choose_edf_unique_min`
- `edf_generic_spec`
- `EDFSchedulerSpec`
- `edf_scheduler`

### FIFO
- `choose_fifo`
- FIFO 用 generic dispatch spec
- first-eligible 系の局所性質
- `fifo_scheduler`

## この phase で追加したいこと
- EDF/FIFO を「policy」として明確化する
- `choose_*` を「その policy を実装する concrete dispatcher」として位置付ける
- tie を含む場合の仕様を dispatcher 側ではなく policy 側で吸収する
- `scheduler` を「dispatch の実行結果」ではなく「policy validity を満たす schedule」としても見られるようにする

## ファイル案
- `theories/PriorityPolicy.v`
- `theories/SchedulerValidity.v`
- 既存 `UniPolicies/*.v` は concrete policy / dispatcher 実装層として維持

## 到達点
- EDF/FIFO が単なる chooser ではなく、明示的な scheduler semantics を持つ
- 今後 RR / prioritized FIFO / FP を同じ枠組みで追加しやすくなる

---

# Phase 4: dispatcher refinement
**状態: 今後の主要追加ポイント**

## 目的
abstract policy と concrete dispatcher の関係を、
「この chooser がこの policy を実装している」という refinement として定式化する。

## ここで追加したいもの
- `dispatcher_refines_policy`
- `schedule_generated_by_dispatcher`
- `dispatcher_implements_scheduler_validity`
- `deterministic_dispatcher`
- `tie_break_refinement`

## 典型的な定理
- `choose_edf` が EDF policy を実装する
- `choose_fifo` が FIFO policy を実装する
- `single_cpu_dispatch_schedule` が対応する scheduler validity を満たす

## ファイル案
- `theories/DispatcherRefinement.v`

## 到達点
- abstract scheduling theory と executable scheduler が明示的に接続される
- 以後の multicore / OS semantics でも「実装が理論を満たす」という形を再利用できる

---

# Phase 5: EDF 一般補題層と schedule transform
**状態: 次の主目標**

## 目的
EDF 最適性定理に必要な一般補題と schedule 変換補題を整備する。

## ここで追加したいもの
- `service_job` / `completed` / `missed_deadline` に関する比較補題
- prefix/suffix に関する補題
- finite horizon ないし prefix ベースの議論
- swap / exchange 用の schedule 変換補題
- 「EDF でない最初の時刻」を取り出す補題
- EDF 形への正規化補題

## ファイル案
- `theories/UniPolicies/EDFLemmas.v`
- `theories/UniPolicies/ScheduleTransform.v`

## 到達点
- EDF 最適性の証明部を、局所選択則の定義から分離できる
- 後で RR/FIFO/FP や multicore にも流用できる変換補題の核ができる

## 直近の具体タスク
1. `service_job` に関する prefix monotonicity を補題化する
2. completion と service の対応補題を整理する
3. 2 時刻の入れ替えが total service を保存する補題を作る
4. swap 後の deadline miss への影響を比較する補題を作る
5. finite candidate ベースで first violation を取り出す補題を作る

---

# Phase 6: EDF 最適性定理
**状態: 次の中心マイルストーン**

## 目的
単一CPU・preemptive・独立 job 系で EDF の最適性を証明する。

## 位置づけ
このフェーズは、
- 単一CPU scheduling theory の中心定理
であると同時に、
- dispatcher refinement を持つ理論の最初の成功例
でもある。

## 目標定理の候補
最初は subset-aware / single-CPU 版が自然である。

例:
- `feasible_on J jobs 1 -> schedulable_by_on J edf_scheduler jobs 1`

あるいは、より抽象的に
- feasible な単一CPU schedule が存在するなら、EDF policy を満たす feasible schedule が存在する

さらに refinement つきには
- `choose_edf` が生成する schedule が EDF validity を満たす
- feasible なら EDF dispatcher による schedule でも feasible

## 証明方針
- feasible schedule を仮定する
- EDF でない最初の時刻を取る
- その時刻で deadline の早い job を前に出す swap を行う
- feasibility を壊さないことを示す
- これを繰り返して EDF 形へ正規化する
- 最後に concrete dispatcher と abstract EDF validity を接続する

## ファイル案
- `theories/UniPolicies/EDFOptimality.v`

## 到達点
- 単一CPUにおいて EDF が最適であることを示せる
- abstract policy と executable dispatcher の両方にまたがる代表定理ができる

---

# Phase 7: single-CPU policy family の拡充
**状態: 未着手**

## 目的
EDF 以外の policy を同じ枠組みで拡張し、比較可能にする。

## 追加候補
- `theories/UniPolicies/RoundRobin.v`
- `theories/UniPolicies/PrioritizedFIFO.v`
- 必要なら `theories/UniPolicies/FixedPriority.v`

## 追加したい理論
- FIFO が optimal でないことの反例
- RR の fairness / progress 系
- priority-based scheduler の一般補題
- 各 policy に対する refinement 定理
- policy class 間の包含・差異の整理

## 到達点
- single-CPU scheduling library としての厚みが増す
- 単なるアルゴリズム集ではなく、scheduler family の理論になる

---

# Phase 8: partitioned multicore semantics
**状態: 基盤はかなり進んでいる**

## 目的
multicore の第一段階として、partitioned scheduling を
「解析対象」ではなく「意味論対象」として整備する。

## 対応ファイル
- `theories/Partitioned.v`

## 実装済み
- `cpu_schedule`
- `local_candidates`
- `partitioned_schedule_on`
- `valid_partitioned_schedule`
- `local_jobset`
- `local_candidates_of`
- `local_candidates_spec`
- `partitioned_schedule_implies_respects_assignment`
- `partitioned_implies_sequential`
- `service_decomposition`
- `completed_iff_on_assigned_cpu`
- `missed_deadline_iff_on_assigned_cpu`
- `local_feasible_on_implies_global_feasible_on`
- `local_valid_feasible_on_implies_global`
- `partitioned_scheduler`
- `partitioned_schedulable_by_on_intro`

## この phase で追加したいこと
- `valid_partitioned_schedule` を「assignment respect + local validity + global validity」を含む全部入り述語として整理する
- local scheduler validity と global scheduler validity の関係を体系化する
- local dispatcher refinement から global dispatcher refinement を導く
- partitioned EDF / FIFO / RR を同一枠組みで載せる

## 到達点
- partitioned scheduling が「single-CPU scheduler の寄せ集め」ではなく、明示的な multicore semantics を持つ
- multicore 拡張の最初の安定基盤になる

---

# Phase 9: global / clustered multicore semantics
**状態: 未着手**

## 目的
partitioned ではなく、共有 ready pool に基づく multicore scheduling を扱う。

## 追加候補
- global ready set
- top-`m` dispatch
- global EDF
- clustered scheduler
- CPU 選択と job 選択の分離

## ここでの主要論点
- 単一CPUと違い「1つ選ぶ」ではなく「上位 m 個を選ぶ」必要がある
- job 選択と CPU 割当てが独立かどうか
- simultaneous dispatch の意味論
- work-conserving を multicore でどう定義するか

## ファイル案
- `theories/Global.v`
- `theories/Clustered.v`

## 到達点
- partitioned と global を同じ `Schedule` 抽象上で比較できる
- multicore scheduler semantics の本格的な一般化が始まる

---

# Phase 10: affinity / migration / assignment semantics
**状態: 未着手**

## 目的
multicore scheduling における assignment, affinity, migration を明示的に扱う。

## 追加候補
- affinity 制約
- migration 許可・禁止
- cost-free migration model
- migration-aware validity
- assignment-preserving refinement

## ファイル案
- `theories/Affinity.v`
- `theories/Migration.v`

## 到達点
- partitioned / global / clustered を、assignment と migration の観点から統一的に理解できる
- 将来的な OS 寄りモデルの runqueue / wakeup / rebalance に接続しやすくなる

---

# Phase 11: OS寄り operational model
**状態: 未着手**

## 目的
純粋な scheduling theory から、OS 寄り operational semantics へ拡張する。

## 追加候補
- runqueue
- current task
- wakeup / block / completion
- dispatch point
- preemption point
- migration event
- timer / IPI との接続
- context switch の抽象

## ここでの狙い
- schedule を「完成した関数」として見るだけでなく、
  scheduler state の遷移として記述する
- abstract scheduler spec と concrete kernel scheduler の refinement へ進む
- 将来的に async task / kernel thread / interrupt 駆動の統合へ繋げる

## ファイル案
- `theories/Operational/RunQueue.v`
- `theories/Operational/DispatchStep.v`
- `theories/Operational/Wakeup.v`
- `theories/Operational/Preemption.v`

## 到達点
- scheduling theory と kernel scheduler implementation の距離が大きく縮まる
- このプロジェクト固有の価値が最も強く出る段階になる

---

# Phase 12: task model は「解析本体」ではなく adapter として接続する
**状態: periodic 骨格はあり、理論化は後段**

## 目的
task-level モデルを本体ではなく adapter として接続する。

## 対応ファイル
- `theories/PeriodicTasks.v`

## 位置づけ
この段階では、periodic / sporadic / implicit deadline などは
scheduler semantics の上に乗る task model として扱う。

## 追加したいもの
- job-level semantics と task-level assumptions の橋渡し
- periodic task から job stream を得る構成
- utilization などの task-level 指標
- 必要なら schedulability result への adapter

## コメント
ここでは「EDF 利用率定理を増やすこと」が主目的ではない。
主目的は、task model が scheduler semantics のどこに接続するかを明確化することである。

## 到達点
- task model が scheduler semantics の上位層として整理される
- 将来的に analysis を追加する場合も、本体を壊さずに接続できる

---

# Phase 13: DAG / precedence / refinement
**状態: 未着手**

## 目的
precedence や refinement を含む、より豊かなスケジューリングモデルへ進む。

## 追加候補
- DAG task / node-level semantics
- precedence constraints
- release dependency
- abstract model と concrete implementation の refinement
- policy refinement と implementation refinement の二層化

## 到達点
- 単純な独立 job 系を超えた一般モデルに入れる
- scheduler semantics ライブラリとしての一般性が大きく上がる

---

# Phase 14: analysis adapter
**状態: 後回し**

## 目的
必要になったときに、response-time analysis や schedulability analysis を
本体に後付けできるようにする。

## 方針
- analysis を本体に埋め込まない
- scheduler semantics / dispatcher refinement / multicore semantics を先に固める
- 解析は adapter として後から接ぐ

## 追加候補
- busy-window 的な抽象
- interference / workload 的な抽象
- task-level schedulability result への接続

## 到達点
- このプロジェクトは「解析ライブラリ」ではなく
  「scheduler semantics の共有基盤」であり続ける
- 必要なら Prosa 的な解析とも補完関係を作れる

---

# 直近の優先順位

## 最優先
1. `PriorityPolicy` / `SchedulerValidity` / `DispatcherRefinement` の責務分担を決める
2. `EDFLemmas.v` を作る
3. `ScheduleTransform.v` を作る
4. `EDFOptimality.v` を作る
5. `choose_edf` が EDF policy を実装する refinement 定理を書く

## その次
6. `RoundRobin.v` / `PrioritizedFIFO.v` を追加する
7. `Partitioned.v` を local/global validity を明示する形で整理する
8. partitioned EDF の refinement を作る
9. `Global.v` / `Clustered.v` の最小骨格を導入する

## さらにその次
10. affinity / migration の意味論を追加する
11. OS 寄り operational semantics を追加する
12. periodic/sporadic task model を adapter として接続する

---

# 現在のファイル構成に基づく見取り図

- `Base.v`
  基本型、Task/Job、task-job 整合性

- `ScheduleModel.v`
  service / completion / eligible / ready / feasible

- `SchedulerInterface.v`
  `Scheduler`, `schedulable_by`, `schedulable_by_on`

- `DispatchInterface.v`
  generic dispatch 抽象

- `DispatchLemmas.v`, `DispatchClassicalLemmas.v`
  dispatch 一般補題

- `DispatchSchedulerBridge.v`
  single-CPU bridge と subset-aware scheduler 構成

- `UniPolicies/EDF.v`, `UniPolicies/FIFO.v`
  concrete single-CPU policies / dispatcher 実装

- `Partitioned.v`
  partitioned multicore scheduling の基礎

- `PeriodicTasks.v`
  periodic task 生成規則の骨格

## 今後追加したい中核ファイル
- `PriorityPolicy.v`
- `SchedulerValidity.v`
- `DispatcherRefinement.v`
- `UniPolicies/EDFLemmas.v`
- `UniPolicies/ScheduleTransform.v`
- `UniPolicies/EDFOptimality.v`
- `Global.v`
- `Clustered.v`
- `Affinity.v`
- `Migration.v`
- `Operational/*`

---

# 要約

現在の実装は、

- 共通基盤
- dispatch 抽象
- single-CPU bridge
- EDF/FIFO
- partitioned 基礎
- periodic 骨格

まで到達している。

したがって、次の中核マイルストーンは

- **Phase 3: single-CPU executable scheduler semantics**
- **Phase 4: dispatcher refinement**
- **Phase 5: EDF 一般補題層と schedule transform**
- **Phase 6: EDF 最適性定理**

である。

その後は、

- single-CPU policy family の拡充
- partitioned multicore semantics
- global / clustered multicore semantics
- affinity / migration
- OS寄り operational model

へ進むのが自然である。

このロードマップの主眼は、
**解析結果を増やすことではなく、実行可能な scheduler semantics と dispatcher refinement を核に、single-CPU から multicore / OS semantics へ伸ばすこと**
である。

# Prosa と本プロジェクトの差分

- **Prosa**
  - 主目標は、機械検証された **schedulability analysis** の共有基盤
  - 重心は、priority / schedule / workload / interference / busy-window / RTA
  - EDF も扱うが、主役は「解析結果の蓄積」
  - 主な利用者は real-time systems **researchers**
  - multicore もあるが、前面に出るのは主に analysis 側

- **本プロジェクト**
  - 主目標は、**実行可能な scheduler semantics** の定式化
  - 重心は、policy / scheduler validity / dispatcher / dispatcher refinement
  - EDF は、最適性だけでなく **concrete dispatcher (`choose_edf`) まで接続**
  - single-CPU から **partitioned / global / clustered / affinity / migration** へ伸ばす
  - 最終的には **OS 寄り operational semantics**（runqueue, wakeup, preemption, timer/IPI）へ接続する

## 一言でいうと

- **Prosa** は
  **「検証済み schedulability analysis の共有基盤」**

- **本プロジェクト** は
  **「実行可能な scheduler semantics と dispatcher refinement の共有基盤」**

## このプロジェクトの立ち位置

本プロジェクトは、Prosa と競合して解析結果を増やすことを目標にするのではなく、

1. abstract policy を定義する
2. schedule validity を定義する
3. concrete dispatcher がその policy を実装することを示す
4. それを multicore / OS semantics へ拡張する

という方向を取る。

## 差別化ポイント

- analysis-centered ではなく **semantics/refinement-centered**
- EDF を「定理」で終えず、**executable chooser** まで落とす
- multicore を「解析対象」ではなく **意味論対象**として早期に扱う
- 将来的に **kernel scheduler implementation への refinement** を見据える