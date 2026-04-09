# ロードマップ（実装反映版）

このロードマップは、現在の実装構成を踏まえて更新したものです。
単一CPUの抽象化と具体 policy、subset-aware な bridge、partitioned scheduling の基盤、periodic task model の骨格まではすでに整備されており、次の中心目標は **単一CPU EDF 最適性定理** です。

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

- **単一CPUの一般補題層の整備**
- **EDF 最適性定理**
- **task-level EDF 理論への接続**

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
- policy 一般の比較補題
- tie-break を含む dispatch 一般化の検討

---

# Phase 2: single-CPU bridge
**状態: 完了**

## 目的
dispatch 抽象から単一CPU scheduler 抽象へ接続する。

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
- 単一CPUでは `DispatchSchedulerBridge.v` が実質的に `UniSchedulerInterface` 相当の役割を担っている

## コメント
以前想定していた `UniSchedulerInterface.v` / `UniSchedulerLemmas.v` は、現状では独立ファイルではなく、この bridge 層に吸収されている。

---

# Phase 3: single-CPU concrete policy
**状態: EDF/FIFO は完了、他は未着手**

## 目的
単一CPU上の具体 policy を共通インターフェース上に載せる。

## 対応ファイル
- `theories/UniPolicies/EDF.v`
- `theories/UniPolicies/FIFO.v`
- `theories/FIFOExamples.v`
- `theories/SchedulableExamples.v`

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

## 未着手
- `RoundRobin.v`
- `PrioritizedFIFO.v`
- priority-based policy の一般枠組み

## 到達点
- EDF と FIFO は dispatch/spec/scheduler の流れで定義済み
- 具体 policy の拡張がしやすい構造になっている

---

# Phase 4: partitioned scheduling 基盤
**状態: かなり進んでいる**

## 目的
multicore のうち、partitioned scheduling の基礎理論を整備する。

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

## 到達点
- local single-CPU scheduler から global partitioned scheduler を構成できる
- local feasibility / validity から global feasibility を導く骨格がある
- `feasible_schedule_on (local_jobset c)` による subset-aware な局所理論へ修正済み

## 今後の補強候補
- `valid_partitioned_schedule` を「assignment respect + global validity を含む全部入り述語」に強化
- partitioned EDF の具体化
- task assignment と schedulability の接続

---

# Phase 5: periodic task model
**状態: 骨格は先行着手済み**

## 目的
task-level モデルから job-level 理論への接続の入口を作る。

## 対応ファイル
- `theories/PeriodicTasks.v`

## 実装済み
- `expected_release`
- `expected_abs_deadline`
- `generated_by_periodic_task`
- `periodic_job_model`
- `periodic_job_model_on`
- `implicit_deadline_tasks`
- `generated_implies_valid_job_of_task`

## 到達点
- periodic task から job を生成する骨格がある
- implicit deadline task の条件が分離されている

## コメント
この段階はまだ job 生成モデルであり、schedulability theory 本体ではない。
EDF 最適性定理のあとに、task-level 理論へ持ち上げるのが自然である。

---

# Phase 6: 単一CPUの一般補題層
**状態: 次の主目標**

## 目的
EDF 最適性定理に必要な一般補題と schedule 変換補題を整備する。

## ここで追加したいもの
- `service_job` / `completed` / `missed_deadline` に関する比較補題
- prefix/suffix に関する補題
- finite horizon ないし prefix ベースの議論の導入
- swap / exchange 用の schedule 変換補題
- 「EDF でない最初の時刻」を取り出す補題
- EDF 形への正規化補題

## ファイル案
- `theories/UniPolicies/EDFLemmas.v`
- 必要なら `theories/UniPolicies/ScheduleTransform.v`

## 到達点
- EDF 最適性証明に必要な下準備が揃う
- `EDF.v` を局所選択則の層に保ったまま、証明を分離できる

## 直近の具体タスク
1. `service_job` に関する prefix monotonicity を補題化する
2. completion と service の対応補題を整理する
3. 2 時刻の入れ替えが total service を保存する補題を作る
4. swap 後の deadline miss への影響を比較する補題を作る

---

# Phase 7: EDF 最適性定理
**状態: 次の中心マイルストーン**

## 目的
単一CPU・preemptive・独立 job 系で EDF の最適性を証明する。

## 位置づけ
このフェーズが、単一CPU scheduling theory の中心定理にあたる。

## 目標定理の候補
最初は subset-aware / single-CPU 版が自然である。

例:
- `feasible_on J jobs 1 -> schedulable_by_on J edf_scheduler jobs 1`

あるいは、より抽象的に
- feasible な単一CPU schedule が存在するなら、EDF 条件を満たす feasible schedule が存在する

## 証明方針
- feasible schedule を仮定する
- EDF でない最初の時刻を取る
- その時刻で deadline の早い job を前に出す swap を行う
- feasibility を壊さないことを示す
- これを繰り返して EDF 形へ正規化する

## ファイル案
- `theories/UniPolicies/EDFOptimality.v`

## 到達点
- 単一CPUにおいて EDF が最適であることを示せる
- 以後の periodic/sporadic task 理論の基準点になる

---

# Phase 8: task-level EDF 理論
**状態: EDF 最適性定理の後に着手**

## 目的
job-level EDF 理論を periodic task / sporadic task 理論に接続する。

## 追加したいもの
- utilization の定義
- task set の feasibility / schedulability
- implicit deadline periodic task に対する EDF 利用率定理
- job-level feasibility と task-level feasibility の橋渡し

## ファイル案
- `theories/PeriodicTasks.v` を拡張
- 必要なら `theories/UniPolicies/EDFTaskTheory.v`

## 到達点
- `PeriodicTasks.v` が単なる生成規則から schedulability theory へ進む
- classic EDF utilization result への土台ができる

---

# Phase 9: single-CPU policy の拡充
**状態: 未着手**

## 目的
EDF 以外の policy を同じ枠組みで拡張し、比較可能にする。

## 追加候補
- `theories/UniPolicies/RoundRobin.v`
- `theories/UniPolicies/PrioritizedFIFO.v`

## 追加したい定理
- FIFO が optimal でないことの反例
- RR の fairness / progress 系
- priority-based scheduler の一般補題

## 到達点
- single-CPU scheduling library としての厚みが増す
- EDF 以外の policy も理論化できる

---

# Phase 10: partitioned scheduling の強化
**状態: 基盤はある、次は具体理論**

## 目的
現在の `Partitioned.v` を基礎から具体 policy と定理へ伸ばす。

## 追加したいもの
- `valid_partitioned_schedule` の全部入り述語化
- partitioned EDF
- per-CPU local EDF から global schedulability を導く定理
- assignment respect を明示的に含む定義整理

## 到達点
- partitioned scheduling が「基礎定義」から「具体 policy theory」へ進む
- EDF を multicore 側へ拡張する第一歩になる

---

# Phase 11: global / clustered scheduling
**状態: 未着手**

## 目的
partitioned ではなく、共有 ready pool に基づく multicore scheduling を扱う。

## 追加候補
- global ready set
- top-`m` dispatch
- global EDF
- clustered scheduler

## コメント
これは単一CPU EDF 最適性や partitioned 基盤のあとに進むのが自然である。

---

# Phase 12: OS寄り operational model
**状態: 未着手**

## 目的
純粋な scheduling theory から、OS 寄り operational model へ拡張する。

## 追加候補
- runqueue
- current task
- wakeup / block / completion
- migration
- timer / IPI との接続

## 到達点
- abstract scheduler spec と concrete kernel scheduler の refinement へ進める

---

# Phase 13: DAG / refinement
**状態: 未着手**

## 目的
precedence や refinement を含む、より豊かなスケジューリングモデルへ進む。

## 追加候補
- DAG task / node-level semantics
- precedence constraints
- abstract model と concrete implementation の refinement

---

# 直近の優先順位

## 最優先
1. `EDFLemmas.v` を作る
2. schedule transform / swap 補題を整備する
3. `EDFOptimality.v` を作る

## その次
4. `PeriodicTasks.v` と EDF 理論を接続する
5. `RoundRobin.v` を追加する
6. `Partitioned.v` を partitioned EDF へ伸ばす

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
  concrete single-CPU policies

- `Partitioned.v`
  partitioned multicore scheduling の基礎

- `PeriodicTasks.v`
  periodic task 生成規則の骨格

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

- **Phase 6: 単一CPUの一般補題層**
- **Phase 7: EDF 最適性定理**

である。

その後、

- task-level EDF 理論
- Round Robin などの policy 拡充
- partitioned EDF
- global EDF

へ進むのが自然である。
