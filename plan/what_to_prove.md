# what_to_prove.md

# Proof Inventory and Next Theorems

このファイルの目的は、理論的に面白い定理を列挙することだけではなく、
**現在の実装に照らして、何が完了し、何が進行中で、何が未着手か**を明確にすることにある。

現在の実装は、すでに次の段階まで進んでいる。

- 共通 schedule / service / readiness / feasibility の基盤
- 単一CPU scheduler / scheduling algorithm abstraction
- generic canonical bridge
- generic normalization skeleton
- generic finite optimality skeleton
- EDF finite optimality
- LLF finite optimality
- partitioned scheduling の generic compose 層
- partitioned EDF / FIFO / RR / LLF wrapper
- multicore-common の初期層
- global EDF / LLF の初期層
- periodic task generation の初期層

したがって、このファイルでは
「証明すべきこと」を単なる未来の一覧ではなく、

- **Done**
- **In progress**
- **Planned**

に分けて整理する。

---

# 0. Reading Guide

## Status labels

- **Done**: 主要な定義・補題・定理がすでにコードにある
- **In progress**: 主要な骨格はあるが、整理や一般化がまだ必要
- **Planned**: まだ本格的な実装に入っていない

## Main tracks

今後の証明対象は、次の 7 系統に分けて考える。

1. 共通基盤
2. 単一CPU policy
3. repair / normalization / finite optimality
4. partitioned / multicore / global semantics
5. task-generation model
6. OS / delay / refinement
7. analysis and advanced guarantees

## Design principle for delay-aware proofs

遅延を扱うときでも、`Schedule` 自体はできるだけ純粋に保つ。

したがって、遅延は次のどこかに置く。

- task-generation 側の release jitter / arrival offset
- OS-like operational semantics 側の timer / wakeup / dispatch / migration latency
- refinement 側の bounded lag / bounded overhead
- analysis theorem 側の明示パラメータ

この整理により、zero-delay idealization を特殊化として回収しやすくする。

---

# Lv.0: Common schedule semantics
**Status: Mostly done**

ここは最下層であり、単一CPUでもマルチコアでも再利用される。

## 0-1. service / cpu_count basics
**Status: Done**

証明済みとして扱うもの:

- `runs_on_true_iff`, `runs_on_false_iff`
- `cpu_count_zero_iff_not_executed`
- `cpu_count_pos_iff_executed`
- `cpu_count_nonzero_iff_executed`
- `cpu_count_le_1` under sequential-job assumption
- `cpu_count_eq_1_iff_executed`
- `service_job_step`
- `service_job_monotone`
- `service_job_increase_at_most_1`
- `service_job_no_increase_if_not_executed`
- `service_job_increases_iff_executed`

## 0-2. completed / released / pending / ready consistency
**Status: Done**

証明済みとして扱うもの:

- `completed_not_pending`
- `completed_not_ready`
- `pre_release_not_pending`
- `pre_release_not_ready`
- `pending_after_release`
- `ready_after_release`
- `scheduled_implies_running`
- `valid_schedule` から release / completion / ready の整合性を引き出す補題群

## 0-3. deadline / feasibility basics
**Status: Done**

証明済みとして扱うもの:

- `completed_iff_service_ge_cost`
- `not_completed_iff_service_lt_cost`
- `missed_deadline_iff_not_completed_at_deadline`
- `missed_deadline_iff_service_lt_cost_at_deadline`

## 0-4. interval service
**Status: Done**

証明済みとして扱うもの:

- `service_between_eq`
- `service_between_0_r`
- `service_between_refl`
- `service_between_split`
- `service_between_nonneg`
- `service_before_release_zero`
- `service_at_release_zero`
- `service_increases_implies_executed_in_interval`

## 0-5. remaining cost / laxity basics
**Status: Mostly done**

証明済みとして扱うもの:

- `remaining_cost_le_cost`
- `completed_implies_remaining_cost_zero`
- `remaining_cost_zero_implies_completed`
- `not_completed_implies_remaining_cost_pos`
- `remaining_cost_step_running_uni`
- `remaining_cost_step_not_running_uni`
- `laxity_unfold`
- `completed_implies_laxity_deadline_minus_now`
- `laxity_step_running_uni`
- `laxity_step_not_running_uni`

残作業:

- 単一CPU向けだけでなく、multicore 共通形で remaining-cost / laxity をどこまで上げるか整理する
- dynamic metric policy 向けに、再利用しやすい補題セットへ整理する

---

# Lv.1: Single-CPU scheduler / algorithm abstraction
**Status: Mostly done**

ここでは「policy そのもの」よりも、
policy を抽象 scheduler / scheduling algorithm として扱うための基盤を指す。

## 1-1. scheduler interface basics
**Status: Done**

証明済みとして扱うもの:

- `schedulable_by_implies_feasible`
- `schedulable_by_implies_schedulable_by_on`
- `schedulable_by_on_monotone`
- `schedulable_by_on_intro`

## 1-2. algorithm-spec validity layer
**Status: Done**

証明済みとして扱うもの:

- `respects_algorithm_spec_at_with_in_candidates`
- `respects_algorithm_spec_at_with_implies_eligible`
- `respects_algorithm_spec_at_with_in_subset`
- `single_cpu_algorithm_spec_schedulable_by_on_intro`

## 1-3. algorithm-to-scheduler bridge
**Status: Done**

証明済みとして扱うもの:

- `single_cpu_algorithm_valid`
- `single_cpu_algorithm_eq_cpu0`
- `single_cpu_algorithm_idle_on_other_cpus`
- `single_cpu_algorithm_in_subset`
- `single_cpu_algorithm_some_if_subset_eligible`
- `single_cpu_algorithm_none_if_no_subset_eligible`
- `single_cpu_algorithm_schedulable_by_on_intro`

## 1-4. abstract refinement bridge
**Status: Done**

証明済みとして扱うもの:

- `single_cpu_algorithm_schedule_respects_algorithm_spec_at_with`
- `single_cpu_algorithm_schedule_respects_algorithm_spec_before`
- `single_cpu_algorithm_schedule_implies_single_cpu_algorithm_spec_schedule`

残作業:

- 単一CPU abstraction の説明を design documents と揃える
- 新 policy 追加時の最小 obligation をテンプレート化する

---

# Lv.2: Single-CPU policy local properties
**Status: In progress, with EDF / LLF largely mature**

## 2-1. FIFO
**Status: Mostly done**

証明済みとして扱うもの:

- eligible / none-if-no-eligible / some-if-exists
- candidate membership
- first-eligible property
- policy sanity
- chooser refines policy

残作業:

- FIFO を generic normalization / finite optimality に載せるかは要判断
- completion / waiting / fairness 系の inventory を追加する

## 2-2. Round Robin
**Status: Implemented, but theorem inventory still thin**

現状:

- policy 実装と example はある

残作業:

- local rotation correctness を inventory 上で明示する
- bounded waiting / fairness 的な定理を追加候補として整理する
- generic optimality pipeline に載せる対象かどうかを明確化する

## 2-3. EDF
**Status: Done for the finite optimality pipeline**

証明済みとして扱うもの:

- choose-EDF の局所性質
- canonicality decider
- one-step local repair
- finite-horizon normalization wrapper
- finite optimality wrapper

## 2-4. LLF
**Status: Done for the finite optimality pipeline**

証明済みとして扱うもの:

- choose-LLF の局所性質
- schedule-dependent canonicality decider
- one-step local repair
- finite-horizon normalization wrapper
- finite optimality wrapper

## 2-5. metric-based chooser layer
**Status: In progress**

現状:

- EDF / LLF を支える chooser infrastructure はある
- static metric / dynamic metric の両方が実例付きで存在する

残作業:

- `MetricChooser` を policy inventory 上の独立レイヤとして明示する
- 将来の LST などを見据えた obligation を整理する

## 2-6. prioritized FIFO / fixed-priority family
**Status: Not started**

候補:

- prioritized FIFO
- RM / DM
- fixed-priority ready-set chooser

---

# Lv.3: Repair / normalization / finite optimality
**Status: Done as a generic uniprocessor core**

ここはこのプロジェクトの単一CPU側の中核であり、
「未着手」ではなく **すでに中核部分が完成している層** とみなす。

## 3-1. policy-facing canonicality
**Status: Done generically, instantiated for EDF / LLF**

証明済みとして扱うもの:

- generic canonical bridge
- finite-horizon canonicality-to-scheduler-rel bridge
- policy-specific canonical predicates for EDF / LLF

## 3-2. local repair
**Status: Done generically, instantiated for EDF / LLF**

証明済みとして扱うもの:

- local one-step repair interface
- generic repair-pushes-forward lemma
- EDF local repair
- LLF local repair

## 3-3. finite-horizon normalization
**Status: Done generically, instantiated for EDF / LLF**

証明済みとして扱うもの:

- generic normalization theorem
- EDF normalization wrapper
- LLF normalization wrapper

## 3-4. finite optimality
**Status: Done generically, instantiated for EDF / LLF**

証明済みとして扱うもの:

- generic finite optimality skeleton
- EDF finite optimality theorem
- LLF finite optimality theorem

残作業:

- この 5 層構造
  1. chooser
  2. local properties
  3. local repair
  4. normalization
  5. finite optimality
  を `what_to_prove.md` 全体の標準テンプレートにする
- EDF / LLF 以外の policy へ適用するかどうかを個別に判断する

---

# Lv.4: Schedule transformation / prefix reasoning
**Status: Mostly done**

これは repair / normalization を支える共通補題層である。

## 4-1. prefix agreement
**Status: Done**

証明済みとして扱うもの:

- `agrees_before_*`
- service / completed / eligible / ready / remaining_cost / laxity の prefix invariance
- candidate / choose の prefix agreement に必要な基礎補題

## 4-2. schedule restriction / truncation
**Status: Done**

証明済みとして扱うもの:

- single-CPU restriction
- J-restriction
- truncation
- finite restricted schedule 補題群

## 4-3. schedule swapping / transformation
**Status: Mostly done**

証明済みとして扱うもの:

- `swap_at` 系の service preservation
- validity preservation
- feasibility preservation

残作業:

- transformation 補題の分類を整理し、
  repair 用 / generic schedule reasoning 用に章立てを分ける

---

# Lv.5: Partitioned multicore composition
**Status: In progress, but already substantial**

この層は「未着手」ではなく、すでに generic theorem layer が立ち上がっている。

## 5-1. partitioned local-to-global composition
**Status: Done for the generic witness-lifting core**

証明済みとして扱うもの:

- `glue_cpu_schedule_eq_local`
- `glue_other_cpus_idle_local_view`
- `glue_respects_assignment`
- `glue_valid_if_local_valid`
- local witness schedules から global partitioned schedule を作る定理
- local `schedulable_by_on` から partitioned `schedulable_by_on` への lifting

## 5-2. partitioned service localization
**Status: Done**

証明済みとして扱うもの:

- `service_partitioned_eq_local_service`
- `completed_partitioned_iff_local_completed`
- `eligible_local_implies_eligible_global_on_assigned_cpu`
- `global_running_implies_running_on_assigned_cpu`

## 5-3. partitioned policy wrappers
**Status: Done at the wrapper level**

証明済みとして扱うもの:

- partitioned EDF
- partitioned FIFO
- partitioned RR
- partitioned LLF
- `PartitionedPolicyLift.v` による wrapper theorem の共通化

## 5-4. partitioned EDF from local feasibility
**Status: Done**

証明済みとして扱うもの:

- local finite-job EDF feasibility から
  partitioned EDF `schedulable_by_on` を導く定理
- `PartitionedFiniteOptimalityLift.v` による finite-job lifting の generic entry point

## 5-5. remaining work for partitioned
**Status: In progress**

残作業:

- EDF 以外の policy についても
  「local feasible から partitioned schedulable_by_on」
  までをどこまで揃えるか決める
- partitioned を roadmap 上で「最初の multicore major result」として明示する
- 後段の delay-aware partitioned analysis に必要な theorem inventory を整理する

---

# Lv.6: Task-generation models
**Status: In progress at the periodic skeleton level**

## 6-1. Task / Job consistency
**Status: Done as a base-layer skeleton**

証明済みとして扱うもの:

- `Task`
- `job_task`, `job_index`
- `valid_job_of_task`

## 6-2. periodic task generation
**Status: Finite-horizon bridge and partitioned lift done**

証明済みとして扱うもの:

- expected release
- expected absolute deadline
- generated-by-periodic-task predicate
- periodic job model
- periodic job model on `J`
- implicit-deadline task predicate
- generated job -> `valid_job_of_task`
- `periodic_jobset_upto` + bool reflection (`PeriodicFiniteHorizon.v`)
- `PeriodicFiniteHorizonCodec` + `enum_periodic_jobs_upto` (sound/complete)
  (`PeriodicEnumeration.v`)
- `periodic_finite_optimality_lift` / `periodic_finite_optimality_lift_auto`:
  generic uniprocessor periodic finite-optimality lift (`PeriodicFiniteOptimalityLift.v`)
- `periodic_edf_optimality_on_finite_horizon` / `_auto`: EDF thin wrapper
  (`PeriodicEDFBridge.v`)
- `periodic_llf_optimality_on_finite_horizon` / `_auto`: LLF thin wrapper
  (`PeriodicLLFBridge.v`)
- `partitioned_periodic_finite_optimality_lift`: periodic → partitioned
  schedulability lift (`PeriodicPartitionedFiniteOptimalityLift.v`)

## 6-3. sporadic task generation
**Status: In progress**

Done:

- `earliest_sporadic_release`
- `generated_by_sporadic_task` + bool reflection + `generated_by_sporadic_task_b_spec`
- `sporadic_job_model_on` restructured to use generation predicate
- `sporadic_jobset_upto` updated to use generation predicate
- periodic → sporadic bridge: `generated_by_periodic_implies_sporadic`,
  `periodic_model_satisfies_separation`, `periodic_model_implies_sporadic_model`

Remaining:

- finite-horizon index-bound lemma
  (sporadic lacks a codec; releases are not determined by (task, index) alone)
- utilization / dbf hooks
- release jitter extensions (see 6-4)

## 6-4. release jitter / arrival offset
**Status: Not started**

予定:

- bounded release jitter
- phase / offset model
- expected release と actual release の関係
- periodic / sporadic generation への拡張

重要点:

- release jitter は analysis 層に直接押し込まず、
  まず task-generation semantics として定義する

## 6-5. periodic / sporadic schedulability analysis hooks
**Status: Not started**

予定:

- finite-horizon extraction lemmas
- utilization-related helper lemmas
- Liu & Layland 型の定理に接続する前段補題

注意:

- ここは「generation semantics」と「analysis theorem」を分けて管理する

---

# Lv.7: Multicore-common semantics beyond partitioned
**Status: Initial layer done**

## 7-1. cpu-local views and no-duplication bridge
**Status: Done**

証明済みとして扱うもの:

- `cpu_schedule`
- `no_duplication <-> sequential_jobs`
- idle / busy / all-cpus-idle
- globally-runnable 関連補題

## 7-2. affinity / admissible CPU
**Status: Generic admissibility layer done**

証明済みとして扱うもの:

- `all_cpus_admissible` / `singleton_admissibility` / `eligible_on_cpu` / `admissible_somewhere`
- all-cpus-admissible の変換補題:
  - `eligible <-> admissible_somewhere`
  - `admissible_somewhere -> eligible`
  - `~ admissible_somewhere -> ~ eligible`
  - `valid_schedule -> running -> admissible_somewhere`
- `AdmissibleCandidateSourceSpec`
- `StrongAdmissibleCandidateSourceSpec`
- generic `adm` work-conserving lemmas in `TopMAdmissibilityBridge.v`

残作業:

- allowed-CPU / affinity invariants
- migration 制約と接続する補題
- richer candidate-source instantiation examples

## 7-3. multicore service / completion under migration
**Status: Initial layer only**

残作業:

- migration を許したときの service / completion / remaining-cost 一貫性
- global / clustered で再利用できる補題層の整備

---

# Lv.8: Global / clustered scheduling
**Status: Initial global EDF/LLF layers exist**

## 8-1. global scheduling
**Status: In progress at the initial theorem-layer stage**

証明済みとして扱うもの:

- `TopMSchedulerBridge.v` の generic bridge:
  - `top_m_algorithm_valid`
  - `top_m_algorithm_idle_outside_range`
  - `top_m_algorithm_no_duplication`
  - subset-aware theorem layer
- `TopMAdmissibilityBridge.v` generic bridge
- `GlobalEDF.v`:
  - `global_edf_scheduler`
  - `global_edf_valid`
  - `global_edf_idle_outside_range`
  - `global_edf_no_duplication`
  - subset soundness / idle-if-no-eligible / busy-if-eligible
  - idle CPU exists -> eligible subset job is already running
  - admissibility-aware wrappers
  - `schedulable_by_on` intro lemma
- `GlobalLLF.v`:
  - `global_llf_scheduler`
  - `global_llf_valid`
  - `global_llf_idle_outside_range`
  - `global_llf_no_duplication`
  - EDF と同型の subset-aware theorem layer
  - admissibility-aware wrappers

残作業:

- wrapper layer documentation and API stabilization
- global policy results を EDF 以外へ一般化できるところまで切り出す
- analysis theorem の前段となる theorem inventory を明示する
- richer affinity instantiation examples

注:

- `running -> admissible_somewhere` は現実装では無条件ではなく、`valid_schedule` 前提つきで使う

## 8-2. clustered scheduling
**Status: Not started**

候補:

- cluster-local global scheduling
- cluster confinement
- partitioned と global の中間モデル

## 8-3. global dynamic-metric policies
**Status: Initial layer exists**

候補:

- global LLF の解析定理層
- migration-aware dynamic metric

---

# Lv.9: DAG / node-level semantics
**Status: Not started**

この層は periodic task の延長ではなく、
**job 内部構造の拡張** として扱う。

## 9-1. node model
**Status: Not started**

予定:

- `NodeId`
- node-level service
- node-level completed
- node-level ready
- precedence constraints

## 9-2. schedule model migration
**Status: Not started**

予定:

- `Schedule : Time -> CPU -> option JobId`
  から
  `option NodeId` または `option (JobId * NodeId)` への拡張

## 9-3. job-level semantics との接続
**Status: Not started**

予定:

- job completion と node completion の関係
- job-level work と node-level work の関係
- no-duplication の node-level 化

---

# Lv.10: OS-like operational semantics
**Status: Not started**

## 10-1. machine / scheduler state
**Status: Not started**

予定:

- per-CPU current
- per-CPU runqueue / global runqueue
- wakeup / block / completion
- migration
- reschedule IPI
- timer / quantum / preemption

## 10-2. trace semantics
**Status: Not started**

予定:

- machine trace
- step relation
- trace-level event labels
- abstract schedule への projection

## 10-3. explicit operational delay sources
**Status: Not started**

予定:

- dispatch / context-switch overhead
- timer latency
- wakeup latency
- migration latency
- remote reschedule / IPI latency
- bounded non-preemptive windows if needed

重要点:

- これらは core `Schedule` の定義に埋め込まず、
  operational semantics 上の明示的パラメータまたは relation として置く

---

# Lv.11: Delay / overhead model
**Status: Not started**

この層は analysis のための補助概念であり、
core schedule semantics と OS operational semantics の中間に置く。

## 11-1. delay taxonomy
**Status: Not started**

定義候補:

- release jitter bound
- blocking bound
- dispatch overhead bound
- timer latency bound
- wakeup latency bound
- migration latency bound

## 11-2. delay accounting lemmas
**Status: Not started**

予定:

- delay budget の単調性
- より大きい bound への monotonicity
- zero-delay simplification
- independent delay sources の加法的合成条件

## 11-3. abstract/operational consistency lemmas
**Status: Not started**

予定:

- operational trace から得た遅延が abstract 側の bound に収まること
- projection lag が bounded であること
- ideal schedule と actual schedule の差分を定量化する補題

---

# Lv.12: Refinement
**Status: Partially done only at the abstract single-CPU bridge level**

## 12-1. abstract policy -> executable single-CPU scheduler
**Status: Done**

これは現在の single-CPU algorithm/scheduler bridge でほぼ達成済みとみなす。

## 12-2. executable scheduler -> operational scheduler
**Status: Planned**

予定:

- chooser/algorithm の決定が operational state machine に実装されること
- runqueue / current / event handling が抽象選択を実現すること

## 12-3. bounded-delay refinement
**Status: Planned**

予定:

- operational scheduler が ideal abstract schedule から高々 δ だけ遅れる
- dispatch / wakeup / timer / migration delay を合成した lag bound
- zero-delay case では exact refinement に落ちること

## 12-4. partitioned refinement
**Status: Planned**

予定:

- per-CPU concrete scheduler が abstract partitioned scheduler を実現する

## 12-5. global refinement
**Status: Planned**

予定:

- global queue / heap / balancing 実装が abstract global scheduling を実現する

## 12-6. service refinement
**Status: Planned**

予定:

- operational trace の execution count = abstract service
- bounded-delay projection 下での service gap bound

## 12-7. schedule refinement
**Status: Planned**

予定:

- machine trace から得た schedule が abstract policy schedule を満たす
- あるいは bounded-lag version を満たす

---

# Lv.13: Analysis and advanced guarantees
**Status: Mostly planned**

## 13-1. idealized uniprocessor / partitioned analysis
**Status: Planned**

候補:

- idealized partitioned EDF / fixed-priority response-time analysis
- idealized completion guarantees
- zero-overhead / zero-jitter baseline theorems

## 13-2. delay-aware response-time analysis
**Status: Planned**

候補:

- `R = C + interference + blocking + overhead (+ jitter)` 型の上界
- partitioned response-time bound with local delay parameters
- global interference reasoning with explicit delay budgets
- bounded tardiness / speedup 系への接続

## 13-3. periodic / sporadic analysis theorems
**Status: Planned**

候補:

- utilization lemmas
- Liu & Layland 型の定理
- periodic EDF / RM 系の定理
- release jitter を含む拡張版

## 13-4. policy comparison
**Status: Planned**

候補:

- EDF vs LLF
- FIFO vs RR
- partitioned vs global
- idealized vs delay-aware guarantees

## 13-5. zero-delay specialization theorems
**Status: Planned**

候補:

- 一般の delay-aware theorem から zero-delay corollary を導く
- idealized theorem と delay-aware theorem の対応を明文化する

---

# Recommended next proof priorities

## Priority 1
`Lv.5 Partitioned` を theorem inventory として整理し直す。

## Priority 2
`Lv.6 Task-generation` を periodic / sporadic / release jitter まで前倒しで強化する。

## Priority 3
`Lv.10 OS-like operational semantics` と `Lv.11 Delay / overhead model` の骨格を入れる。

## Priority 4
`Lv.12 Refinement` で bounded-delay refinement を設計する。

## Priority 5
その上で `Lv.13 Analysis` として idealized / delay-aware response-time analysis に進む。

---

# One-line summary

単一CPUの generic optimality core はすでに主要部分が完成している。
今後の主戦場は、

- partitioned の theorem-layer completion
- periodic/sporadic/release-jitter generation strengthening
- multicore-common semantics
- OS / delay / refinement
- idealized / delay-aware analysis

である。