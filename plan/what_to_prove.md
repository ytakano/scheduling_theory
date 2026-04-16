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
- periodic / sporadic / jittered-periodic task generation の初期層
- Periodic EDF idealized-analysis の stable entry-point
- minimal operational projection slice

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

現状では、Periodic EDF idealized-analysis inventory の stable entry-point 化は
完了済みとして扱う。次の uniprocessor analysis 側の主戦場は、
zero-offset classical EDF corollary、infinite-time periodic EDF wrapper、
そして LLF analytical bridge である。

## Current periodic EDF wrapper direction

- finite-horizon window-DBF theorems remain the proof core
- infinite-time periodic EDF should be exposed as a wrapper over that core
- public bridge assumptions remain bridge-first rather than auto-deriving `no_carry_in`

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

multicore-common 側で追加済みとして扱うもの:

- `remaining_cost_eq_job_cost_minus_service_sum`
- `remaining_cost_step_running_mc`
- `remaining_cost_step_not_running_mc`
- `laxity_unfold_service_sum`
- `laxity_step_running_mc`
- `laxity_step_not_running_mc`

残作業:

- dynamic metric policy 向けに、再利用しやすい補題セットへ整理する
- `GlobalLLF.v` や multicore interference hook が必要とする補題粒度を見極める

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
**Status: Generic theorem layer done, public inventory stabilized**

この層は「未着手」ではなく、すでに reusable theorem layer が立ち上がっている。

## 5-1. partitioned local-to-global composition
**Status: Done for the generic witness-lifting core**

証明済みとして扱うもの:

- `glue_cpu_schedule_eq_local`
- `glue_other_cpus_idle_local_view`
- `glue_respects_assignment`
- `glue_valid_if_local_valid`
- `local_witnesses_imply_partitioned_schedulable_by_on`
- `local_schedulable_by_on_implies_partitioned_schedulable_by_on`
- `glue_feasible_on_if_local_feasible_on`

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
- EDF / LLF は finite-optimality-ready policy
- FIFO / RR は wrapper-only policy

## 5-4. partitioned EDF from local feasibility
**Status: Done**

証明済みとして扱うもの:

- local finite-job EDF feasibility から
  partitioned EDF `schedulable_by_on` を導く定理
- `PartitionedFiniteOptimalityLift.v` による finite-job lifting の generic entry point
- `partitioned_periodic_finite_optimality_lift`
- `partitioned_sporadic_finite_optimality_lift_with_witness`
- `partitioned_jittered_periodic_finite_optimality_lift_with_witness`

## 5-5. partitioned LLF from local feasibility
**Status: Done**

証明済みとして扱うもの:

- local finite-job LLF feasibility から
  partitioned LLF `schedulable_by_on` を導く定理
- EDF と同じ generic finite-optimality lift を再利用する thin wrapper

## 5-6. existing major-result entry points
**Status: Done**

証明済みとして扱うもの:

- `PartitionedEntryPoints.v` が stable downstream import を提供する
- `Examples/PartitionedExamples.v` が canonical example inventory を提供する
- curated examples は次を 1 箇所から辿れる
  - local witness → partitioned EDF
  - local schedulable → partitioned EDF
  - local feasible → partitioned EDF / LLF
  - periodic / sporadic / jittered periodic → partitioned EDF

## 5-7. remaining work for partitioned
**Status: In progress**

残作業:

- FIFO / RR を finite-optimality pipeline に載せるかどうかを判断する
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
- release/index uniqueness lemmas for periodic generation
  (`PeriodicReleaseLemmas.v`)
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
- finite-horizon release lower-bound / expected-release-below-horizon /
  index-below-horizon lemmas
- shared finite-horizon witness abstraction plus a sporadic specialization for
  manual enumeration
- periodic → sporadic bridge: `generated_by_periodic_implies_sporadic`,
  `periodic_model_satisfies_separation`, `periodic_model_implies_sporadic_model`

Remaining:

- utilization / dbf hooks
- release jitter extensions (see 6-4)

Design note:

- sporadic still lacks an automatic codec because releases are not determined by
  `(task, index)` alone
- finite-horizon lifting should go through a witness record, not through
  inferred enumeration

## 6-4. release jitter / arrival offset
**Status: In progress**

実装済みの核:

- `within_jitter` と bool reflection
- jittered periodic generation predicate
- witness-based finite-horizon jobset / enumeration
- shared witness-based finite-optimality lift plus EDF / LLF / partitioned
  wrappers
- delayed actual release を含む example

重要点:

- release jitter は analysis 層に直接押し込まず、
  まず task-generation semantics として定義する
- arrival offset と jitter は分離する
- `generated_by_jittered_periodic_task -> generated_by_sporadic_task` は成り立つ
- ただし `sporadic_job_model_on` に必要な
  `sporadic_separation_on` は jitter bound だけでは一般には導けない
- そのため model-level bridge では separation を追加仮定として扱う

## 6-5. periodic / sporadic schedulability analysis hooks
**Status: RBF layer complete**

Done:

- `Analysis/Common/WorkloadAggregation.v`:
  - `total_job_cost`, `total_job_cost_le_length_mul`
  - `nat_mul_lt_ceil_div`: `k * p < H → 1 ≤ p → k < ⌈H/p⌉`
  - `ceil_div_mono`: monotonicity of ceiling division
- `PeriodicFiniteHorizon.v`:
  - `periodic_jobset_upto_implies_index_lt_tight`: `k < ⌈H/period⌉` tight bound
- `SporadicFiniteHorizon.v`:
  - `sporadic_jobset_upto_implies_index_lt_tight`: same tight bound for sporadic
- `Analysis/Uniprocessor/RequestBound.v`:
  - `periodic_rbf`, `sporadic_rbf_bound` (definitionally equal)
  - `sporadic_rbf_bound_eq_periodic_rbf`
  - `periodic_rbf_zero`: `rbf tasks τ 0 = 0`
  - `periodic_rbf_count_monotone`, `periodic_rbf_monotone`, `sporadic_rbf_bound_monotone`
  - `periodic_rbf_count_le_H`: `⌈H/p⌉ ≤ H`
  - `periodic_rbf_le_coarse_bound`: `rbf ≤ H × wcet`
- `PeriodicWorkload.v`:
  - `periodic_jobs_of_task_upto_count`: `⌈H/period⌉` (replaced coarse `H`)
  - `periodic_workload_upto_eq_rbf`
  - `periodic_workload_le_rbf`
- `SporadicWorkload.v`:
  - `sporadic_jobs_of_task_upto_bound`: `⌈H/period⌉`
  - `sporadic_workload_upto_bound_eq_rbf`
  - `sporadic_workload_le_rbf`
- `JitteredPeriodicWorkload.v`:
  - tighter workload bound via sporadic bridge
- `Examples/RequestBoundExamples.v`:
  - concrete RBF computations (period=5, wcet=2)
  - monotonicity and coarse-bound comparisons
  - `workload_le_rbf_ex`: periodic workload bridge in action
  - `jittered_le_sporadic_rbf`: jitter → sporadic bound

完了:

- demand bound function (DBF): `periodic_dbf`, `sporadic_dbf_bound`,
  `jittered_periodic_dbf_bound` defined and verified
- `periodic_dbf_le_periodic_rbf`: DBF ≤ RBF (requires `0 < rel_deadline`)
- `periodic_demand_le_dbf` / `sporadic_demand_le_dbf` /
  `jittered_periodic_demand_le_dbf`: job-level demand bounds
- `Examples/DemandBoundExamples.v`: concrete DBF examples

予定:

- utilization-related helper lemmas
- Liu & Layland 型の定理に接続する前段補題

注意:

- ここは「generation semantics」と「analysis theorem」を分けて管理する
- finite-horizon witness pipeline と workload analysis hook layer も分ける

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
**Status: Service/completion/remaining-cost/laxity bridge implemented**

残作業:

- global / clustered analysis 向けのより強い再利用補題層
- fairness / interference 向けの interval-level migration-aware 補題

---

# Lv.8: Global / clustered scheduling
**Status: Stable downstream entry layer being finalized**

## 8-1. global scheduling
**Status: In progress at the public-API stabilization stage**

証明済みとして扱うもの:

- `TopMSchedulerBridge.v` の generic bridge:
  - `top_m_algorithm_valid`
  - `top_m_algorithm_idle_outside_range`
  - `top_m_algorithm_no_duplication`
  - subset-aware theorem layer
- `TopMAdmissibilityBridge.v` generic bridge
- `GlobalEntryPoints.v` が stable downstream import を提供する
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
  - non-running admissible job から running jobs の laxity 上界を引く wrapper
  - non-running eligible job から machine-full を引く LLF 固有 wrapper
- `Multicore/Common/TopMMetricFacts.v`:
  - 非選出 eligible candidate があるなら top-`m` result は full
  - 非選出 eligible candidate の metric は全 chosen job 以上
- `Examples/GlobalExamples.v` が canonical example inventory を提供する
- curated examples は次を 1 箇所から辿れる
  - admissibility-aware running example
  - global LLF の dynamic-metric theorem client
  - migration preserves global service
  - global service equals the sum of per-CPU service
  - duplicate schedules are rejected by `no_duplication`

残作業:

- global policy results を EDF 以外へ一般化できるところまで切り出す
- richer affinity instantiation examples
- analysis / fairness hooks

注:

- `running -> admissible_somewhere` は現実装では無条件ではなく、`valid_schedule` 前提つきで使う

## 8-1a. multicore global analysis packaging
**Status: Done for the stable downstream boundary**

証明済みとして扱う public downstream inventory:

- `Analysis/Multicore/GlobalAnalysisEntryPoints.v` が stable downstream import
  を提供する
- `ProcessorSupply.v`:
  - `total_cpu_service_between_eq_capacity_if_all_cpus_busy`
  - `total_cpu_service_between_le_capacity`
- `Interference.v`:
  - `total_service_between_list_covers_total_cpu_supply`
- global EDF / LLF analysis-facing interval wrappers:
  - `global_edf_not_running_admissible_job_interval_implies_full_supply`
  - `global_edf_not_running_eligible_job_interval_implies_full_supply`
  - `global_llf_not_running_admissible_job_interval_implies_full_supply`
  - `global_llf_not_running_eligible_job_interval_implies_full_supply`

internal/helper inventory として扱うもの:

- `ProcessorSupply.v` の step/split/single-slot 補題
- `Interference.v` の `covered_cpu_count` と list-aggregation の補助補題群
- helper facts that only normalize list coverage or interval decomposition

残作業:

- coverage-based interference templates を full-supply consequence から
  workload-absorption statementsへ拡張する

追加済み public inventory:

- `Analysis/Multicore/GlobalWorkloadAbsorption.v`
- `total_service_between_list_le_total_job_cost`
- `covering_list_full_supply_implies_total_service_eq_capacity`
- strict workload-gap wrappers:
  - `global_edf_not_running_admissible_job_interval_implies_workload_gap`
  - `global_edf_not_running_eligible_job_interval_implies_workload_gap`
  - `global_llf_not_running_admissible_job_interval_implies_workload_gap`
  - `global_llf_not_running_eligible_job_interval_implies_workload_gap`

追加済み fairness client inventory:

- `Analysis/Multicore/GlobalFairness.v`
- contradiction wrappers:
  - `global_edf_not_running_admissible_job_interval_contradicts_workload_upper_bound`
  - `global_edf_not_running_eligible_job_interval_contradicts_workload_upper_bound`
  - `global_llf_not_running_admissible_job_interval_contradicts_workload_upper_bound`
  - `global_llf_not_running_eligible_job_interval_contradicts_workload_upper_bound`
- first must-run client theorems:
  - `global_edf_persistently_admissible_job_must_run_in_interval`
  - `global_edf_persistently_eligible_job_must_run_in_interval`
  - `global_llf_persistently_admissible_job_must_run_in_interval`
  - `global_llf_persistently_eligible_job_must_run_in_interval`

残作業の更新:

- policy-specific wrapper から top-`m` policy-generic analysis hook へ持ち上げる
  範囲を見極める
- bounded waiting / bounded tardiness を task-model-specific bridge に接続する
  ための client 定理粒度を整理する

## 8-2. clustered scheduling
**Status: Not started**

候補:

- cluster-local global scheduling
- cluster confinement
- partitioned と global の中間モデル

## 8-3. global dynamic-metric policies
**Status: LLF theorem inventory strengthened; analysis layer still planned**

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
**Status: In progress at the execution-first projection-discipline level**

## 10-1. machine / scheduler state
**Status: In progress**

実装済みとして扱うもの:

- `OpState`
- per-CPU current
- runnable-job list view
- pending reschedule requests
- minimal Awkernel-facing state wrapper

予定:

- per-CPU runqueue / global runqueue
- richer wakeup / block / completion invariants
- migration
- reschedule IPI
- timer / quantum / preemption

## 10-2. trace semantics
**Status: In progress**

実装済みとして扱うもの:

- `OpTrace`
- `OpEvent`
- `op_step` の最小骨格
- abstract schedule への projection
- `op_struct_inv`
- `trace_stepwise`
- `execution`
- execution-first projection soundness bridge

予定:

- machine trace
- trace-level event labels
- structural invariant を richer operational state へ拡張する
- execution-first bridge に delay/refinement obligation を積む

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
**Status: Partially done at the abstract single-CPU bridge level, with an operational projection bridge skeleton now available**

## 12-1. abstract policy -> executable single-CPU scheduler
**Status: Done**

これは現在の single-CPU algorithm/scheduler bridge でほぼ達成済みとみなす。

## 12-2. executable scheduler -> operational scheduler
**Status: Planned, with projection skeleton done**

前段として実装済み:

- operational state から abstract schedule を読む interface
- Awkernel-facing projection wrapper

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

## 13-0. analysis foundations
**Status: In progress**

Done:

- policy-independent busy interval definitions
- uniprocessor busy interval prefix / suffix lemmas
- no-idle-slot characterization for busy intervals
- maximal busy interval boundary decomposition
- interval processor-supply aggregation on top of schedule semantics
- periodic / sporadic / jittered-periodic finite-horizon workload helper lemmas
- periodic / sporadic / jittered-periodic per-task DBF helper lemmas
- aggregate task-set DBF definitions and monotonicity / append / NoDup-stability lemmas
- explicit-demand to aggregate-DBF bridge lemmas for periodic / sporadic / jittered-periodic job lists
- busy-interval to processor-demand contradiction hook for uniprocessor supply
- periodic window-DBF definitions and explicit-window-demand bridge lemmas
- EDF-facing busy-window overload contradiction helpers
- periodic window-DBF example layer and bridge-theorem examples
- busy-window search-space reduction hooks (`BusyWindowSearch.v`:
  `busy_window_candidate`, `busy_window_witness`, overload/deadline lemmas)
- finite-horizon busy-prefix witness layer in `BusyWindowSearch.v`
  (`busy_prefix_candidate`, `busy_prefix_witness`) plus bridge lemmas from the
  older maximal witness
- response-time search-space reduction hooks (`ResponseTimeSearch.v`:
  `response_time_candidate`, `response_time_search_witness`)
- finite-horizon response-time prefix witness in `ResponseTimeSearch.v`
  (`response_time_search_prefix_witness`)
- EDF-specific processor-demand theorem interfaces
  `periodic_window_dbf_implies_no_deadline_miss_under_edf` and
  `periodic_window_dbf_implies_edf_feasible_on_finite_horizon`
  in `EDFProcessorDemand.v`
  (both are now proven at stronger interfaces requiring an explicit EDF
  schedule witness; the no-miss theorem additionally requires a busy-window
  witness and a no-carry-in bridge)
- busy-prefix variants in `EDFProcessorDemand.v`, including
  `periodic_window_dbf_implies_no_deadline_miss_under_edf_if_covering_busy_prefix_and_no_carry_in`
  and `periodic_window_dbf_implies_edf_feasible_on_finite_horizon_with_busy_prefix`
- packaged periodic EDF busy-prefix bridge interface in `EDFProcessorDemand.v`
  via `periodic_edf_busy_prefix_bridge`, so generated-schedule and
  finite-horizon wrappers can share one explicit bridge premise
- `PeriodicEDFBridge.v` window-DBF bridge theorems close without `feasible_on` hypothesis
- `PeriodicEDFBridge.v` exposes bridge-first public busy-prefix wrappers for
  no-miss / feasible-schedule / schedulable-by-on
- `PeriodicEDFAnalysisEntryPoints.v` packages the stable downstream import for
  the current periodic EDF idealized-analysis inventory
- `PeriodicLLFAnalysisEntryPoints.v` packages the stable downstream import for
  periodic LLF analysis wrappers layered on top of the EDF feasibility bridge
- `PeriodicEDFBridgeCompat.v` retains the older unpackaged busy-prefix forms
  only as compatibility wrappers
- `PeriodicProcessorDemandExamples.v` now includes both
  `periodic_example_edf_no_deadline_miss_by_window_dbf_auto_with_busy_prefix_bridge`
  and
  `periodic_example_edf_schedulable_by_window_dbf_auto_with_busy_prefix_bridge`
- `PeriodicProcessorDemandExamples.v` also includes the generated-schedule
  bridge example
  `periodic_example_edf_schedulable_by_window_dbf_generated_with_busy_prefix_bridge`
- `PeriodicLLFAnalysisBridge.v` now exposes bridge-first LLF schedulable-by-on
  wrappers from both window DBF and zero-offset classical DBF assumptions
- `PeriodicProcessorDemandExamples.v` also includes LLF clients for the
  packaged bridge-first entry points:
  `periodic_example_llf_schedulable_by_window_dbf_generated_with_busy_prefix_bridge`
  and
  `periodic_example_llf_schedulable_by_classical_dbf_generated_with_busy_prefix_bridge`
- `PeriodicProcessorDemandExamples.v` is the stable client of the packaged
  bridge-first EDF/LLF entry points
- `PeriodicProcessorDemandCompatExamples.v` isolates the older busy-window /
  unpackaged busy-prefix example entry points
- `PeriodicProcessorDemandCompatExamples.v` remains the legacy-only client for
  compatibility wrappers

Remaining:
- busy-interval existence lemma: constructive extraction of maximal busy interval
  from any busy time point in a discrete schedule
- keep the bridge-first classical EDF corollary as the canonical public API;
  do not treat generated EDF alone as sufficient to derive `no_carry_in`
- split any future `periodic_edf_busy_prefix_bridge` supply story into a
  separate task with explicit backlog-exclusion / prefix-choice assumptions
- utilization / dbf hooks above the aggregate layer
- rbf / sbf style interfaces
- broader policy-specific analysis wrappers beyond the current EDF/LLF layer

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
Operational execution slice の上で delay-aware obligation を導入する。

## Priority 2
明示的な delay source を `Operational` 層に導入する。

## Priority 3
`Lv.12 Refinement` の executable scheduler -> operational scheduler bridge を始める。

## Priority 4
sporadic / jittered-periodic 側へ stable analysis inventory 形式を広げる。

## Priority 5
`Lv.5 Partitioned` と `Lv.6 Task-generation` の inventory を必要な範囲で整理し直す。

---

# One-line summary

単一CPUの generic optimality core と periodic EDF idealized-analysis の
stable entry-point はすでに主要部分が完成している。
直近の主戦場は、

- partitioned の theorem-layer completion
- periodic/sporadic/release-jitter generation strengthening
- multicore-common semantics
- multicore interval supply / interference foundations
- OS / delay / refinement
- idealized / delay-aware analysis

である。

直近の multicore 側では、

- top-`m` bridge で non-running eligible/admissible job から machine-full を引く層
- `total_cpu_service_between = m * (t2 - t1)` を与える interval full-supply 層
- global EDF / LLF の thin analysis hook

を stable public inventory として揃えたうえで、より豊かな interference template に進む。
