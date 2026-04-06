# Proof Plan: PeriodicTasks.v — 周期生成規則の骨格

## Goal

`PeriodicTasks.v` に周期タスクの job 生成規則を定義し、`Base.v` の `valid_job_of_task` との整合性を示す 4 つの基本補題を証明する。

## Definitions (in order)

1. `expected_release tasks offset τ k` = `offset τ + k * task_period (tasks τ)`
2. `expected_abs_deadline tasks offset τ k` = `expected_release ... + task_relative_deadline (tasks τ)`
3. `generated_by_periodic_task tasks offset jobs j` — release/deadline/cost が生成規則に従う
4. `periodic_job_model tasks offset jobs` — 全 job が生成規則に従う（total-function 版）
5. `periodic_job_model_on J tasks offset jobs` — job 集合 J に限定した版
6. `implicit_deadline_tasks tasks` — relative_deadline = period

## Proof Strategy

各補題はすべて定義を展開して等式/不等式を示すだけ。`lia` または `exact` で閉じられる見通し。

`generated_implies_valid_job_of_task` のみ少し注意:
- `valid_job_of_task` は `job_abs_deadline = job_release + relative_deadline` を要求
- `generated_by_periodic_task` が持つのは `job_abs_deadline = expected_abs_deadline ...`
- `expected_abs_deadline` を unfold し、`job_release = expected_release` (Hrel) を `<-` 方向で rewrite

## Proposed Lemmas

- [ ] `generated_job_release` : release が定義通り
- [ ] `generated_job_deadline` : deadline = release + relative_deadline
- [ ] `generated_job_cost_bounded` : cost ≤ task_cost
- [ ] `generated_implies_valid_job_of_task` : `valid_job_of_task` を含意

## Proof Order

1. `generated_job_release`
2. `generated_job_deadline`
3. `generated_job_cost_bounded`
4. `generated_implies_valid_job_of_task`
