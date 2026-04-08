# Proof Plan: example_schedulable

## Goal

`example_feasible.v` として、Job・Schedule・feasible_schedule の具体例を Rocq で示す。
- **Example 1**: feasible_schedule な例（job 0 が締切を守る）
- **Example 2**: not feasible な例（どんなスケジュールでも job 0 が締切を守れない）

## 注意点: JobId の全域性

`feasible_schedule jobs m sched := forall j, ~missed_deadline jobs m sched j`
は**全 JobId** に対する命題。

教育目的では、個々のジョブについて締切を証明する方が直感的。
- Example 1: `~missed_deadline jobs_ex1 1 sched_ex1 0`（job 0 が締切を守る）
- Example 2: `forall sched, missed_deadline jobs_ex2 1 sched 0`（どんなスケジュールでも job 0 が締切を破る）

## 設定

### Example 1

```
Job:      release=0, cost=2, deadline=3
Schedule: CPU 0 で t=0,1 に job 0 を実行、t≥2 は None
```

### Example 2

```
Job:      release=0, cost=3, deadline=2
Schedule: 任意（1 CPU）
          deadline=2 までに最大 2 タイムスロット < cost=3
```

## Proposed Lemmas

- [ ] `cpu_count_le_m`: `forall m sched j t, cpu_count sched j t m <= m`
- [ ] `service_le_m_mul_t`: `forall m sched j t, service m sched j t <= m * t`
- [ ] `ex1_job0_completed`: `completed jobs_ex1 1 sched_ex1 0 3` (simpl で計算)
- [ ] `ex2_any_sched_misses`: `forall sched, missed_deadline jobs_ex2 1 sched 0`

## Proof Order

1. `cpu_count_le_m`
2. `service_le_m_mul_t` (uses `cpu_count_le_m`)
3. `ex1_job0_completed` (simpl/compute)
4. `ex2_any_sched_misses` (uses `service_le_m_mul_t`)
