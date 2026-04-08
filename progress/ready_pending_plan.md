# Proof Plan: ready/pending 状態分離

## Goal

job の状態概念を明確に分離し、以下の述語を整備する:

- `pending j t` (Base.v) = pre-release: `t < job_release (jobs j)` [schedule 非依存]
- `running sched j t` (Schedule.v) = `exists c, sched t c = Some j`
- `runnable sched j t` (Schedule.v) = `released AND NOT completed` [旧 `pending`]
- `ready sched j t` (Schedule.v) = `runnable` [意味は変えない: 将来拡張の準備]

## 設計上の注意

`ready = runnable AND NOT running` とすると `valid_schedule` が矛盾する:
- `valid_schedule: sched t c = Some j → ready j t`
- `ready j t = runnable j t AND NOT running j t`
- `sched t c = Some j → running j t` (定義より)
- よって `valid_schedule` は `sched t c = Some j → NOT (sched t c = Some j)` を導く → 矛盾

このため今フェーズでは `ready = runnable` の意味を保持し:
- `running` と `runnable` を新規追加
- `pending` (pre-release) を Base.v に追加
- 旧 `Schedule.v::pending` → `runnable` に改名
- 旧 `ready = pending` → `ready = runnable` (同義だが名前が変わる)

## Proof Strategy

Step-by-step refactoring + new lemmas:

1. `Base.v`: `pending` (pre-release) 追加
2. `Schedule.v`: 定義再編 (running追加, pending→runnable改名, ready更新)
3. `Schedule.v`: 既存lemmaのpending→runnable置換
4. `Schedule.v`: 新規lemma追加
5. `UniSchedulerLemmas.v`: choose_some_implies_pending → choose_some_implies_runnable
6. `EDF.v`: pending参照をrunnable置換

## Proposed Lemmas

新規 lemma (Schedule.v に追加):

- [ ] `pending_not_runnable`: `pending j t → NOT runnable j t`
- [ ] `pending_not_ready`: `pending j t → NOT ready j t`
- [ ] `ready_implies_runnable`: `ready j t → runnable j t` [定義より自明]
- [ ] `completed_not_runnable`: `completed j t → NOT runnable j t`
- [ ] `runnable_after_release`: `runnable j t → job_release (jobs j) <= t`
- [ ] `ready_after_release`: `ready j t → job_release (jobs j) <= t`
- [ ] `scheduled_implies_running`: `sched t c = Some j → running sched j t`

既存 lemma のリネーム:
- [ ] `valid_running_implies_pending` → `valid_running_implies_runnable`

## Proof Order

1. Base.v: `pending` 追加
2. Schedule.v: `running`, `runnable`, `ready` 定義更新
3. Schedule.v: 既存lemma更新 (pending→runnable)
4. Schedule.v: 新規lemma (pending_not_runnable 等)
5. UniSchedulerLemmas.v: choose_some_implies_runnable
6. EDF.v: readyb + pending参照修正
7. 全コンパイル確認
