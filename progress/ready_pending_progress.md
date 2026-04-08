# Proof Progress: ready/pending 状態分離

## Status Overview
- Overall: Complete
- Complete Steps: 7/7
- Unproven (`Admitted`): none
- Failed/Abandoned Items: none

## TODO
(すべて完了)

## Completed Steps

### Step 1: Base.v に `pending` (pre-release) を追加 ✓

```coq
Definition pending (jobs : JobId -> Job) (j : JobId) (t : Time) : Prop :=
  t < job_release (jobs j).
```

`released` の直後に追加。schedule 非依存 (sched, m 不要)。

---

### Step 2 & 3: Schedule.v 定義再編 + 既存 lemma 更新 ✓

追加した定義:
```coq
Definition running (sched : Schedule) (j : JobId) (t : Time) : Prop :=
  exists c : CPU, sched t c = Some j.

Definition runnable (jobs : JobId -> Job) (m : nat) (sched : Schedule)
    (j : JobId) (t : Time) : Prop :=
  released jobs j t /\ ~completed jobs m sched j t.

Definition ready (jobs : JobId -> Job) (m : nat) (sched : Schedule)
    (j : JobId) (t : Time) : Prop :=
  runnable jobs m sched j t.
```

旧 `pending` (Schedule.v) を削除し `runnable` に改名。

既存 lemma の更新:
- `unfold ..., pending` → `unfold ..., runnable` (全箇所)
- `valid_running_implies_pending` → `valid_running_implies_runnable` (改名)

---

### Step 4: Schedule.v 新規 lemma 追加 ✓

以下の lemma を追加 (Lv.0-4 セクション):

- `pending_not_runnable`: `pending j t → NOT runnable j t`
- `pending_not_ready`: `pending j t → NOT ready j t`
- `ready_implies_runnable`: `ready j t → runnable j t`
- `completed_not_runnable`: `completed j t → NOT runnable j t`
- `runnable_after_release`: `runnable j t → job_release (jobs j) <= t`
- `ready_after_release`: `ready j t → job_release (jobs j) <= t`
- `scheduled_implies_running`: `sched t c = Some j → running sched j t`

---

### Step 5: UniSchedulerLemmas.v 更新 ✓

- `choose_some_implies_pending` → `choose_some_implies_runnable` (改名)
- 本体の `unfold ready, pending` → `unfold ready, runnable`
- 呼び出し元 `apply choose_some_implies_pending` → `apply choose_some_implies_runnable`

---

### Step 6: EDF.v 更新 ✓

- `readyb_iff` の証明中 `unfold readyb, ready, pending, released, completed`
  → `unfold readyb, ready, runnable, released, completed`

---

### Step 7: 全コンパイル確認 ✓

```
rocq compile Base.v && rocq compile Schedule.v && 
rocq compile UniSchedulerInterface.v && rocq compile UniSchedulerLemmas.v && 
rocq compile EDF.v && rocq compile PeriodicTasks.v && rocq compile example_feasible.v
```

全て Exit: 0

## Design Decision

`ready = runnable AND NOT running` は **採用しなかった**。
理由: `valid_schedule: sched t c = Some j → ready j t` において
`running j t` が成立するので `ready = runnable AND NOT running` とすると矛盾する。
将来、dispatcher の仕様を `runnable` ベースに変更する際に改めて検討する。
