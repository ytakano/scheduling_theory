# Periodic / Sporadic / Jittered-Periodic に対して、有限区間上の job 数・累積実行量・利用率補題を入れる

## 実装Plan

### 1. periodic の workload 基盤を入れる
**実装ファイル**
- `theories/TaskModels/Periodic/PeriodicWorkload.v` （新規）
- `theories/TaskModels/Periodic/PeriodicReleaseLemmas.v` （必要に応じて追記）
- `_CoqProject` （追記）

**やること**
- horizon `H` までに task `τ` から現れうる job 数の上界を定義する
- `periodic_jobset_upto` に属する job の index 上界を、既存の release/index 補題から導く
- 各 task の cumulative cost 上界を定義する
- utilization 形式に接続しやすい補題を用意する

**最低限ほしい定理の形**
```coq
Definition periodic_jobs_of_task_upto_count ...
Definition periodic_workload_upto ...

Lemma periodic_job_index_bound_upto :
  ...

Lemma periodic_jobs_of_task_upto_count_sound :
  ...

Lemma periodic_workload_upto_bound :
  ...
```

---

### 2. sporadic の workload 上界を入れる
**実装ファイル**
- `theories/TaskModels/Sporadic/SporadicWorkload.v` （新規）
- `theories/TaskModels/Sporadic/SporadicFiniteHorizon.v` （必要に応じて追記）
- `_CoqProject` （追記）

**やること**
- `sporadic_separation_on` を使って、有限 horizon 内の job 数上界を導く
- periodic より弱いが analysis に使える cumulative workload bound を作る
- witness API とは独立に、集合論的上界補題として置く

**最低限ほしい定理の形**
```coq
Definition sporadic_jobs_of_task_upto_bound ...
Definition sporadic_workload_upto_bound ...

Lemma sporadic_index_bound_from_separation :
  ...

Lemma sporadic_job_count_upto_le :
  ...

Lemma sporadic_workload_upto_le :
  ...
```

---

### 3. jittered-periodic を sporadic workload bound に橋渡しする
**実装ファイル**
- `theories/TaskModels/Jitter/JitteredPeriodicWorkload.v` （新規）
- `theories/TaskModels/Jitter/JitteredPeriodicSporadicBridge.v` （必要に応じて追記）
- `_CoqProject` （追記）

**やること**
- jittered-periodic 独自の count/workload を一から重く証明するのではなく、
  既存の `generated_by_jittered_periodic_task -> generated_by_sporadic_task`
  を使って sporadic bound に還元する
- separation 仮定が必要な箇所を明示する
- 「offset と jitter は task-generation 側で吸収し、analysis 側には bound だけ渡す」という構造を固定する

**最低限ほしい定理の形**
```coq
Lemma jittered_periodic_job_count_upto_le_sporadic_bound :
  ...

Lemma jittered_periodic_workload_upto_le_sporadic_bound :
  ...
```

---

### 4. 小さな example で API を固定する
**実装ファイル**
- `theories/Examples/PeriodicExamples.v` （追記）
- `theories/Examples/SporadicExamples.v` （追記）
- `theories/Examples/JitteredPeriodicExamples.v` （追記）

**やること**
- 既存 example に対して
  - job count bound
  - cumulative workload bound
  - utilization helper
  の使用例を1つずつ足す
- theorem 名と引数順をここで安定化する

---

### 5. 文書を最小更新する
**実装ファイル**
- `plan/roadmap.md`
- `plan/what_to_prove.md`

**やること**
- B-1 / B-2 / 6-5 / 13-0 の status を更新する
- 「finite-horizon witness pipeline」と「analysis hook layer」を分けて記述する

---

## TODOリスト

- [ ] `PeriodicWorkload.v` を追加する
- [ ] periodic の job count / workload 上界を証明する
- [ ] `SporadicWorkload.v` を追加する
- [ ] `sporadic_separation_on` から horizon 内 job count 上界を導く
- [ ] sporadic cumulative workload bound を証明する
- [ ] `JitteredPeriodicWorkload.v` を追加する
- [ ] jittered-periodic の workload bound を sporadic bridge 経由で証明する
- [ ] example に workload bound 使用例を足す
- [ ] `_CoqProject` を更新する
- [ ] `roadmap.md` / `what_to_prove.md` を進捗に合わせて更新する

