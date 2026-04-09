> Historical note
>
> This roadmap captures earlier refactoring phases. Current filenames are
> `FeasibleExamples.v` and `SchedulableExamples.v`, and the scheduler API is
> relation-based (`scheduler_rel`) rather than `run_scheduler`-based.

はい。壊しにくさを優先して、**小さな段階に分けた具体的なリファクタリング計画**にします。
主眼は次の 3 点です。

1. **意味論と interface の境界を明確にする**
2. **`Partitioned.v` の local / global のずれを解消する**
3. **今後 RR や global scheduler を入れやすい形にする**

---

# 全体方針

一度に全部直さず、**5 フェーズ + 各フェーズごとの compile 確認**で進めます。
特に `Partitioned.v` は意味が少し変わるので、**単独フェーズ**に分けます。

推奨順はこれです。

1. **責務分離のためのファイル整理**
2. **`Partitioned.v` の設計修正**
3. **constructive / classical の分離**
4. **EDF / FIFO / example の整理**
5. **`_on` 系を中心にした理論への寄せ**

---

# フェーズ 0: ベースライン固定

## 目的

今の状態を壊したかどうか判定できるようにする。

## 作業

* 現在のファイルをそのまま compile できることを確認
* compile 順を固定
* リファクタリング前の public theorem 名をメモする

## compile 順の目安

```text
Base.v
Schedule.v
UniSchedulerInterface.v
UniSchedulerLemmas.v
FIFO.v
EDF.v
Partitioned.v
PeriodicTasks.v
example_feasible.v
example_schedulable.v
```

## 完了条件

* 全ファイルが compile
* 既存 theorem 名を壊していないベースラインがある

---

# フェーズ 1: 意味論と algorithm interface を分離する

## 目的

`Schedule.v` に集まりすぎている責務を分離する。
ここでは**意味は変えず、構造だけ整理**します。

## 新しい責務分割

### `Base.v`

そのまま維持

* `JobId`, `TaskId`, `CPU`, `Time`
* `Task`, `Job`
* `Schedule`
* `released`, `pre_release`
* `valid_jobs`
* `valid_job_of_task`

### 新設: `ScheduleModel.v`

`Schedule.v` から次を移す

* `runs_on`
* `cpu_count`
* `service_job`
* `completed`
* `running`
* `eligible`
* `ready`
* `sequential_jobs`
* `valid_schedule`
* `missed_deadline`
* `feasible_schedule`
* `feasible`
* `feasible_schedule_on`
* `feasible_on`
* それらに関する補題群

### 新設: `SchedulerInterface.v`

`Schedule.v` から次を移す

* `Scheduler`
* `run_scheduler`
* `schedulable_by`
* `schedulable_by_on`
* それらの補題

### `Schedule.v`

互換レイヤにする

```coq
Require Export ScheduleModel.
Require Export SchedulerInterface.
```

## この段階での重要方針

* **既存 import をすぐに全部書き換えない**
* まず `Schedule.v` を re-export ファイルにして、差分を小さくする

## 影響ファイル

* `Schedule.v`
* 新規 `ScheduleModel.v`
* 新規 `SchedulerInterface.v`

## 完了条件

* 外部ファイルの import をほぼ触らずに compile
* `Schedule.v` が「実装の本体」ではなく「束ね役」になる

---

# フェーズ 2: `UniSchedulerInterface` を `Dispatch` 中心に整理する

## 目的

今の interface は実質的には scheduler というより **dispatch policy** なので、名前と責務を合わせる。

## 作業

### 新設: `DispatchInterface.v`

`UniSchedulerInterface.v` の本体をここに移す。
命名を次のように整理する。

* `GenericSchedulerDecisionSpec`
  → `GenericDispatchSpec`
* `choose_g`
  → `dispatch`

## 互換性維持

すぐ全面改名すると差分が大きいので、最初は互換 alias を置く。

例:

```coq
Notation GenericSchedulerDecisionSpec := GenericDispatchSpec.
Notation choose_g := dispatch.
```

あるいは、まず record 名は据え置きで file 名だけ先に分けてもよいです。
**安全重視なら file 分離 → 名前変更の順**がよいです。

## `UniSchedulerInterface.v`

互換レイヤにする

```coq
Require Export DispatchInterface.
```

## 影響ファイル

* `UniSchedulerInterface.v`
* 新規 `DispatchInterface.v`
* `FIFO.v`
* `EDF.v`
* `Partitioned.v`
* `UniSchedulerLemmas.v`

## 完了条件

* interface の意味が「algorithm 全体」ではなく「その時点の選択規則」に揃う
* 古い名前でも一旦 compile する

---

# フェーズ 3: `Partitioned.v` を local-view ベースに作り直す

ここが一番重要です。

## 現状の問題

今の `partitioned_schedule` は

```coq
sched t c =
  spec.(choose_g) jobs m sched t (candidates_for c jobs sched t xs)
```

となっていて、**single-CPU policy のはずなのに全体 schedule と全 CPU 数 `m` を見ています。**

一方で定理では

```coq
cpu_schedule sched c
```

という **1 CPU view** を使っています。

つまり、

* 定義は global-aware
* 証明は local-view

というねじれがあります。

---

## 修正方針

### 3-1. `candidates_for` を簡約する

今の未使用引数を削除する。

変更前:

```coq
Definition candidates_for (c : CPU) (jobs : JobId -> Job) (sched : Schedule)
    (t : Time) (xs : list JobId) : list JobId := ...
```

変更後:

```coq
Definition candidates_for (c : CPU) (xs : list JobId) : list JobId := ...
```

---

### 3-2. `partitioned_schedule` を本当に local dispatch にする

変更後の形はこれです。

```coq
Definition partitioned_schedule (jobs : JobId -> Job) (sched : Schedule)
    (xs : list JobId) : Prop :=
  forall t c, c < m ->
    sched t c =
      dispatch spec jobs 1 (cpu_schedule sched c) t (candidates_for c xs).
```

ポイントは

* `m` ではなく **1**
* `sched` ではなく **`cpu_schedule sched c`**

です。

---

### 3-3. `respects_assignment` を仮定ではなく定理に下げる

今は

```coq
valid_partitioned_schedule := partitioned_schedule /\ respects_assignment
```

ですが、local dispatch 化すると `choose_g_in_candidates` から

* 選ばれた job は `candidates_for c xs` に入る
* したがって `assign j = c`

が言えるので、`respects_assignment` は**導出可能**になります。

つまり次を新定理にします。

```coq
Theorem partitioned_schedule_implies_respects_assignment : ...
```

そのうえで

* `assignment_respect` はこれの corollary にする
* `valid_partitioned_schedule` は不要なら削除
* 残すなら単なる alias にする

---

### 3-4. `local_to_global_validity` を組み替える

今は per-CPU `valid_schedule` を外から仮定していますが、
local dispatch 化すると `choose_g_ready` から local ready が直接得られます。

そのため次の流れで、**`partitioned_schedule` から global validity を直接出せる**ようになります。

1. `partitioned_schedule`
2. chosen job is ready in `cpu_schedule sched c`
3. `partitioned_schedule_implies_respects_assignment`
4. `service_decomposition`
5. local 非完了性から global 非完了性へ
6. global `eligible`
7. `valid_schedule jobs m sched`

つまり今の `local_to_global_validity` は、
より自然な形に置き換えられます。

候補:

```coq
Theorem partitioned_schedule_implies_valid_schedule : ...
```

---

### 3-5. `service_decomposition` はそのまま活かす

これは今の `Partitioned.v` の中でも良い部分です。
ただし依存関係を

* `respects_assignment`
* `cpu_schedule`

に明確に寄せるように整理します。

---

## このフェーズで変える theorem 構成

### 残す

* `cpu_schedule`
* `service_decomposition`
* `completed_iff_on_assigned_cpu`
* `missed_deadline_iff_on_assigned_cpu`
* `local_feasible_implies_global_feasible_schedule`

### 再構成する

* `assignment_respect`
* `local_to_global_validity`
* `local_valid_feasible_implies_global`
* `valid_partitioned_schedule`

## 完了条件

* `partitioned_schedule` が本当に single-CPU policy の合成になっている
* `respects_assignment` が仮定ではなく結果として出る
* validity lifting が自然になる

---

# フェーズ 4: constructive core と classical lemma を分離する

## 目的

`UniSchedulerLemmas.v` にだけ `Classical` が入っている状態を整理する。

## 現状

`choose_none_implies_each_candidate_unreleased_or_completed` のために
`Classical` を import しています。

## 作業

### `UniSchedulerLemmas.v`

constructive に証明できるものだけ残す

### 新設: `UniSchedulerLemmasClassical.v`

次を移す

* `choose_none_implies_each_candidate_unreleased_or_completed`

必要なら lemma 名も少し明示的にする

* `..._classical`

## 影響ファイル

* `UniSchedulerLemmas.v`
* 新規 `UniSchedulerLemmasClassical.v`

## 完了条件

* core 側が `Classical` に依存しない
* 古典論理依存がファイル境界で見える

---

# フェーズ 5: EDF / FIFO / example を整理する

## 目的

policy 本体と example / 補助 spec を切り分ける。

---

## 5-1. `EDF.v` の不要仮定を消す

次の補題の `NoDup candidates` は今使っていません。

* `choose_edf_complete`
* `choose_edf_optimal`

なので、一旦削除します。
将来 tie-breaking の一意性に使うなら、そのとき改めて別 lemma に入れる方が明確です。

---

## 5-2. `FIFO.v` の example を分離する

今の `FIFO.v` の `FIFOExample` section は悪くないですが、policy 定義と混ざっています。

分け方:

* `FIFO.v`
  定義 + 一般補題 + spec
* `FIFOExamples.v`
  具体例

EDF も同様に将来 example が増えるなら分離するとよいです。

---

## 5-3. policy file の責務を統一する

各 policy file の構成を揃えると読みやすくなります。

推奨テンプレート:

1. dispatch 定義
2. generic spec の証明
3. policy-specific invariant
4. policy-specific corollary
5. examples は別 file

---

## 完了条件

* `FIFO.v` / `EDF.v` が「一般定義の置き場」になる
* 例が増えても本体が見通しよく保てる

---

# フェーズ 6: `_on` 系を中心にした理論へ寄せる

## 目的

今後 finite job set / periodic task / 実用例に進みやすくする。

## 方針

total-function 版を消す必要はありません。
ただし**理論の中心を `_on` 版に寄せる**のがよいです。

### 具体的には

* `example_schedulable.v` はすでに `_on` 中心でよい
* `PeriodicTasks.v` でも `periodic_job_model_on` を前面に出す
* comments も

  * total 版 = 簡易モデル
  * `_on` 版 = 今後の主流
    と整理する

## このフェーズで追加するとよい補題

* total 版から `_on` 版への単調な橋渡し
* `J` に対する feasibility / schedulability の単調性
* `periodic_job_model_on` と `feasible_on` の組み合わせ用補題

## 完了条件

* 例や今後の理論が total-function の不自然さに引きずられない
* finite / subset reasoning に自然に進める

---

# 実際の実施順

一番安全なのはこの順です。

## Commit 1

* `ScheduleModel.v`, `SchedulerInterface.v` を新設
* `Schedule.v` を re-export 化

## Commit 2

* `DispatchInterface.v` を新設
* `UniSchedulerInterface.v` を re-export 化
* 名前変更は alias で互換維持

## Commit 3

* `Partitioned.v` の `candidates_for` 簡約
* `partitioned_schedule` を local-view に変更
* `partitioned_schedule_implies_respects_assignment`
* `partitioned_schedule_implies_valid_schedule` を追加
* 古い theorem を組み替え

## Commit 4

* `UniSchedulerLemmasClassical.v` を新設
* `Classical` 依存 lemma を移動

## Commit 5

* `EDF.v` の不要仮定削除
* `FIFOExamples.v` などに example 分離
* `_on` 中心の comments 整理

---

# この計画で得られる状態

最終的にこうなります。

* `Base.v`
  基本データ型と job/task の局所整合性

* `ScheduleModel.v`
  スケジュール意味論

* `SchedulerInterface.v`
  abstract scheduler と schedulability

* `DispatchInterface.v`
  単一 CPU dispatch policy interface

* `UniSchedulerLemmas.v`
  constructive な一般補題

* `UniSchedulerLemmasClassical.v`
  classical に依存する補題

* `FIFO.v`, `EDF.v`
  policy の定義と一般補題

* `Partitioned.v`
  local dispatch の合成理論

* `PeriodicTasks.v`
  periodic generation model
