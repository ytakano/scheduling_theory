再設計の中心は

**`Dispatch` は「1 step の選択規則」**
**`Bridge` は「それを Scheduler relation に埋め込む層」**
**`Partitioned` は「single-CPU dispatch を CPU ごとに持ち上げる層」**

と責務をきれいに分けることです。
これは、ロードマップ上でも **partitioned は per-CPU scheduler の持ち上げとして扱う** のが自然で、最初の multicore 到達点として適切です。

---

## まず結論

今回の再設計案では、次の3点を固定します。

1. **`DispatchInterface` は `ready` ではなく `eligible` を使う**
   今の `ScheduleModel` では、実行中 job は `eligible` だが `ready` ではありません。したがって dispatch の返り値仕様を `ready` にすると、bridge で `sched t c = Some j` と結んだ瞬間に矛盾します。
   ここは interface 側を現行意味論に合わせるべきです。

2. **`DispatchSchedulerBridge` が candidate source の責務を持つ**
   「どの job が候補に入るか」は policy ではなく bridge 側の責務に寄せます。
   dispatch は「与えられた候補から 1 つ選ぶ」だけにします。

3. **`Partitioned` は外から任意の `xs` を受け取るのをやめる**
   `xs` が不完全でも relation が成立してしまう穴を塞ぎます。
   代わりに、対象 job 集合 `J` とその有限列挙 `enumJ` を受け取り、CPU ごとの候補は `assign` で自動生成します。

---

# 1. `DispatchInterface.v` の再設計

現状の `DispatchInterface.v` では、

* `dispatch_ready`
* `dispatch_some_if_ready`
* `dispatch_none_if_no_ready`

がすべて `ready` ベースです。

しかし `ScheduleModel.v` では、`ready = eligible /\ ~running`、`valid_schedule` は `eligible` ベースです。
なので interface は次の形に揃えるのが自然です。

## 新しい役割

`DispatchInterface` は、

* 候補集合 `candidates`
* 現在までの schedule 情報
* 時刻 `t`

を見て、**この時刻に実行してよい job を 1 つ返す**
という最小仕様だけを持つ。

## 新しい record の核

```coq
Record GenericDispatchSpec : Type := mkGenericDispatchSpec {
  dispatch :
    (JobId -> Job) -> nat -> Schedule -> Time -> list JobId -> option JobId;

  dispatch_eligible :
    forall jobs m sched t candidates j,
      dispatch jobs m sched t candidates = Some j ->
      eligible jobs m sched j t;

  dispatch_in_candidates :
    forall jobs m sched t candidates j,
      dispatch jobs m sched t candidates = Some j ->
      In j candidates;

  dispatch_some_if_eligible_candidate :
    forall jobs m sched t candidates,
      (exists j, In j candidates /\ eligible jobs m sched j t) ->
      exists j', dispatch jobs m sched t candidates = Some j';

  dispatch_none_if_no_eligible_candidate :
    forall jobs m sched t candidates,
      (forall j, In j candidates -> ~ eligible jobs m sched j t) ->
      dispatch jobs m sched t candidates = None
}.
```

## 追加で入れたいが、必須ではない性質

これは bridge の循環依存を防ぐためにかなり有用です。

```coq
dispatch_prefix_extensional :
  forall jobs m s1 s2 t candidates,
    (forall t' c, t' < t -> s1 t' c = s2 t' c) ->
    dispatch jobs m s1 t candidates =
    dispatch jobs m s2 t candidates
```

意味は、**dispatch は時刻 `t` より前の履歴にしか依存しない**、です。
EDF/FIFO/RR のような policy なら本質的にこの性質を満たすはずです。

## このファイルに残すもの / 残さないもの

残すもの:

* `dispatch`
* 選択結果の健全性
* 候補集合に対する完全性 / 空性

残さないもの:

* 候補集合が ready set を覆うこと
* assignment
* per-CPU / partitioned の話
* classical ready queue 的性質

`ready` を使った補題は、必要なら `DispatchClassicalLemmas.v` 側へ逃がすのがよいです。

---

# 2. `DispatchSchedulerBridge.v` の再設計

このファイルの仕事は、**dispatch spec を Scheduler relation に埋め込むこと**だけに絞ります。

現状の問題は、`single_cpu_dispatch_schedule` が

```coq
sched t 0 = dispatch jobs m sched t ...
```

という形で、**生成される schedule 自身をその時刻の dispatch に渡している**ことです。
`ready` ベースだったときは破綻し、`eligible` ベースにしても依存方向はやや不透明です。

なので bridge では、**candidate source の契約**を明示します。

## このファイルに入れるべき新概念

### 1. candidate source の抽象

```coq
Definition CandidateSource :=
  (JobId -> Job) -> nat -> Schedule -> Time -> list JobId.
```

### 2. candidate source の契約

少なくとも次の3つです。

```coq
Record CandidateSourceSpec
    (J : JobId -> Prop)
    (candidates_of : CandidateSource) : Prop := {
  candidates_sound :
    forall jobs m sched t j,
      In j (candidates_of jobs m sched t) -> J j;

  candidates_complete :
    forall jobs m sched t j,
      J j ->
      eligible jobs m sched j t ->
      In j (candidates_of jobs m sched t);

  candidates_prefix_extensional :
    forall jobs m s1 s2 t,
      (forall t' c, t' < t -> s1 t' c = s2 t' c) ->
      candidates_of jobs m s1 t = candidates_of jobs m s2 t
}.
```

ここで重要なのは `J` を入れることです。
これで bridge は `schedulable_by_on J` に自然につながります。

## single-CPU bridge の新API

`SchedulerInterface.v` はそのままでも、bridge 側で `schedulable_by_on` に向いた constructor を出せます。

```coq
Definition single_cpu_dispatch_scheduler_on
    (J : JobId -> Prop)
    (spec : GenericDispatchSpec)
    (candidates_of : CandidateSource)
    : Scheduler := ...
```

relation の中身は今と似ていますが、意味づけが変わります。

* CPU 0 は dispatch に従う
* 他 CPU は idle
* 候補集合の sound/complete は `CandidateSourceSpec` が持つ

## この bridge で証明すべき基本定理

1. `scheduler_rel -> valid_schedule jobs 1 sched`
2. `J` 上で eligible job が候補に入る
3. `dispatch_none_if_no_eligible_candidate` から idle 条件が導ける
4. 可能なら `J` 上の weak work-conserving

これは、あなたの整理している「抽象 scheduler の健全性」や「partitioned への持ち上げ」の前段にちょうど対応します。

---

# 3. `Partitioned.v` の再設計

ここは、**single-CPU dispatch を CPU ごとに複製して静的 assignment で合成する層**に徹します。
ロードマップの「partitioned scheduling は各 CPU が独立な単一CPU scheduler を動かす」という方針に合わせる形です。

現状の最大の問題は、

```coq
partitioned_schedule jobs sched xs :=
  forall t c, ...
    spec.(dispatch) jobs 1 (cpu_schedule sched c) t (candidates_for c xs)
```

で、`xs` が任意の list なので、**対象 job 集合を本当に覆っているかが relation に入っていない**ことです。

## ここで変えるべきこと

### 1. `xs` を主役から降ろす

外部APIは `J : JobId -> Prop` を主役にします。
ただし dispatch は list を必要とするので、有限列挙 `enumJ : list JobId` を witness として持ちます。

```coq
Variable J : JobId -> Prop.
Variable enumJ : list JobId.

Hypothesis enumJ_complete :
  forall j, J j -> In j enumJ.
```

必要なら `NoDup enumJ` も入れます。

### 2. local candidate を自動生成する

```coq
Definition local_candidates (c : CPU) : list JobId :=
  filter (fun j => Nat.eqb (assign j) c) enumJ.
```

これで `Partitioned` は外から candidate list をもらわずに済みます。

### 3. relation を `..._on J` に寄せる

```coq
Definition partitioned_schedule_on
    (jobs : JobId -> Job) (sched : Schedule) : Prop :=
  forall t c, c < m ->
    sched t c =
      spec.(dispatch) jobs 1 (cpu_schedule sched c) t (local_candidates c).
```

この relation に加えて、列挙完全性から

* `J j /\ assign j = c /\ eligible ...`
  なら `j ∈ local_candidates c`

が出せるようにします。

## `Partitioned.v` に残すべき定理

残すべき中核は今のままでよいです。

1. `partitioned_schedule_on -> respects_assignment`
2. `partitioned_schedule_on -> sequential_jobs`
3. `service_decomposition`
4. `completed_iff_on_assigned_cpu`
5. `partitioned_schedule_on -> valid_schedule`
6. `per-CPU feasible -> global feasible_on J`

特に 6 は、今後の main theorem を `schedulable_by_on` に寄せると非常に使いやすくなります。
partitioned は「各 CPU の単一CPU理論の conjunction」で進めるのが自然なので、この方向が一番無理がありません。

---

# 4. 3ファイルの依存方向

この形にすると、依存はこうなります。

```text
DispatchInterface
    ↓
DispatchSchedulerBridge
    ↓
Partitioned
```

* `DispatchInterface` は最下層
* `DispatchSchedulerBridge` は `Scheduler` への埋め込み
* `Partitioned` は bridge を使う multicore lifting

逆方向の依存は作らない方がよいです。

---

# 5. 具体的な変更順序

## Step 1

`DispatchInterface.v` の `ready` を `eligible` に置き換える。
まずは名前も素直に変えます。

* `dispatch_ready` → `dispatch_eligible`
* `dispatch_some_if_ready` → `dispatch_some_if_eligible_candidate`
* `dispatch_none_if_no_ready` → `dispatch_none_if_no_eligible_candidate`

この時点で、いまの self-contradiction は消えます。

## Step 2

`DispatchSchedulerBridge.v` に `CandidateSourceSpec` を導入する。
`candidates_of` を「ただの関数」から「契約付きの source」に昇格させます。

## Step 3

`single_cpu_dispatch_schedule` を `single_cpu_dispatch_scheduler_on` に改名する。
主役を `J` ベースへ寄せます。

## Step 4

`Partitioned.v` から外部 `xs` を消し、`J + enumJ + assign` に置き換える。
`local_candidates` は `assign` で内部生成するようにします。

## Step 5

`local_feasible_implies_global_feasible_schedule` を
`...feasible_schedule_on J...` ベースに寄せる。
全域量化版よりこちらが今後の証明に自然です。

---

# 6. 変更後の各ファイルの責務

## `DispatchInterface.v`

「候補から 1 つ選ぶ」最小仕様

* dispatch
* dispatch result の健全性
* 候補集合に対する完全性 / 空性

## `DispatchSchedulerBridge.v`

「dispatch を Scheduler relation に持ち上げる」

* candidate source の契約
* single-CPU scheduler 化
* validity の基本定理

## `Partitioned.v`

「single-CPU dispatch を assignment で multicore に持ち上げる」

* `cpu_schedule`
* `local_candidates`
* `respects_assignment`
* `service_decomposition`
* global validity / feasibility lifting

---

# 7. この再設計の利点

1. **現行の `eligible` / `ready` 分離と整合する**
2. **dispatch と scheduler abstraction の責務が分かれる**
3. **partitioned が単一CPU理論の再利用層として明確になる**
4. **`schedulable_by_on` と自然につながる**
5. **将来の global scheduler 導入時にも、`DispatchInterface` を壊さずに済む**

特に 5 は大きいです。
global 側では top-`m` selection という別抽象が必要になるので、いまの段階で `Dispatch` を single-choice policy にきれいに閉じておくのは得です。

---

# 8. 一番おすすめの最終形

名前まで含めると、私は次をおすすめします。

* `DispatchInterface.v`

  * `GenericDispatchSpec`

* `DispatchSchedulerBridge.v`

  * `CandidateSource`
  * `CandidateSourceSpec`
  * `single_cpu_dispatch_scheduler_on`
  * `single_cpu_dispatch_valid_on`

* `Partitioned.v`

  * `partitioned_schedule_on`
  * `partitioned_dispatch_scheduler_on`
  * `partitioned_schedule_implies_valid_schedule`
  * `local_feasible_on_implies_global_feasible_on`

