はい。
実装を踏まえると、**壊さずに前進するための最短ルート**は次です。

* まず `SchedulerValidity.v` で **「schedule が policy を満たす」** を一般化する
* 次に `DispatcherRefinement.v` で **「dispatcher が policy を実装する」** を一般化する
* その後で EDF/FIFO をこの層に載せる
* 最後に必要なら `Partitioned.v` をこの新層へ接続する

以下、**そのまま着手できる具体 plan**です。

---

# 全体方針

今回のポイントは、既存の

* `GenericDispatchSpec`
* `single_cpu_dispatch_schedule`
* `matches_choose_edf_at_with`

を壊さずに、

* `policy`
* `schedule validity`
* `dispatcher refinement`

を **別ファイルとして追加**することです。

つまり、今回は **既存 EDF 最適性証明を書き換えるのではなく、上に新しい抽象層を増やす** 方針がよいです。

特に重要なのは次の2点です。

1. **policy は candidate list ベースで定義する**

   * EDF だけでなく FIFO も扱うため
   * FIFO は順序依存なので `J` だけでは足りない

2. **EDF の tie は policy 側で吸収する**

   * `choose_edf` は deterministic chooser のままでよい
   * policy は「最小 deadline の job ならどれでもよい」とする

---

# まずやる変更

## 0. `_CoqProject` に新ファイルを追加

順序はこれがよいです。

```text
theories/SchedulerValidity.v
theories/DispatcherRefinement.v
```

挿入位置は

* `DispatchSchedulerBridge.v` の後
* `UniPolicies/EDF.v` の前

が自然です。

つまり概ねこうです。

```text
theories/DispatchSchedulerBridge.v
theories/SchedulerValidity.v
theories/DispatcherRefinement.v
theories/UniPolicies/EDF.v
theories/UniPolicies/FIFO.v
...
```

---

# Phase 1: `SchedulerValidity.v` を作る

## 目的

`DispatchSchedulerBridge.v` が提供している
「dispatcher から schedule を作る」
とは別に、

**ある schedule が局所的に policy を満たしている**

という概念を切り出します。

---

## 1-1. まず導入する定義

最初に、policy を candidate list ベースで定義します。

```coq
Definition DispatchPolicy :=
  (JobId -> Job) -> nat -> Schedule -> Time -> list JobId -> option JobId -> Prop.
```

これで

* EDF policy
* FIFO policy
* RR policy
* fixed-priority policy

を全部同じ型で置けます。

---

## 1-2. 「その時刻で policy を満たす」の定義

次に、schedule の実際の選択 `sched t 0` が
policy に許されているかを表す述語を入れます。

```coq
Definition respects_policy_at
    (policy : DispatchPolicy)
    (jobs : JobId -> Job)
    (sched : Schedule)
    (t : Time)
    (candidates : list JobId) : Prop :=
  policy jobs 1 sched t candidates (sched t 0).

Definition respects_policy_at_with
    (policy : DispatchPolicy)
    (jobs : JobId -> Job)
    (candidates_of : CandidateSource)
    (sched : Schedule)
    (t : Time) : Prop :=
  policy jobs 1 sched t (candidates_of jobs 1 sched t) (sched t 0).

Definition respects_policy_before
    (policy : DispatchPolicy)
    (jobs : JobId -> Job)
    (candidates_of : CandidateSource)
    (sched : Schedule)
    (H : Time) : Prop :=
  forall t, t < H ->
    respects_policy_at_with policy jobs candidates_of sched t.
```

この3つがこのファイルの中心です。

---

## 1-3. policy の sanity 条件を record 化する

`respects_policy_at_with` だけだと、
そこから「選ばれた job は候補集合にいる」「eligible である」を一般に引けません。

そこで、policy 側に最低限の健全性条件を持たせます。

```coq
Record PolicySanity (policy : DispatchPolicy) : Prop := mkPolicySanity {
  policy_some_in_candidates :
    forall jobs m sched t candidates j,
      policy jobs m sched t candidates (Some j) ->
      In j candidates ;

  policy_some_eligible :
    forall jobs m sched t candidates j,
      policy jobs m sched t candidates (Some j) ->
      eligible jobs m sched j t
}.
```

ここでは **None の意味までは固定しません**。
これが重要です。

理由は、将来

* idle を許す policy
* work-conserving でない policy
* OS 的な status event

を入れる余地を残すためです。

---

## 1-4. policy-valid schedule の wrapper を作る

次に、「dispatcher が作った schedule」ではなく、
「policy validity を満たす schedule」という scheduler relation を作ります。

```coq
Definition single_cpu_policy_schedule
    (policy : DispatchPolicy)
    (candidates_of : CandidateSource)
    (jobs : JobId -> Job)
    (m : nat)
    (sched : Schedule) : Prop :=
  m = 1 /\
  forall t, respects_policy_at_with policy jobs candidates_of sched t.

Definition single_cpu_policy_scheduler
    (policy : DispatchPolicy)
    (candidates_of : CandidateSource)
    : Scheduler :=
  mkScheduler (single_cpu_policy_schedule policy candidates_of).
```

これで、ロードマップにある

> scheduler を「dispatch の実行結果」ではなく「policy validity を満たす schedule」としても見られるようにする

が実現できます。

---

## 1-5. この file に置く補題

この file では、**policy sanity だけで証明できる補題**だけを置きます。

### 補題A: 選ばれた job は candidates にいる

```coq
Lemma respects_policy_at_with_in_candidates :
  forall policy
         (Hsane : PolicySanity policy)
         jobs candidates_of sched t j,
    respects_policy_at_with policy jobs candidates_of sched t ->
    sched t 0 = Some j ->
    In j (candidates_of jobs 1 sched t).
```

### 補題B: 選ばれた job は eligible

```coq
Lemma respects_policy_at_with_implies_eligible :
  forall policy
         (Hsane : PolicySanity policy)
         jobs candidates_of sched t j,
    respects_policy_at_with policy jobs candidates_of sched t ->
    sched t 0 = Some j ->
    eligible jobs 1 sched j t.
```

### 補題C: `CandidateSourceSpec` と組み合わせると `J j`

```coq
Lemma respects_policy_at_with_in_subset :
  forall policy
         (Hsane : PolicySanity policy)
         J candidates_of
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched t j,
    respects_policy_at_with policy jobs candidates_of sched t ->
    sched t 0 = Some j ->
    J j.
```

### 補題D: schedulable_by_on intro

```coq
Lemma single_cpu_policy_schedulable_by_on_intro :
  forall J policy candidates_of jobs sched,
    single_cpu_policy_schedule policy candidates_of jobs 1 sched ->
    valid_schedule jobs 1 sched ->
    feasible_schedule_on J jobs 1 sched ->
    schedulable_by_on J (single_cpu_policy_scheduler policy candidates_of) jobs 1.
```

---

# Phase 2: `DispatcherRefinement.v` を作る

## 目的

ここで初めて

**この concrete dispatcher はこの abstract policy を実装している**

を定義します。

---

## 2-1. refinement の定義

```coq
Definition dispatcher_refines_policy
    (spec : GenericDispatchSpec)
    (policy : DispatchPolicy) : Prop :=
  forall jobs m sched t candidates,
    policy jobs m sched t candidates
      (dispatch spec jobs m sched t candidates).
```

これで

* `edf_generic_spec` refines `edf_policy`
* `fifo_generic_spec` refines `fifo_policy`

を同じ形で言えます。

---

## 2-2. dispatcher 生成 schedule は policy validity を満たす

この file の主定理はこれです。

```coq
Lemma single_cpu_dispatch_schedule_respects_policy_at_with :
  forall spec policy candidates_of jobs sched t,
    dispatcher_refines_policy spec policy ->
    single_cpu_dispatch_schedule spec candidates_of jobs 1 sched ->
    respects_policy_at_with policy jobs candidates_of sched t.
```

これが通ると、各時刻の policy validity を
既存 bridge から引けます。

証明は単純で、

* `single_cpu_dispatch_schedule` を展開
* `sched t 0 = dispatch spec ...`
* refinement を適用

です。

---

## 2-3. horizon 版

```coq
Lemma single_cpu_dispatch_schedule_respects_policy_before :
  forall spec policy candidates_of jobs sched H,
    dispatcher_refines_policy spec policy ->
    single_cpu_dispatch_schedule spec candidates_of jobs 1 sched ->
    respects_policy_before policy jobs candidates_of sched H.
```

これは上の時刻ごとの補題を回すだけです。

---

## 2-4. scheduler relation の包含

次に、既存の dispatcher-based scheduler から
policy-valid scheduler への持ち上げを作ります。

```coq
Lemma single_cpu_dispatch_schedule_implies_single_cpu_policy_schedule :
  forall spec policy candidates_of jobs sched,
    dispatcher_refines_policy spec policy ->
    single_cpu_dispatch_schedule spec candidates_of jobs 1 sched ->
    single_cpu_policy_schedule policy candidates_of jobs 1 sched.
```

さらに scheduler 単位で見るなら

```coq
Lemma single_cpu_dispatch_scheduler_refines_policy_scheduler :
  forall spec policy candidates_of jobs sched,
    scheduler_rel (single_cpu_dispatch_scheduler_on spec candidates_of) jobs 1 sched ->
    dispatcher_refines_policy spec policy ->
    scheduler_rel (single_cpu_policy_scheduler policy candidates_of) jobs 1 sched.
```

のような形でもよいです。
ただし、まずは前者だけで十分です。

---

# Phase 3: EDF を新層へ載せる

ここは **いきなり `EDFOptimality.v` を書き換えない** のが重要です。

---

## 3-1. `UniPolicies/EDF.v` に `edf_policy` を追加

定義は tie を許す形にします。

```coq
Definition edf_policy : DispatchPolicy :=
  fun jobs m sched t candidates oj =>
    match oj with
    | None =>
        forall j, In j candidates -> ~ eligible jobs m sched j t
    | Some j =>
        In j candidates /\
        eligible jobs m sched j t /\
        forall j',
          In j' candidates ->
          eligible jobs m sched j' t ->
          job_abs_deadline (jobs j) <= job_abs_deadline (jobs j')
    end.
```

これで

* deterministic chooser としての `choose_edf`
* abstract policy としての `edf_policy`

が分離されます。

---

## 3-2. `edf_policy` の sanity を証明

```coq
Lemma edf_policy_sane : PolicySanity edf_policy.
```

これは `Some` 分岐を壊すだけです。

---

## 3-3. `choose_edf` が `edf_policy` を refine することを証明

```coq
Lemma choose_edf_refines_edf_policy :
  dispatcher_refines_policy edf_generic_spec edf_policy.
```

使う既存補題はほぼそのままです。

* `choose_edf_eligible`
* `choose_edf_in_candidates`
* `choose_edf_min_deadline`
* `choose_edf_none_if_no_eligible`

です。

これはかなり低リスクです。

---

## 3-4. `EDFLemmas.v` に互換レイヤを追加

ここが実務上いちばん大事です。
既存の

* `matches_choose_edf_at_with`
* `matches_choose_edf_before`

をすぐには消しません。

代わりに、まず次を追加します。

### 新補題 1

```coq
Lemma matches_choose_edf_at_with_implies_respects_edf_policy_at_with :
  forall jobs candidates_of sched t,
    matches_choose_edf_at_with jobs candidates_of sched t ->
    respects_policy_at_with edf_policy jobs candidates_of sched t.
```

これは `sched t 0 = choose_edf ...` と
`choose_edf_refines_edf_policy` からすぐ出ます。

### 新補題 2

```coq
Lemma respects_edf_policy_at_with_implies_respects_edf_priority_at_on :
  forall J candidates_of
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched t,
    respects_policy_at_with edf_policy jobs candidates_of sched t ->
    respects_edf_priority_at_on J jobs sched t.
```

これで、今 `matches_choose_edf_at_with` から出している
priority 性質を、新 API からも出せます。

### 新補題 3

既存名は wrapper にする

```coq
Lemma matches_choose_edf_at_with_implies_respects_edf_priority_at_on :
  ...
```

の中身を

* まず `respects_policy_at_with edf_policy ...` に落とす
* そこから `respects_edf_priority_at_on` を出す

構造に置き換えます。

これで `EDFOptimality.v` はほぼ触らずに済みます。

---

# Phase 4: FIFO も同じ枠に載せる

EDF だけだと設計の良し悪しが見えにくいので、
FIFO でも 1 本通すべきです。

---

## 4-1. `UniPolicies/FIFO.v` に `fifo_policy` を追加

```coq
Definition fifo_policy : DispatchPolicy :=
  fun jobs m sched t candidates oj =>
    match oj with
    | None =>
        forall j, In j candidates -> ~ eligible jobs m sched j t
    | Some j =>
        exists prefix suffix,
          candidates = prefix ++ j :: suffix /\
          eligible jobs m sched j t /\
          forall j', In j' prefix -> ~ eligible jobs m sched j' t
    end.
```

これで FIFO の「最初の eligible」が abstract policy になります。

---

## 4-2. `fifo_policy_sane`

```coq
Lemma fifo_policy_sane : PolicySanity fifo_policy.
```

---

## 4-3. `choose_fifo_refines_fifo_policy`

```coq
Lemma choose_fifo_refines_fifo_policy :
  dispatcher_refines_policy fifo_generic_spec fifo_policy.
```

使うのは既存の

* `choose_fifo_eligible`
* `choose_fifo_none_if_no_eligible`
* `choose_fifo_first_eligible`
* `choose_fifo_in_candidates`

です。

---

# Phase 5: ここまで終わったら初めて `Partitioned.v` へ接続

これは今回の主目的ではないですが、
新層が入ったあとにやると非常にきれいです。

---

## 5-1. まず今は `Partitioned.v` を壊さない

`valid_partitioned_schedule` はまだ alias のままでよいです。

---

## 5-2. 次の一手としてやるべきこと

各 CPU の local view に対して

* local dispatcher が local policy を refine
* よって local schedule は local policy validity を満たす

を示します。

その上で将来的に

```coq
valid_partitioned_schedule jobs sched :=
  partitioned_schedule_on jobs sched /\
  respects_assignment sched /\
  valid_schedule jobs m sched
```

あるいはさらに
「各 CPU view が local policy validity を満たす」
まで含める方向へ進めます。

ただし、これは今回の 2 ファイルが安定してからで十分です。

---

# 実装順のおすすめ

実際の作業順は、次の順が安全です。

## Step 1

`SchedulerValidity.v` を作る

* `DispatchPolicy`
* `PolicySanity`
* `respects_policy_at`
* `respects_policy_at_with`
* `respects_policy_before`
* `single_cpu_policy_schedule`
* `single_cpu_policy_scheduler`
* generic inspection lemmas

## Step 2

`DispatcherRefinement.v` を作る

* `dispatcher_refines_policy`
* `single_cpu_dispatch_schedule_respects_policy_at_with`
* `..._before`
* `single_cpu_dispatch_schedule_implies_single_cpu_policy_schedule`

## Step 3

`EDF.v` を拡張

* `edf_policy`
* `edf_policy_sane`
* `choose_edf_refines_edf_policy`

## Step 4

`EDFLemmas.v` に互換補題を追加

* `matches_choose_edf_at_with_implies_respects_edf_policy_at_with`
* `respects_edf_policy_at_with_implies_respects_edf_priority_at_on`

## Step 5

`FIFO.v` を拡張

* `fifo_policy`
* `fifo_policy_sane`
* `choose_fifo_refines_fifo_policy`

## Step 6

必要なら `EDFOptimality.v` の一部コメント・補題名を更新

ただし大規模 rewrite はしない

---

# 直近の着手タスク

一番最初にやるべき 3 つだけに絞ると、これです。

1. `SchedulerValidity.v` を新規作成
2. `DispatcherRefinement.v` を新規作成
3. `EDF.v` に `edf_policy` と `choose_edf_refines_edf_policy` を追加

この3つが入れば、設計の芯はできます。
