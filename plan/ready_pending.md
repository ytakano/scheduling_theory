# 目的

今のモデルで job の状態を整理し、

* `pending` = まだ dispatch 対象ではない
* `ready` = dispatch 対象である

を明確に分離し、今後

* work-conserving
* scheduler の正当性
* release / completion の補題
* 将来の blocked / migration 拡張

を証明しやすくする、というのが目的です。

---

# 全体方針

いきなり複雑な状態機械を入れるのではなく、まずは **最小限の意味づけ** で分離します。

最初の段階では次のように置くのがよいです。

* `pending j t` : `j` はまだ release 前
* `running j t` : `j` は時刻 `t` に実行中
* `completed j t` : `j` は時刻 `t` までに完了
* `runnable j t` : release 済みかつ未完了
* `ready j t` : runnable だが running ではない

つまり

* `pending` は「未来の job」
* `ready` は「今すぐ dispatch 可能だが CPU にはまだ載っていない job」

です。

この分け方なら、後で `blocked` を追加しても自然に拡張できます。

---

# 実施 plan

## Step 1: 状態概念を整理する

最初に、ファイル上で使う概念を明文化します。

導入する述語:

* `running`
* `completed`
* `runnable`
* `ready`
* `pending`

おすすめの依存関係はこれです。

```coq
running   : JobId -> Time -> Prop
completed : JobId -> Time -> Prop
runnable  : JobId -> Time -> Prop
ready     : JobId -> Time -> Prop
pending   : JobId -> Time -> Prop
```

意味は次です。

* `running j t` : `j` は `t` に CPU 上にある
* `completed j t` : `j` は `t` までに必要実行量を満たした
* `runnable j t` : `j` は release 済みで未完了
* `ready j t` : `j` は runnable だが running ではない
* `pending j t` : `j` はまだ release 前

この段階では `blocked` はまだ入れません。

---

## Step 2: 定義を最小形で導入する

まずは `Base.v` か、それに近い基礎ファイルに、以下のような定義を入れます。

```coq
Definition running (sched : Schedule) (j : JobId) (t : Time) : Prop :=
  exists c, sched t c = Some j.

Definition completed (sched : Schedule) (jobs : JobId -> Job) (j : JobId) (t : Time) : Prop :=
  service sched j t >= job_cost (jobs j).

Definition runnable (sched : Schedule) (jobs : JobId -> Job) (j : JobId) (t : Time) : Prop :=
  job_release (jobs j) <= t /\
  ~ completed sched jobs j t.

Definition ready (sched : Schedule) (jobs : JobId -> Job) (j : JobId) (t : Time) : Prop :=
  runnable sched jobs j t /\ ~ running sched j t.

Definition pending (jobs : JobId -> Job) (j : JobId) (t : Time) : Prop :=
  t < job_release (jobs j).
```

ここでのポイントは、`ready` を独立に定義せず、

* `runnable`
* `~ running`

の組として置くことです。

これで later extension がしやすくなります。

---

## Step 3: 基本整合性 lemma を追加する

次に `UniSchedulerLemmas.v` のような補題ファイルを新設または拡張して、基本補題を入れます。

最初に証明したいのは以下です。

### 3.1 pending と ready の排他

```coq
Lemma pending_not_runnable :
  forall sched jobs j t,
    pending jobs j t ->
    ~ runnable sched jobs j t.
```

```coq
Lemma pending_not_ready :
  forall sched jobs j t,
    pending jobs j t ->
    ~ ready sched jobs j t.
```

### 3.2 ready の分解

```coq
Lemma ready_implies_runnable :
  forall sched jobs j t,
    ready sched jobs j t ->
    runnable sched jobs j t.
```

```coq
Lemma ready_not_running :
  forall sched jobs j t,
    ready sched jobs j t ->
    ~ running sched j t.
```

### 3.3 completed との排他

```coq
Lemma completed_not_runnable :
  forall sched jobs j t,
    completed sched jobs j t ->
    ~ runnable sched jobs j t.
```

```coq
Lemma completed_not_ready :
  forall sched jobs j t,
    completed sched jobs j t ->
    ~ ready sched jobs j t.
```

### 3.4 release に関する補題

```coq
Lemma runnable_after_release :
  forall sched jobs j t,
    runnable sched jobs j t ->
    job_release (jobs j) <= t.
```

```coq
Lemma ready_after_release :
  forall sched jobs j t,
    ready sched jobs j t ->
    job_release (jobs j) <= t.
```

この層ができると、以後の定理で状態遷移の議論がかなり簡単になります。

---

## Step 4: running と scheduler の関係を整理する

次に `running` を scheduler と結びつけます。

追加したい補題:

```coq
Lemma scheduled_implies_running :
  forall sched j t c,
    sched t c = Some j ->
    running sched j t.
```

もし単一 CPU なら:

```coq
Lemma running_unique :
  forall sched j1 j2 t,
    running sched j1 t ->
    running sched j2 t ->
    j1 = j2 \/ j1 <> j2.
```

これは弱いので、本当に欲しいのは scheduler の well-formedness です。
たとえば multi-core なら、同じ job が複数 CPU で同時実行されないことを仮定または定義します。

```coq
Definition schedule_well_formed (sched : Schedule) : Prop :=
  forall t c1 c2 j,
    sched t c1 = Some j ->
    sched t c2 = Some j ->
    c1 = c2.
```

これを置くと

```coq
Lemma running_on_at_most_one_cpu :
  ...
```

が証明できます。

---

## Step 5: dispatch 側の責務を ready に限定する

ここが `pending` / `ready` 分離の実質的な中心です。

scheduler や dispatch の仕様で、

* 選ばれる job は `ready`
* `pending` な job は絶対に選ばれない

という形に整理します。

たとえば dispatcher の性質として:

```coq
Definition respects_ready_queue (sched : Schedule) (jobs : JobId -> Job) : Prop :=
  forall t c j,
    sched t c = Some j ->
    ready sched jobs j t \/ running sched j t.
```

あるいは、離散ステップごとに「dispatch 前 ready 集合から選ぶ」というモデルなら、

```coq
chosen_job ∈ ready_set
```

に相当する補題や仮定を置きます。

この段階で重要なのは、**scheduler の責務を ready に限定する**ことです。
release 前のものや未解禁のものは `pending` に押し込めておけば、scheduler correctness の議論がかなりきれいになります。

---

## Step 6: work-conserving を ready ベースで再定義する

`pending` と `ready` を分けたあと、work-conserving は `ready` に対して書くのが自然です。

単一 CPU なら例えば:

```coq
Definition idle (sched : Schedule) (t : Time) : Prop :=
  sched t cpu0 = None.

Definition work_conserving (sched : Schedule) (jobs : JobId -> Job) : Prop :=
  forall t,
    (exists j, ready sched jobs j t) ->
    ~ idle sched t.
```

multi-core なら、

* idle CPU がある
* ready job がある

なら idle を許さない、という形にします。

この定義にすると、`pending` な job がいるだけでは work-conserving 違反にならないので、意味がかなり明確です。

---

## Step 7: periodic / sporadic task model と接続する

次に `PeriodicTasks.v` や job generation model とつなぎます。

ここで追加したい補題は、

* release 前なら pending
* release 済みかつ未完了なら runnable
* runnable かつ非実行なら ready

です。

周期タスクで job が生成されるなら、

```coq
Lemma generated_job_pending_before_release :
  ...
```

```coq
Lemma generated_job_runnable_after_release_before_completion :
  ...
```

のような補題を入れると、task model から scheduler model へ橋渡しできます。

---

## Step 8: 将来拡張のために runnable を中心にする

ここが中期的に重要です。

後で `blocked` を入れたくなったとき、`ready` を直接書いていると修正範囲が大きくなります。
なので今の段階から

```coq
Definition runnable ... :=
  release 済み /\ 未完了 /\ 非blocked
```

に発展できるようにしておくのがよいです。

つまり将来は:

```coq
Definition runnable ... :=
  job_release ... <= t /\
  ~ completed ... /\
  ~ blocked ... .
```

```coq
Definition ready ... :=
  runnable ... /\ ~ running ...
```

という形に拡張します。

この設計にしておくと、

* sleep / wakeup
* suspension
* migration 中の中間状態
* OS 寄りの state machine

へ自然に進めます。

---

# ファイル単位の作業 plan

## 1. `Base.v`

やること:

* `running`
* `completed`
* `runnable`
* `ready`
* `pending`

の定義を追加する。

目標:

* 状態概念の基礎をここに置く。

---

## 2. `UniSchedulerLemmas.v`

やること:

* `pending_not_runnable`
* `pending_not_ready`
* `ready_implies_runnable`
* `ready_not_running`
* `completed_not_runnable`
* `completed_not_ready`
* `ready_after_release`
* `runnable_after_release`

を証明する。

目標:

* 状態整合性の土台を作る。

---

## 3. `DispatchSchedule.v`

やること:

* dispatch が `ready` な job だけを対象にすることを明文化
* 必要なら dispatcher の well-formedness を定義

目標:

* scheduler 側の責務を `ready` に限定する。

---

## 4. `PeriodicTasks.v` あるいは生成モデル側

やること:

* generated job が release 前は `pending`
* release 後かつ未完了なら `runnable`

を示す補題を置く。

目標:

* task model と scheduler model を接続する。

---

## 5. 将来用の `WorkConservation.v`

やること:

* `ready` ベースの work-conserving を定義
* idle と ready の関係を証明

目標:

* 中間目標の定理を証明しやすくする。

---

# 優先順位つき TODO

実際に着手する順番としては、次がおすすめです。

## 最優先

1. `Base.v` に `running/completed/runnable/ready/pending` を定義
2. `UniSchedulerLemmas.v` を作り、基本補題を入れる
3. `DispatchSchedule.v` で「選ばれる job は ready」を明確化

## 次点

4. `PeriodicTasks.v` と接続
5. `work_conserving` を `ready` ベースで再定義

## 後回しでよい

6. `blocked`
7. `migration`
8. local/global run queue の分岐

---

# この plan のゴール

この plan が終わると、少なくとも次が明確になります。

* release 前の job を scheduler の証明から除外できる
* ready 集合だけを dispatch の対象にできる
* completed job を自然に除外できる
* work-conserving の定義がきれいになる
* 将来の blocked/suspended/migration 拡張がしやすくなる

---

# おすすめの最初の中間目標

この plan を進めるうえで、最初の小さな到達点は次です。

1. `ready` と `pending` の定義を導入
2. `pending_not_ready` を証明
3. `ready_after_release` を証明
4. `completed_not_ready` を証明
5. `work_conserving` を `ready` ベースで定義

ここまで行くと、「状態分離がうまく働いている」とかなり言いやすくなります。

次に進めるなら、`Base.v` と `UniSchedulerLemmas.v` にそのまま貼れる **Rocq の雛形コード** まで具体的に書けます。
