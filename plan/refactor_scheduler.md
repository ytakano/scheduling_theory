いまの構造を見ると、

* `DispatchInterface.v` は
  「**候補集合が与えられたときの 1 ステップの選択**」
* `EDF.v` / `FIFO.v` は
  その concrete instance
* `Partitioned.v` は
  すでに `dispatch` ベースで schedule 全体との整合性を **関係**として定義
* `SchedulerInterface.v` は
  逆に `Parameter Scheduler` と `run_scheduler` で **Schedule 全体を黒箱生成**する

という形で、**抽象化のレベルがずれている**のが本質的な問題です。
特に `SchedulerInterface.v` の `Scheduler` は inhabitant がなく、`SchedulableExamples.v` でも `run_scheduler alg = sched` を仮定して使っているので、現状ではかなり「外から等式を与えて使う箱」になっています。

そのため、今回の refactoring の目標は次に置くのがよいです。

## 目標

**`schedulable_by` を「dispatch から作られた scheduler relation」に対する述語へ変える。**

つまり、

* 下位層: `DispatchInterface`
  = 候補列から 1 つ選ぶ policy
* 上位層: `SchedulerInterface`
  = ある schedule がその policy と整合していることを述べる relation
* `schedulable_by`
  = その relation を満たす schedule のうち、valid かつ feasible なものが存在する

という形に揃えます。

---

## 提案する最終形

### 1. `Scheduler` を「関数」ではなく「schedule 上の relation」にする

`SchedulerInterface.v` の `Parameter Scheduler` / `run_scheduler` はやめて、たとえば次の方向にします。

```coq
Record Scheduler : Type := mkScheduler {
  scheduler_rel : (JobId -> Job) -> nat -> Schedule -> Prop
}.
```

そして `schedulable_by` は

```coq
Definition schedulable_by
    (alg : Scheduler) (jobs : JobId -> Job) (m : nat) : Prop :=
  exists sched,
    scheduler_rel alg jobs m sched /\
    valid_schedule jobs m sched /\
    feasible_schedule jobs m sched.
```

`_on` 版も同様です。

これで `Scheduler` は「schedule を生成する黒箱」ではなく、
**「この schedule はこのアルゴリズムの schedule である」**
という意味になります。

これは現在の `Partitioned.v` の `partitioned_schedule jobs sched xs : Prop` と非常に相性が良いです。

---

### 2. `Dispatch -> Scheduler` の bridge を作る

新しい bridge file を 1 つ作るのがよいです。名前はたとえば

* `UniSchedulerInterface.v`

です。

ここで、

```coq
Definition scheduler_from_dispatch
  (spec : GenericDispatchSpec)
  (candidates_of : (JobId -> Job) -> nat -> Schedule -> Time -> list JobId)
  : Scheduler := ...
```

のような wrapper を定義します。

単一 CPU 版なら relation は概ね

```coq
scheduler_rel (scheduler_from_dispatch spec candidates_of) jobs 1 sched :=
  forall t,
    sched t 0 =
      dispatch spec jobs 1 sched t (candidates_of jobs 1 sched t)
```

の形になります。必要なら `c <> 0 -> sched t c = None` も含めます。

ここで重要なのは、`candidates_of` を **固定 list ではなく関数**にすることです。
そうすると、

* EDF: 「その時点で見る候補列」
* FIFO: 「順序つき ready queue」
* 将来の RR: 「回転後の ready queue」
* OS 寄りモデル: 「pending/ready/runqueue 状態から作る候補列」

を全部同じ形で包めます。

---

### 3. EDF/FIFO は「dispatch spec + scheduler wrapper」を両方 export する

`EDF.v` / `FIFO.v` は今のまま `GenericDispatchSpec` の concrete instance を持っていてよいです。
その上で、

```coq
Definition edf_scheduler (candidates_of : ...) : Scheduler :=
  scheduler_from_dispatch edf_generic_spec candidates_of.
```

```coq
Definition fifo_scheduler (candidates_of : ...) : Scheduler :=
  scheduler_from_dispatch fifo_generic_spec candidates_of.
```

を追加します。

これで

* policy-level lemma は引き続き `DispatchInterface` 側で証明できる
* `schedulable_by` は EDF/FIFO に直接適用できる

ようになります。

---

## なぜこの形がよいか

### 理由1: `dispatch` と `scheduler` は本来レベルが違う

`dispatch` は 1 ステップの意思決定です。
`scheduler` は schedule 全体との整合性です。
ここを同一視すると、FIFO のような「順序状態」を持つものが不自然になります。

### 理由2: 今の `SchedulerInterface` は抽象すぎる

`run_scheduler` が黒箱なので、EDF/FIFO/Partitioned とつながりません。
relation 化すると、いま既にある `partitioned_schedule` と同じ流儀に統一できます。

### 理由3: 将来の OS 寄り拡張と相性がよい

候補列を外から与える設計にすると、

* ready / pending 分離
* runqueue 状態
* migration
* priority queue / heap
* RR の queue rotation

を後から追加しやすいです。

---

## 具体的な段階的 plan

### Phase 1: `SchedulerInterface.v` を relation ベースへ置き換える

やることは 3 つです。

1. `Parameter Scheduler` と `run_scheduler` を削除
2. `Record Scheduler := { scheduler_rel : ... }` に置換
3. `schedulable_by`, `schedulable_by_on` を existential witness 版に変更

この段階で既存補題もほぼそのまま書き直せます。

* `schedulable_by_implies_feasible`
* `schedulable_by_implies_schedulable_by_on`
* `schedulable_by_on_monotone`

は、今度は `exists sched` を剥がして証明するだけになります。

---

### Phase 2: bridge file を追加する

`DispatchSchedulerBridge.v` を追加して、

* 単一 CPU 用 wrapper
* 必要なら candidate soundness / completeness に関する補助補題
* `dispatch_ready` から `valid_schedule` を引く補題

を置きます。

ここで最低限欲しいのは、

```coq
scheduler_from_dispatch
single_cpu_dispatch_schedule
scheduler_from_dispatch_valid
```

あたりです。

この phase が終わると、`DispatchInterface` と `SchedulerInterface` が一本につながります。

---

### Phase 3: `EDF.v` / `FIFO.v` から `Scheduler` を export する

今ある

* `edf_generic_spec`
* `fifo_generic_spec`

はそのまま残し、追加で

* `edf_scheduler`
* `fifo_scheduler`

を定義します。

このとき大事なのは、**EDF/FIFO の policy lemma は壊さない**ことです。
`choose_edf_min_deadline` や `choose_fifo_first_ready` は引き続き dispatch-level lemma として残すべきです。

つまりこの phase の方針は、**既存資産を捨てずに上に wrapper を足す**です。

---

### Phase 4: `Partitioned.v` も `Scheduler` を返す wrapper を持たせる

`Partitioned.v` はすでに relation 的なので、ここはかなり自然です。

たとえば

```coq
Definition partitioned_scheduler
  (spec : GenericDispatchSpec)
  (assign : JobId -> CPU)
  (xs : list JobId)
  : Scheduler := ...
```

のような wrapper を追加します。

内部では既存の

* `partitioned_schedule`
* `valid_partitioned_schedule`
* `partitioned_schedule_implies_valid_schedule`

をそのまま使えばよいです。

これで

* 単一 CPU scheduler
* partitioned multiprocessor scheduler

の両方が **同じ `Scheduler` 抽象**に乗ります。

---

### Phase 5: examples を移植する

`SchedulableExamples.v` はかなり改善できます。

今は

```coq
Variable alg_sc : Scheduler.
Hypothesis alg_sc_runs_sched_sc : run_scheduler alg_sc jobs_sc 1 = sched_sc.
```

ですが、relation 版にすると

```coq
exists sched_sc, scheduler_rel alg_sc jobs_sc 1 sched_sc /\ ...
```

で直接書けます。

つまり、**不自然な `run_scheduler = sched_sc` 仮定が不要**になります。
これは今回の refactoring のかなり大きい成果です。

---

## 実装順のおすすめ

実際の作業順はこれが安全です。

1. `SchedulerInterface.v` を relation 化
2. 旧定理名を保ったまま証明を通す
3. `DispatchSchedulerBridge.v` を追加
4. `EDF.v` と `FIFO.v` に wrapper を追加
5. `SchedulableExamples.v` を移植
6. `Partitioned.v` に `partitioned_scheduler` wrapper を追加
7. 最後に不要になった `run_scheduler` 前提の痕跡を削除

この順だと、**下から順に壊さず移せます**。

---

## 設計上の注意点

### 1. `candidates` は list のまま残してよい

これは正しいです。
特に FIFO は順序が意味を持つので、`list JobId` を失うと policy が表現しづらくなります。

### 2. ただし `FIFO` はまだ「完全な FIFO scheduler」ではない

今の `choose_fifo` は正確には

**「与えられた候補列の中で、最初の ready job を選ぶ policy」**

です。
これは悪くありません。むしろ今回の refactoring ではそこを明確にして、

* `FIFO dispatch`
* `FIFO scheduler = queue order を供給する wrapper`

に分離するのがきれいです。

### 3. executable function にする必要はまだない

現段階では relation の方が自然です。
無理に `run_scheduler : ... -> Schedule` を保とうとすると、
候補集合生成や queue state まで全部関数的に持たせる必要があり、かなり重くなります。

いまのプロジェクト段階では、**relation ベースの scheduler 抽象**が最も良い落としどころです。

---

## この plan の一言要約

**`Dispatch` を消すのではなく、`Scheduler` を relation 化して `Dispatch` の上に載せる。**
これで EDF/FIFO/Partitioned/schedulable_by が同じ世界に入ります。
