# 目標

最終的に `Partitioned.v` を、

* 各 CPU ごとに

  * `local_jobset c`
  * `local_candidates_of c`
  * `CandidateSourceSpec (local_jobset c) (local_candidates_of c)`
* 単一 CPU の `DispatchSchedulerBridge` を CPU ごとに貼り合わせる

という形に直します。

つまり、今の

* `enumJ`
* `filter (assign j = c) enumJ`
* constant candidate list

ベースから、

* **CPU ごとの CandidateSource ベース**

に移します。

---

# 段階付き plan

## Phase 0: 先に壊さないための足場を作る

### 目的

大きく書き換える前に、「今の振る舞い」を補助定理として固定する。

### 作業

`Partitioned.v` の現行定義に対して、次を先に明示しておく。

* `local_candidates_of c` は現状 constant source である
* `partitioned_schedule_on` は「各 CPU が local 1-CPU dispatch bridge を満たす」と同値

  * これはすでに `partitioned_schedule_on_iff_local_rel` があるので活用
* `partitioned_schedule_implies_valid_schedule`
* `partitioned_schedule_implies_respects_assignment`

### 完了条件

少なくとも次が今のまま通る。

* `partitioned_schedule_on_iff_local_rel`
* `partitioned_schedule_implies_valid_schedule`
* `local_valid_feasible_on_implies_global`

### メモ

これは実質、以後の refactor の**回帰チェック用の中間到達点**です。

---

## Phase 1: `local_candidates` を「実装例」に格下げする

### 目的

`Partitioned.v` の中心を `enumJ/filter` から切り離す。

### 作業

Section の引数を次の形へ寄せます。

現状:

* `enumJ`
* `enumJ_complete`
* `enumJ_sound`

を直接使っている

変更後:

* `local_candidates_of : CPU -> CandidateSource`
* `local_candidates_spec :
    forall c, c < m ->
      CandidateSourceSpec (local_jobset c) (local_candidates_of c)`

を主引数にする

そして今の `enumJ` ベース実装は、
**その abstract interface の具体例**として残す。

つまり構造はこうです。

### 1-1. abstract core

`Partitioned.v` の core theorem 群は、以下だけを仮定する。

```coq
Variable assign : JobId -> CPU.
Variable m : nat.
Variable valid_assignment : forall j, assign j < m.
Variable spec : GenericDispatchSpec.
Variable J : JobId -> Prop.

Definition local_jobset (c : CPU) : JobId -> Prop :=
  fun j => J j /\ assign j = c.

Variable local_candidates_of : CPU -> CandidateSource.
Hypothesis local_candidates_spec :
  forall c, c < m ->
    CandidateSourceSpec (local_jobset c) (local_candidates_of c).
```

### 1-2. concrete instance

別 Section か末尾で、

```coq
Definition enum_local_candidates ...
Definition enum_local_candidates_of ...
Lemma enum_local_candidates_spec ...
```

を作って、現行の `enumJ/filter` 方式をそこに押し込める。

### 影響箇所

`Partitioned.v` 内の以下を更新。

* `partitioned_schedule_on`
* `partitioned_schedule_on_iff_local_rel`
* `partitioned_schedule_implies_respects_assignment`
* `partitioned_schedule_implies_valid_schedule`

### 完了条件

core theorems が `enumJ` なしで書けること。

---

## Phase 2: `partitioned_schedule_on` の定義を bridge-style に揃える

### 目的

single-CPU の `DispatchSchedulerBridge` と揃える。

### 作業

今は

```coq
sched t c = spec.(dispatch) jobs 1 (cpu_schedule sched c) t (local_candidates c)
```

ですが、これを

```coq
sched t c =
  spec.(dispatch) jobs 1 (cpu_schedule sched c) t
    (local_candidates_of c jobs 1 (cpu_schedule sched c) t)
```

の形に変えます。

ただし、ここで重要なのは **local CPU view に対して source を呼ぶ**ことです。
グローバル `sched` をそのまま渡すより、`cpu_schedule sched c` を渡した方が意味が揃います。

### あわせて直す補題

`partitioned_schedule_on_iff_local_rel` は、かなり自然に

* 各 CPU の `single_cpu_dispatch_schedule spec (local_candidates_of c)`
* を `cpu_schedule sched c` 上で満たす

という形になります。

### 完了条件

`partitioned_schedule_on_iff_local_rel` が、定義展開なしに「設計の中心補題」として使えるようになること。

---

## Phase 3: `valid_partitioned_schedule` を本当に公開述語にする

### 目的

今は alias なので、client が将来巻き込まれやすい。
これを **安定 API** にします。

### 推奨する進め方

一気に定義を強くするより、2 段階が安全です。

### 3-1. 生の構成述語を分離

まず

```coq
Definition raw_partitioned_schedule_on ...
```

を作り、現在の `partitioned_schedule_on` の中身を移す。

### 3-2. 公開述語を `valid_partitioned_schedule` に寄せる

次に

```coq
Definition valid_partitioned_schedule jobs sched : Prop :=
  raw_partitioned_schedule_on jobs sched.
```

とし、**全ての client-facing theorem を `valid_partitioned_schedule` ベースに言い換える**。

対象は少なくとも:

* `assignment_respect`
* `local_valid_feasible_on_implies_global`
* 将来の `partitioned_schedulable_by_on_intro`

### 3-3. その後で定義を強化

client の移行が済んだら、将来的に

```coq
Definition valid_partitioned_schedule jobs sched : Prop :=
  raw_partitioned_schedule_on jobs sched /\
  respects_assignment sched /\
  valid_schedule jobs m sched.
```

のように強められます。

ただし現時点では、**すぐ強化しなくてもよい**です。
まずは「公開定理が raw に依存しない」状態にするのが先です。

### 完了条件

`partitioned_schedule_on` は library 内部用、`valid_partitioned_schedule` が外向き用、という役割分担がはっきりすること。

---

## Phase 4: `partitioned_scheduler` に必要な証拠を寄せる

### 目的

今の `partitioned_scheduler` は `schedulable_by_on` に入るとき、外部からかなり多くの事実を再投入しないといけません。
ここを single-CPU 側に近づけます。

### 問題点

今の constructor は

```coq
Definition partitioned_scheduler
    (assign : JobId -> CPU)
    (n : nat)
    (spec : GenericDispatchSpec)
    (enumJ : list JobId)
    : Scheduler := ...
```

で、実際に必要な

* `J`
* `valid_assignment`
* `CandidateSourceSpec`
* local feasibility をどこから得るか

が scheduler の外にあります。

### 作業案

record を 1 つ導入するのがよいです。たとえば:

```coq
Record PartitionedDispatchContext := {
  part_assign : JobId -> CPU;
  part_m : nat;
  part_valid_assignment : forall j, part_assign j < part_m;
  part_spec : GenericDispatchSpec;
  part_J : JobId -> Prop;
  part_candidates_of : CPU -> CandidateSource;
  part_candidates_spec :
    forall c, c < part_m ->
      CandidateSourceSpec
        (fun j => part_J j /\ part_assign j = c)
        (part_candidates_of c)
}.
```

この context から

* `valid_partitioned_schedule`
* `partitioned_scheduler`

を作るようにすると、以後の補題がかなり整理されます。

### 完了条件

`partitioned_scheduler` が「何を前提に正しいのか」が型に現れること。

---

## Phase 5: グローバル schedulability への標準導線を作る

### 目的

今ある `local_valid_feasible_on_implies_global` を、
今後の main theorem 群の入り口にする。

### 作業

次の形の補題を標準入口にします。

```coq
Lemma partitioned_schedulable_by_on_from_local :
  ...
```

内容は、

* global schedule が `valid_partitioned_schedule`
* 各 CPU の local 1-CPU view が `local_jobset c` 上で feasible
* なら global に `schedulable_by_on J ... jobs m`

です。

今の `partitioned_schedulable_by_on_intro` は
かなり薄い wrapper なので、これだけだと partitioned の旨味が弱いです。
本命は「local から global を持ち上げる」方です。

### 完了条件

partitioned 層の典型的利用手順が

1. 各 CPU の local scheduler 性質を示す
2. `valid_partitioned_schedule` を示す
3. global schedulability を得る

の 3 ステップで定着すること。

---

## Phase 6: FIFO / RR を入れられる形へ確認する

### 目的

今回の refactor が本当に次の拡張を開くか確認する。

### 作業

最低限、次のどちらかを行う。

* `FIFO` 用の `local_candidates_of` の形を試作する
* `RoundRobin` を想定し、「schedule prefix に依存する candidate order」が表現できることを確認する

### 重要ポイント

ここで初めて、今回の refactor の価値が出ます。
今の static list 方式だと、RR の「回転」が素直に表せません。

### 完了条件

`Partitioned.v` が EDF 専用っぽい見た目から脱して、
本当に generic dispatch multicore 層になっていること。

---

# 実際の編集順

実装順としては、次の順を勧めます。

1. `Partitioned.v` に abstract な `local_candidates_of` / `local_candidates_spec` を導入
2. `partitioned_schedule_on` をそれに合わせて変更
3. 既存の `enumJ/filter` 方式を concrete instance として残す
4. `partitioned_schedule_on_iff_local_rel` を通す
5. `partitioned_schedule_implies_respects_assignment` を通す
6. `partitioned_schedule_implies_valid_schedule` を通す
7. `local_valid_feasible_on_implies_global` を通す
8. `valid_partitioned_schedule` を public API として整理
9. `partitioned_scheduler` を record/context ベースへ寄せる

---

# この refactor で直ること

この計画を完了すると、次が改善されます。

* `Partitioned.v` が EDF 寄りの static enumeration 設計から外れる
* single-CPU bridge と multicore bridge の形が揃う
* `valid_partitioned_schedule` が本当に stable interface になる
* FIFO / RR / priority 系を自然に載せやすくなる
* その先の clustered / global / migration への拡張の土台になる

---

# 逆に、今すぐやらなくてよいこと

今の段階では、まだ無理にやらなくてよいです。

* `valid_partitioned_schedule` の即時強化
* partitioned 用の巨大 typeclass 化
* global scheduler まで一気に一般化
* classical 除去のための大改造

まずは **Partitioned を bridge-style に揃える**のが先です。
