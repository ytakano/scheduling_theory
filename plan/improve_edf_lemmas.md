## 目標

`Classical` に依存する

```coq
exists_first_edf_violation_before
```

を置き換えて、

* violation を `candidates_of` 上の**有限探索可能**な述語に落とす
* 「最初の violation 時刻」の抽出を **constructive** に行う
* その後の swap / repair / normalization でその述語を使う

ようにします。

---

## Phase 1: violation の定義を finite candidate ベースに作り直す

まず、今の一般版

```coq
Definition edf_violation_at ...
```

は `exists j j'` で全 JobId 上を量化しているので、constructive に最小時刻を取るには不向きです。

そこで、以下のような候補リスト依存版を追加します。

### 1-1. 明示 candidates 版

```coq
Definition edf_violation_at_in
    (J : JobId -> Prop)
    (jobs : JobId -> Job)
    (sched : Schedule)
    (t : Time)
    (cands : list JobId) : Prop :=
  exists j j',
    J j /\
    J j' /\
    sched t 0 = Some j /\
    In j' cands /\
    eligible jobs 1 sched j' t /\
    job_abs_deadline (jobs j') < job_abs_deadline (jobs j).
```

### 1-2. candidates_of 版

```coq
Definition edf_violation_at_with
    (J : JobId -> Prop)
    (candidates_of : CandidateSource)
    (jobs : JobId -> Job)
    (sched : Schedule)
    (t : Time) : Prop :=
  edf_violation_at_in J jobs sched t (candidates_of jobs 1 sched t).
```

この形にすると、`j'` の探索対象が有限リストになります。

---

## Phase 2: 既存の補題を新定義へ写す

すでにある補題のうち、次を finite candidate 版へ移します。

### 2-1. canonical 不一致から finite violation を出す

今ある

```coq
canonical_non_edf_step_has_other_min_or_better_eligible_job
```

は `candidates_of` の中に `j'` を出しています。
これはそのまま finite violation 構成の入口になります。

追加したい補題:

```coq
Lemma canonical_non_edf_step_implies_finite_violation :
  ...
  ~ matches_choose_edf_at_with jobs candidates_of sched t ->
  sched t 0 = Some j ->
  J j ->
  valid_schedule jobs 1 sched ->
  exists j',
    J j' /\
    In j' (candidates_of jobs 1 sched t) /\
    eligible jobs 1 sched j' t /\
    job_abs_deadline (jobs j') < job_abs_deadline (jobs j).
```

ここで `<` が直接出ないなら、まず `<= /\ j' <> j` を出してから、
`choose_edf = Some j` との矛盾や min 性質から strict 化する補題を 1 本足します。

### 2-2. canonical 一致なら finite violation はない

今ある

```coq
matches_choose_edf_at_with_no_earlier_eligible_job
```

は事実上これです。
新しい述語に合わせて、

```coq
Lemma matches_choose_edf_at_with_no_finite_violation :
  ...
  matches_choose_edf_at_with jobs candidates_of sched t ->
  ~ edf_violation_at_with J candidates_of jobs sched t.
```

を作ります。

### 2-3. old violation と new violation の関係

`CandidateSourceSpec` の `candidates_complete` を使えば、

* `edf_violation_at` から `edf_violation_at_with`
* 逆に `edf_violation_at_with` から `edf_violation_at`

の両方向を整理できます。

ただし、最適性証明で必要なのはたいてい前者です。
最初は片方向だけで十分です。

---

## Phase 3: decidable / boolean 判定器を作る

constructive に最初の violation 時刻を取るには、時刻 `t` ごとに

> violation かどうかを判定できる

必要があります。

ここで必要なのは、少なくとも次の decidable 性です。

* `JobId` の等価判定
* `J j` の判定
* `eligible jobs 1 sched j t` の判定
* `job_abs_deadline (jobs j1) < job_abs_deadline (jobs j2)` は `nat` なので判定可能

`eligible` については、定義が `released /\ ~ completed` の形ならかなり作りやすいです。
いま `eligibleb` があり、`choose_edf` 側でも boolean で扱っているので、ここを再利用できる可能性が高いです。

### 3-1. boolean predicate を作る

```coq
Definition edf_violationb_in ... (cands : list JobId) : bool := ...
Definition edf_violationb_at_with ... := ...
```

実装は二重走査で十分です。

* 実行中 `j` を `sched t 0` から取得
* `cands` の中に

  * `J j'`
  * `eligibleb ... j' t = true`
  * `deadline j' < deadline j`
    を満たすものがあるか `existsb` で調べる

これなら Job 全体を走査しません。

### 3-2. boolean と Prop の対応

```coq
Lemma edf_violationb_in_true_iff :
  ...
  edf_violationb_in ... cands = true <-> edf_violation_at_in ... cands.
```

ここが constructive 化の要です。

---

## Phase 4: horizon 内の最初の violation 時刻を constructive に取る

ここで初めて `classic` なしの “first violation” を作れます。

### 4-1. 有限時刻探索関数を作る

`0 .. H-1` を線形探索する関数を作ります。

```coq
Fixpoint first_nat_up_to (H : nat) (p : nat -> bool) : option nat := ...
```

仕様補題:

```coq
Lemma first_nat_up_to_some_spec :
  ...
Lemma first_nat_up_to_none_spec :
  ...
```

### 4-2. violation 用に specialize する

```coq
Definition first_edf_violation_before_with
    J candidates_of jobs sched H : option Time :=
  first_nat_up_to H (fun t => edf_violationb_at_with J candidates_of jobs sched t).
```

### 4-3. 仕様補題を示す

```coq
Lemma first_edf_violation_before_with_some :
  ...
  first_edf_violation_before_with ... H = Some t0 ->
  t0 < H /\
  edf_violation_at_with J candidates_of jobs sched t0 /\
  (forall t, t < t0 -> ~ edf_violation_at_with J candidates_of jobs sched t).
```

```coq
Lemma exists_first_edf_violation_before_with :
  ...
  (exists t, t < H /\ edf_violation_at_with J candidates_of jobs sched t) ->
  exists t0, ...
```

この最後の補題は、もはや `classic` 不要です。
存在仮定は boolean/探索関数の完全性から処理できます。

---

## Phase 5: repair / normalization 側を新述語に切り替える

次に、最適性証明で使う “bad step” を `edf_violation_at_with` に差し替えます。

### 5-1. first bad step の statement を置き換える

今後の補題は

* `edf_violation_at`
* `exists_first_edf_violation_before`

ではなく

* `edf_violation_at_with`
* `exists_first_edf_violation_before_with`

を参照するようにします。

### 5-2. exchange pair 抽出を candidates 内で行う

今の `edf_violation_exposes_exchange_pair` は一般版です。
これを

```coq
Lemma finite_violation_exposes_exchange_pair :
  ...
  edf_violation_at_with J candidates_of jobs sched t ->
  exists j',
    In j' (candidates_of jobs 1 sched t) /\
    eligible jobs 1 sched j' t /\
    job_abs_deadline (jobs j') < job_abs_deadline (jobs j).
```

へ差し替えます。

swap 補題に必要なのはむしろこちらです。

---

## Phase 6: ファイル構成を整理する

おすすめは次です。

### `EDFLemmas.v`

constructive core のみ置く。

* `matches_choose_edf_at_with`
* `respects_edf_priority_at_on`
* `edf_violation_at_in`
* `edf_violation_at_with`
* boolean 判定器
* boolean/Prop 対応
* constructive first violation

### `EDFOptimality.v`

* first violation を使う repair / normalization / optimality 本体

### `EDFOptimalityClassical.v`

必要なら旧版を一時退避
最終的に消してよいです。

---

## 実装順のおすすめ

着手順はこれが安全です。

### Step 1

`edf_violation_at_in` / `edf_violation_at_with` を追加

### Step 2

`matches_choose_edf_at_with_no_finite_violation` を証明

### Step 3

`edf_violationb_at_with` を作る
ここで `eligibleb` を再利用する

### Step 4

`first_nat_up_to` を作る

### Step 5

`exists_first_edf_violation_before_with` を証明

### Step 6

repair / normalization の bad-step API を置換
