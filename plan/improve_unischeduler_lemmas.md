はい。`UniSchedulerLemmas.v` に追加すべき lemma を、**依存関係つき・実装順つき**でそのまま TODO に使える形で書きます。

大きな方針としては、ロードマップどおり **共通基盤 → 単一CPU抽象 scheduler の健全性 → 単一CPU policy 局所仕様 → その後に partitioned** の順で積むのが自然です。したがって `UniSchedulerLemmas.v` では、まず **Lv.2 の dispatch 健全性** と **Lv.4 へ渡すための service/ready 連携補題** を揃えるのが最優先です。

---

## まず結論

`UniSchedulerLemmas.v` で次に足すべきものは、次の 4 群です。

1. **chosen job の基本事実**
   これはかなり入っています。`ready / pending / released / not completed / min deadline` はもうあるので、土台は良いです。

2. **None/Some の特徴付けの強化**
   これも半分できています。ここに「idle しない」「ready 集合が空でない限り Some」を、より使いやすい形で揃えるべきです。

3. **候補集合 coverage 仮定の下での完全性**
   `candidates` が ready 集合をちゃんと表しているときの lemma 群です。partitioned にそのまま流用できます。

4. **決定性・tie の整理**
   EDF 依存の強い部分は `EDF.v` に置くとしても、`UniSchedulerLemmas.v` には「抽象 spec から言える範囲」の deterministic 風補題を薄く置いておくと、後で `Partitioned.v` が書きやすいです。

---

# 実装順つき plan

以下の順で追加するのがおすすめです。

---

## Step 1: `Schedule.v` 側に先に入れておくと楽な補題

これは `UniSchedulerLemmas.v` の前提として便利です。先に `Schedule.v` に追加しておくと証明がかなり軽くなります。

### S1-1. `ready_implies_released`

```coq
Lemma ready_implies_released :
  forall jobs m sched j t,
    ready jobs m sched j t ->
    released jobs j t.
```

### S1-2. `ready_implies_not_completed`

```coq
Lemma ready_implies_not_completed :
  forall jobs m sched j t,
    ready jobs m sched j t ->
    ~ completed jobs m sched j t.
```

### S1-3. `completed_monotone`

```coq
Lemma completed_monotone :
  forall jobs m sched j t1 t2,
    t1 <= t2 ->
    completed jobs m sched j t1 ->
    completed jobs m sched j t2.
```

### S1-4. `completed_not_ready`

```coq
Lemma completed_not_ready :
  forall jobs m sched j t,
    completed jobs m sched j t ->
    ~ ready jobs m sched j t.
```

### S1-5. `service_job_monotone`

```coq
Lemma service_job_monotone :
  forall m sched j t1 t2,
    t1 <= t2 ->
    service_job m sched j t1 <= service_job m sched j t2.
```

これらは `what_to_prove.md` の Lv.0 にほぼ対応しています。`UniSchedulerLemmas.v` 単体でも書けますが、意味的には `Schedule.v` にいる方が自然です。

---

## Step 2: `UniSchedulerLemmas.v` に追加する最小コア

ここが本命です。

### U2-1. chosen job は candidates に入っている

これは今の `UniSchedulerSpec` だけからは導けません。
理由は、interface に「choose は candidates から選ぶ」という公理がないからです。

なので、**まず interface を 1 つ拡張**するのがよいです。

#### 追加したい spec

```coq
choose_in_candidates :
  forall jobs m sched t candidates j,
    choose jobs m sched t candidates = Some j ->
    In j candidates ;
```

#### それに基づく lemma

```coq
Lemma choose_some_implies_in_candidates :
  forall j,
    spec.(choose) jobs m sched t candidates = Some j ->
    In j candidates.
```

これはかなり重要です。ないと後で `Partitioned.v` で
「assign された CPU の candidate list から選ばれた」
を言えません。

---

### U2-2. idle しないことの使いやすい形

`ready_exists_implies_choose_some` はありますが、実際に使うときは以下の形が便利です。

```coq
Lemma exists_ready_candidate_implies_not_none :
  (exists j, In j candidates /\ ready jobs m sched j t) ->
  spec.(choose) jobs m sched t candidates <> None.
```

証明は `ready_exists_implies_choose_some` からすぐです。

---

### U2-3. None なら全 candidate が unreleased または completed

これは `ready` の否定をそのまま使うより、分解された形の方が後続で便利です。

```coq
Lemma choose_none_implies_each_candidate_unreleased_or_completed :
  spec.(choose) jobs m sched t candidates = None ->
  forall j, In j candidates ->
    ~ released jobs j t \/ completed jobs m sched j t.
```

`~ ready` を `~(released /\ ~completed)` と見て古典に行かずに処理するなら少し工夫が要りますが、Rocq では

```coq
unfold ready, pending in ...
```

して `tauto` や `firstorder` で整理できることが多いです。

---

### U2-4. chosen job は deadline 最小候補であり、strictly smaller な ready candidate は存在しない

これはすでに
`choose_some_implies_no_earlier_deadline_candidate`
があります。
ただ、後続で使いやすい形として以下もあると便利です。

```coq
Lemma choose_some_implies_not_exists_strictly_better_ready :
  forall j,
    spec.(choose) jobs m sched t candidates = Some j ->
    ~ exists j',
        In j' candidates /\
        ready jobs m sched j' t /\
        job_abs_deadline (jobs j') < job_abs_deadline (jobs j).
```

実質同じですが、名前を後続ファイル向けにしてもよいです。既存名のままでも十分です。

---

## Step 3: coverage 仮定つき補題群を追加

ここが **partitioned への橋** になります。

`candidates` が「ちょうど ready job たち」である、という仮定のもとでの補題です。

### U3-1. coverage 仮定の定義

`UniSchedulerLemmas.v` 冒頭か `UniSchedulerInterface.v` 側に、述語として置くと読みやすくなります。

```coq
Definition candidate_covers_ready
    (jobs : JobId -> Job) (m : nat) (sched : Schedule) (t : Time)
    (candidates : list JobId) : Prop :=
  forall j, In j candidates <-> ready jobs m sched j t.
```

ただし、向きによっては強すぎます。実用上は分けた方が便利です。

```coq
Definition candidates_sound ... :=
  forall j, In j candidates -> ready jobs m sched j t.

Definition candidates_complete ... :=
  forall j, ready jobs m sched j t -> In j candidates.
```

おすすめは **sound / complete を分ける** ことです。

---

### U3-2. candidates_sound の下で、chosen job は本当に ready な candidate

```coq
Lemma choose_some_under_sound_candidates :
  candidates_sound jobs m sched t candidates ->
  forall j,
    spec.(choose) jobs m sched t candidates = Some j ->
    In j candidates /\ ready jobs m sched j t.
```

`choose_in_candidates` を入れるときれいに書けます。

---

### U3-3. candidates_complete の下で、ready が 1 つでもあれば Some

```coq
Lemma choose_some_if_any_ready_under_complete_candidates :
  candidates_complete jobs m sched t candidates ->
  (exists j, ready jobs m sched j t) ->
  exists j', spec.(choose) jobs m sched t candidates = Some j'.
```

`Partitioned.v` では、CPU ごとの ready 集合を `candidates` として渡すことになるので、この形が非常に使いやすいです。

---

### U3-4. sound + complete の下で None と “ready なし” が同値

```coq
Lemma choose_none_iff_no_ready_global :
  candidates_complete jobs m sched t candidates ->
  candidates_sound jobs m sched t candidates ->
  spec.(choose) jobs m sched t candidates = None <->
  forall j, ~ ready jobs m sched j t.
```

ただしこれは global すぎるので、実際は CPU ごとの universe を固定する必要が出るかもしれません。最初は無理に入れなくてもよいです。

---

## Step 4: “決定性”の入口だけ入れる

完全な determinism は現在の `UniSchedulerSpec` だけでは言いにくいです。
なぜなら、同じ deadline の tie で別 job を返しても spec を満たせるからです。

なので `UniSchedulerLemmas.v` では無理に

```coq
choose ... = Some j1 -> choose ... = Some j2 -> j1 = j2
```

を一般定理にしない方が安全です。

その代わり、**strict unique minimum があるときは chosen は一意** という形にします。

### U4-1. abstract 版 unique minimum

```coq
Lemma choose_unique_if_strictly_best :
  forall j,
    In j candidates ->
    ready jobs m sched j t ->
    (forall j', In j' candidates -> ready jobs m sched j' t ->
       j' <> j ->
       job_abs_deadline (jobs j) < job_abs_deadline (jobs j')) ->
    spec.(choose) jobs m sched t candidates = Some j.
```

ただし、これは現在の abstract spec だけからは導けません。
`choose_min_deadline` と `choose_some_if_ready` だけでは、「strictly best なら必ず j を返す」とまでは言えないからです。
これは **EDF.v に置くべき** 補題です。実際、すでに `choose_edf_unique_min` があり、ここは良いです。

なので結論として、**決定性は `UniSchedulerLemmas.v` ではなく policy file 側** に寄せるのがよいです。

---

# 依存関係つきの実装順

そのまま作業順にするとこうなります。

### 第1段階: `Schedule.v`

1. `service_job_monotone`
2. `completed_monotone`
3. `ready_implies_released`
4. `ready_implies_not_completed`
5. `completed_not_ready`

### 第2段階: `UniSchedulerInterface.v`

6. `choose_in_candidates` を record に追加

### 第3段階: `EDF.v`

7. `edf_scheduler_spec` に `choose_in_candidates` の証明を追加
   これは `min_dl_job_in` と `filter_In` ですぐ書けます。

### 第4段階: `UniSchedulerLemmas.v`

8. `choose_some_implies_in_candidates`
9. `exists_ready_candidate_implies_not_none`
10. `choose_none_implies_each_candidate_unreleased_or_completed`
11. `candidates_sound`
12. `candidates_complete`
13. `choose_some_under_sound_candidates`
14. `choose_some_if_any_ready_under_complete_candidates`

この順だと、各補題の依存が素直です。

---

# そのまま TODO にできる一覧

以下をそのままコピペして使えます。

```text
[Schedule.v]
- service_job_monotone
- completed_monotone
- ready_implies_released
- ready_implies_not_completed
- completed_not_ready

[UniSchedulerInterface.v]
- add choose_in_candidates to UniSchedulerSpec

[EDF.v]
- prove choose_edf_in_candidates
- extend edf_scheduler_spec with choose_edf_in_candidates

[UniSchedulerLemmas.v]
- choose_some_implies_in_candidates
- exists_ready_candidate_implies_not_none
- choose_none_implies_each_candidate_unreleased_or_completed
- define candidates_sound
- define candidates_complete
- choose_some_under_sound_candidates
- choose_some_if_any_ready_under_complete_candidates
```

---

# 各 lemma の優先度

優先順位をつけるなら次です。

### 最優先

* `service_job_monotone`
* `completed_monotone`
* `choose_in_candidates`
* `choose_some_implies_in_candidates`

### 次点

* `exists_ready_candidate_implies_not_none`
* `choose_none_implies_each_candidate_unreleased_or_completed`

### その次

* `candidates_sound`
* `candidates_complete`
* coverage 仮定つき補題群

この順で進めると、次の `Partitioned.v` にほぼそのままつながります。ロードマップでも、単一CPU共通性質を固めてから partitioned scheduling に進むのが自然な順序です。
