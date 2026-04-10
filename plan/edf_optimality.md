# EDF 最適性定理の証明計画

# まず決めるべき実装方針

最適性定理は、最初は次の形に絞るのがよいです。

* **single CPU**
* **有限 job 集合 `J`**
* `candidates_of` は `J` を過不足なく拾う (`CandidateSourceSpec`)
* 「任意の feasible schedule から、EDF 形の feasible schedule を作れる」

つまり最終定理は、まずは `schedulable_by_on` に直結させるよりも、**正規化定理**として作るのがよいです。

```coq
Theorem edf_normalization_on_finite_jobs :
  ...
  valid_schedule jobs 1 sched ->
  feasible_schedule_on J jobs 1 sched ->
  exists sched',
    valid_schedule jobs 1 sched' /\
    feasible_schedule_on J jobs 1 sched' /\
    (forall t, t < H -> matches_choose_edf_at_with jobs candidates_of sched' t).
```

そのあとで `single_cpu_dispatch_schedulable_by_on_intro` を使って `schedulable_by_on` に持ち上げます。

---

# ファイル分割案

おすすめは 2 段です。

* `theories/UniPolicies/EDFTransform.v`

  * swap / repair の定義
  * service 比較
  * validity / feasibility preservation
* `theories/UniPolicies/EDFOptimality.v`

  * first violation を潰す補題
  * 反復正規化
  * 最終定理

`EDFLemmas.v` に全部入れると大きくなりすぎます。

---

# 具体的 lemma 一覧と証明順序

## Phase 1: 有限 horizon を job 集合から作る

`Partitioned.v` にある `enumJ_complete` / `enumJ_sound` の流儀を、EDF optimality 側でも使います。

### 1. `deadline_horizon`

まず定義です。

```coq
Definition deadline_horizon
    (jobs : JobId -> Job)
    (enumJ : list JobId) : nat :=
  S (fold_right Nat.max 0 (map (fun j => job_abs_deadline (jobs j)) enumJ)).
```

### 2. `in_enum_implies_deadline_lt_horizon`

```coq
Lemma in_enum_implies_deadline_lt_horizon :
  forall jobs enumJ j,
    In j enumJ ->
    job_abs_deadline (jobs j) < deadline_horizon jobs enumJ.
```

### 3. `J_implies_deadline_lt_horizon`

```coq
Lemma J_implies_deadline_lt_horizon :
  forall J enumJ jobs j,
    (forall j, J j -> In j enumJ) ->
    J j ->
    job_abs_deadline (jobs j) < deadline_horizon jobs enumJ.
```

この 2 本は軽いですが、後で
`eligible_feasible_implies_runs_later_before_deadline`
から得た `t'` がちゃんと `H` 未満に入ることを示すのに使えます。

---

## Phase 2: repair 対象の 2 時刻を固定する

ここでは「swap 可能な pair」を明示化します。
既存の

* `exists_first_edf_violation_before_with`
* `edf_violation_exposes_exchange_pair`
* `eligible_feasible_implies_runs_later_before_deadline`

を繋ぐだけです。

### 4. `first_violation_has_repair_witness`

概略はこうです。

```coq
Lemma first_violation_has_repair_witness :
  forall J J_bool candidates_of
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched H t j,
    (forall x, J_bool x = true <-> J x) ->
    valid_schedule jobs 1 sched ->
    feasible_schedule_on J jobs 1 sched ->
    t < H ->
    sched t 0 = Some j ->
    edf_violation_at_with J candidates_of jobs sched t ->
    exists j' t',
      J j' /\
      eligible jobs 1 sched j' t /\
      job_abs_deadline (jobs j') < job_abs_deadline (jobs j) /\
      t <= t' /\
      t' < job_abs_deadline (jobs j') /\
      sched t' 0 = Some j'.
```

証明順:

1. `edf_violation_at_with` から `j'` を取る
2. `CandidateSourceSpec` で `In j' (...) -> J j'`
3. `eligible_feasible_implies_runs_later_before_deadline` で `t'` を取る

この lemma は、以後の repair の入口になります。

---

## Phase 3: repair schedule を定義する

ここは最重要です。
最初は **2 点入れ替え** に限定した定義でよいです。

### 5. `swap_at`

```coq
Definition swap_at
    (sched : Schedule)
    (t1 t2 : Time) : Schedule :=
  fun t c =>
    if Nat.eqb c 0 then
      if Nat.eqb t t1 then sched t2 0
      else if Nat.eqb t t2 then sched t1 0
      else sched t c
    else sched t c.
```

single CPU 専用ならこれで十分です。
あとで一般化できます。

### 6. `swap_at_same_outside`

```coq
Lemma swap_at_same_outside :
  forall sched t1 t2 t c,
    c <> 0 \/ (t <> t1 /\ t <> t2) ->
    swap_at sched t1 t2 t c = sched t c.
```

### 7. `swap_at_t1` / `swap_at_t2`

```coq
Lemma swap_at_t1 :
  forall sched t1 t2,
    swap_at sched t1 t2 t1 0 = sched t2 0.

Lemma swap_at_t2 :
  forall sched t1 t2,
    swap_at sched t1 t2 t2 0 = sched t1 0.
```

この 3 本で、repair 後の schedule を rewite しやすくなります。

---

## Phase 4: swap が service に与える影響を解析する

ここは validity より先にやるのが楽です。
対象は `j` と `j'` と、それ以外の job の 3 種類です。

### 8. `swap_at_service_unchanged_other_job`

```coq
Lemma swap_at_service_unchanged_other_job :
  forall sched j j1 j2 t1 t2 T,
    sched t1 0 = Some j1 ->
    sched t2 0 = Some j2 ->
    j <> j1 ->
    j <> j2 ->
    service_job 1 (swap_at sched t1 t2) j T =
    service_job 1 sched j T.
```

### 9. `swap_at_service_prefix_before_t1`

```coq
Lemma swap_at_service_prefix_before_t1 :
  forall sched j t1 t2 T,
    T <= t1 ->
    service_job 1 (swap_at sched t1 t2) j T =
    service_job 1 sched j T.
```

### 10. `swap_at_service_job1`

`j1` の service は `[t1, t2)` の prefix では早まるが、最終総量は同じ、という補題です。

最初は 2 本に分けるのがよいです。

```coq
Lemma swap_at_service_job1_before_t2 :
  forall sched j1 j2 t1 t2 T,
    t1 < t2 ->
    sched t1 0 = Some j1 ->
    sched t2 0 = Some j2 ->
    j1 <> j2 ->
    t1 < T <= t2 ->
    service_job 1 (swap_at sched t1 t2) j1 T =
    S (service_job 1 sched j1 T).

Lemma swap_at_service_job1_after_t2 :
  forall sched j1 j2 t1 t2 T,
    t2 < T ->
    sched t1 0 = Some j1 ->
    sched t2 0 = Some j2 ->
    j1 <> j2 ->
    service_job 1 (swap_at sched t1 t2) j1 T =
    service_job 1 sched j1 T.
```

`j2` についても対称版を作ります。

この段階で、`j'` は deadline までに 1 単位早く service を受ける、という主張が出せます。

---

## Phase 5: swap が validity を壊さないことを示す

ここは repair 先の時刻 `t'` の job が `j'` で、そこに `j` を後ろ倒ししても問題ないことを示します。
この部分が一番 delicate です。

ただし、今回の設定では

* `sched t 0 = Some j`
* `sched t' 0 = Some j'`
* `j'` は `t` で eligible
* `t <= t' < deadline(j') < deadline(j)`

なので、`j` を `t'` に置いても、通常は eligibility が壊れません。
理由は `j` はもともと `t` で走っているので released であり、さらに `j'` を前倒ししたことで `j` の過剰 service は増えないからです。

ここは 2 補題に分けるのがよいです。

### 11. `swap_at_validity_new_front_job`

```coq
Lemma swap_at_validity_new_front_job :
  forall jobs sched j j' t t',
    valid_schedule jobs 1 sched ->
    sched t 0 = Some j ->
    sched t' 0 = Some j' ->
    eligible jobs 1 sched j' t ->
    valid_step jobs 1 (swap_at sched t t') t 0 j'.
```

`valid_step` がないなら、`valid_schedule` の定義をその場で展開して、その時点 `t` での released / not completed を示します。

### 12. `swap_at_validity_new_back_job`

```coq
Lemma swap_at_validity_new_back_job :
  forall jobs sched j j' t t',
    valid_schedule jobs 1 sched ->
    sched t 0 = Some j ->
    sched t' 0 = Some j' ->
    t <= t' ->
    job_abs_deadline (jobs j') < job_abs_deadline (jobs j) ->
    valid_step jobs 1 (swap_at sched t t') t' 0 j.
```

### 13. `swap_at_preserves_valid_schedule`

```coq
Lemma swap_at_preserves_valid_schedule :
  forall jobs sched j j' t t',
    valid_schedule jobs 1 sched ->
    sched t 0 = Some j ->
    sched t' 0 = Some j' ->
    eligible jobs 1 sched j' t ->
    t <= t' ->
    job_abs_deadline (jobs j') < job_abs_deadline (jobs j) ->
    valid_schedule jobs 1 (swap_at sched t t').
```

これで feasibility preservation の基盤ができます。

---

## Phase 6: swap が deadline miss を増やさないことを示す

ここが最適性の心臓部です。
最初から「全 job で完全保存」を目指すより、影響を受ける job だけ追う方がよいです。

### 14. `swap_at_preserves_missed_deadline_other_job`

```coq
Lemma swap_at_preserves_missed_deadline_other_job :
  forall J jobs sched j j' t t' x,
    J x ->
    x <> j ->
    x <> j' ->
    missed_deadline jobs 1 (swap_at sched t t') x <->
    missed_deadline jobs 1 sched x.
```

### 15. `swap_at_improves_front_job`

```coq
Lemma swap_at_improves_front_job :
  forall jobs sched j j' t t',
    t <= t' ->
    t' < job_abs_deadline (jobs j') ->
    sched t 0 = Some j ->
    sched t' 0 = Some j' ->
    ~ missed_deadline jobs 1 sched j' ->
    ~ missed_deadline jobs 1 (swap_at sched t t') j'.
```

実際にはもっと強く、
`service_job ... deadline(j')` が 1 増える
という形でもよいです。

### 16. `swap_at_does_not_hurt_later_deadline_job`

```coq
Lemma swap_at_does_not_hurt_later_deadline_job :
  forall jobs sched j j' t t',
    t <= t' ->
    job_abs_deadline (jobs j') < job_abs_deadline (jobs j) ->
    sched t 0 = Some j ->
    sched t' 0 = Some j' ->
    ~ missed_deadline jobs 1 sched j ->
    ~ missed_deadline jobs 1 (swap_at sched t t') j.
```

この補題はやや重いですが、deadline 順序を使う本質部分です。
証明では、

* `j` は `t'` で 1 単位失う
* でも `j'` の deadline より後ろにしか影響しない
* `deadline(j') < deadline(j)` なので `j` の own deadline までに取り返せる

という論法ではなく、今回の 2 点 swap では `j` は `t'` で実行されるので、**総 service は保存**されます。
したがって実はこの補題はかなり簡単になり、

```coq
service_job 1 (swap_at ...) j (job_abs_deadline (jobs j))
=
service_job 1 sched j (job_abs_deadline (jobs j))
```

を示せれば済みます。

なので先に次を作るのがよいです。

### 16'. `swap_at_service_at_deadline_same_for_back_job`

```coq
Lemma swap_at_service_at_deadline_same_for_back_job :
  forall jobs sched j j' t t',
    t <= t' ->
    t' < job_abs_deadline (jobs j) ->
    sched t 0 = Some j ->
    sched t' 0 = Some j' ->
    service_job 1 (swap_at sched t t') j (job_abs_deadline (jobs j)) =
    service_job 1 sched j (job_abs_deadline (jobs j)).
```

これから missed deadline preservation が出せます。

### 17. `swap_at_preserves_feasible_schedule_on`

```coq
Lemma swap_at_preserves_feasible_schedule_on :
  forall J jobs sched j j' t t',
    valid_schedule jobs 1 sched ->
    feasible_schedule_on J jobs 1 sched ->
    J j ->
    J j' ->
    sched t 0 = Some j ->
    sched t' 0 = Some j' ->
    eligible jobs 1 sched j' t ->
    t <= t' ->
    t' < job_abs_deadline (jobs j') ->
    job_abs_deadline (jobs j') < job_abs_deadline (jobs j) ->
    feasible_schedule_on J jobs 1 (swap_at sched t t').
```

これで 1-step repair が完成です。

---

## Phase 7: 最初の violation を 1 つ潰す

ここで既存補題群を結合します。

### 18. `repair_first_violation`

```coq
Lemma repair_first_violation :
  forall J J_bool candidates_of
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched H t0 j,
    (forall x, J_bool x = true <-> J x) ->
    valid_schedule jobs 1 sched ->
    feasible_schedule_on J jobs 1 sched ->
    t0 < H ->
    sched t0 0 = Some j ->
    edf_violation_at_with J candidates_of jobs sched t0 ->
    (forall t, t < t0 -> ~ edf_violation_at_with J candidates_of jobs sched t) ->
    exists sched',
      valid_schedule jobs 1 sched' /\
      feasible_schedule_on J jobs 1 sched' /\
      agrees_before sched sched' t0 /\
      matches_choose_edf_at_with jobs candidates_of sched' t0.
```

証明順:

1. `first_violation_has_repair_witness` で `j'`,`t'`
2. `sched' := swap_at sched t0 t'`
3. validity / feasibility preservation
4. `agrees_before` は `t0` より前では自明
5. `t0` で走る job が `j'` になるので `matches_choose_edf_at_with` を示す

最後の 5 は、
`j'` が choose_edf の最小 deadline 候補であることまで必要です。
ここは `edf_violation_at_with` だけだと弱いので、repair 用に使う `j'` は「単に earlier job」ではなく、**canonical_non_edf_step_has_other_min_or_better_eligible_job** から取り直すのがよいです。

つまり `repair_first_violation` では次の既存補題を使う方が安全です。

* `canonical_non_edf_step_has_other_min_or_better_eligible_job`

ただしこれは今 `~ matches_choose_edf_at_with` を前提にして `<=` を返します。
そこで次を追加するとよいです。

### 18'. `first_violation_yields_canonical_repair_job`

```coq
Lemma first_violation_yields_canonical_repair_job :
  forall ...,
    valid_schedule jobs 1 sched ->
    sched t 0 = Some j ->
    J j ->
    edf_violation_at_with J candidates_of jobs sched t ->
    exists j',
      In j' (candidates_of jobs 1 sched t) /\
      eligible jobs 1 sched j' t /\
      job_abs_deadline (jobs j') <= job_abs_deadline (jobs j) /\
      j' <> j /\
      choose_edf jobs 1 sched t (candidates_of jobs 1 sched t) = Some j'.
```

これは既存の `canonical_non_edf_step_has_other_min_or_better_eligible_job` と `choose_edf_some_if_exists` を束ねた補題です。
repair 後に `matches_choose_edf_at_with` を直接出しやすくなります。

---

## Phase 8: violation を前に持たない EDF 形へ反復正規化する

ここは自然数 measure を使います。
一番簡単なのは「最初の violation 時刻」が strict に進むことです。

### 19. `repair_pushes_first_violation_forward`

```coq
Lemma repair_pushes_first_violation_forward :
  forall ... sched sched' t0 H,
    ...
    agrees_before sched sched' t0 ->
    matches_choose_edf_at_with jobs candidates_of sched' t0 ->
    (forall t, t < t0 -> ~ edf_violation_at_with J candidates_of jobs sched t) ->
    (forall t, t <= t0 -> ~ edf_violation_at_with J candidates_of jobs sched' t).
```

これで first violation time が進みます。

### 20. `edf_normalize_up_to`

`H` による帰納法で十分です。

```coq
Lemma edf_normalize_up_to :
  forall J J_bool candidates_of
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched H,
    (forall x, J_bool x = true <-> J x) ->
    valid_schedule jobs 1 sched ->
    feasible_schedule_on J jobs 1 sched ->
    exists sched',
      valid_schedule jobs 1 sched' /\
      feasible_schedule_on J jobs 1 sched' /\
      matches_choose_edf_before jobs candidates_of sched' H.
```

証明イメージ:

* `first_nat_up_to` で violation を探す
* なければ終わり
* あれば `repair_first_violation`
* violation が前進するので再帰

ここは関数的反復を実装せず、`H - t0` のような measure で存在証明だけしてもよいです。

---

## Phase 9: `matches_choose_edf_before` から scheduler relation へ

すでに `DispatchSchedulerBridge.v` に

* `single_cpu_dispatch_schedule`
* `single_cpu_dispatch_valid`
* `single_cpu_dispatch_schedulable_by_on_intro`

があります。
なので EDF 用には「EDF canonical schedule は dispatch schedule と一致する」を 1 本作ればよいです。

### 21. `matches_choose_edf_before_implies_dispatch_prefix`

```coq
Lemma matches_choose_edf_before_implies_dispatch_prefix :
  forall candidates_of jobs sched H,
    matches_choose_edf_before jobs candidates_of sched H ->
    forall t, t < H ->
      sched t 0 =
      single_cpu_dispatch_schedule edf_generic_spec candidates_of jobs sched t 0.
```

ただ、最終的には `single_cpu_dispatch_schedule` 自体が self-referential なので、ここは形式を少し合わせる必要があります。
もしこの形が扱いづらければ、最終定理はまず

* `exists sched, valid_schedule /\ feasible_schedule_on /\ matches_choose_edf_before ...`

までで一区切りにしてもよいです。

---

## Phase 10: 最終定理

### 22. `edf_optimality_on_finite_jobs`

```coq
Theorem edf_optimality_on_finite_jobs :
  forall J J_bool enumJ candidates_of
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs,
    (forall x, J_bool x = true <-> J x) ->
    (forall j, J j -> In j enumJ) ->
    (forall j, In j enumJ -> J j) ->
    feasible_on J jobs 1 ->
    schedulable_by_on J (edf_scheduler candidates_of) jobs 1.
```

証明の流れは:

1. `feasible_on` から feasible witness `sched`
2. `H := deadline_horizon jobs enumJ`
3. `edf_normalize_up_to ... H`
4. `H` まで EDF 形なら、`J` の全 job は deadline が `H` 未満なので feasible
5. bridge で `schedulable_by_on`

---

# 実際の着手順

いま本当に書き始める順番は、次がよいです。

1. `deadline_horizon`
2. `first_violation_has_repair_witness`
3. `swap_at` / `swap_at_t1` / `swap_at_t2`
4. `swap_at_service_unchanged_other_job`
5. `swap_at_service_job1_before_t2`
6. `swap_at_service_job1_after_t2`
7. `swap_at_preserves_valid_schedule`
8. `swap_at_preserves_feasible_schedule_on`
9. `repair_first_violation`
10. `edf_normalize_up_to`
11. `edf_optimality_on_finite_jobs`

---

# 注意点

1. **`edf_violation_at_with` は strict earlier job の存在しか言わない**
   repair 後に `matches_choose_edf_at_with` を出すには、`choose_edf` が返す job を使う方が安全です。
   なので repair の front job は、
   violation witness そのものではなく、`choose_edf` の返り値に寄せるのがよいです。

2. **swap の feasibility preservation は「service at deadline」で見ると楽**
   `completed` を直接追うより、
   `missed_deadline_iff_service_lt_cost_at_deadline`
   を徹底して使う方が詰まりにくいです。

3. **single CPU に固定する**
   今は `m = 1` に徹した方がよいです。一般化は後回しで十分です。

4. **Classical は増やさない**
   `exists_first_edf_violation_before_with` がすでに constructive なので、optimality 側は classical を使わず進めた方がきれいです。
