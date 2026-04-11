# 目標

まず目標は、EDF 版に揃えて次の形にするのがよいです。

`llf_optimality_on_finite_jobs`

つまり、

* 有限 job 集合 `J`
* 候補集合生成器 `candidates_of`
* その健全性 `CandidateSourceSpec`
* 単一 CPU
* feasible witness の存在

を仮定して、

* `schedulable_by_on J (llf_scheduler candidates_of) jobs 1`

を示す、という形です。

これは `edf_optimality_on_finite_jobs` とほぼ同じ statement にできます。
したがって、**最終ゴールは EDFOptimality の LLF 版ファイルを作ること**です。

---

# いま不足している本質

LLF で本当に足りないのは、単なる chooser ではなく、**交換引数に必要な “repair layer”** です。

EDF 版では、

* canonical 定義
* 非 canonical 時刻の抽出
* repair witness の抽出
* `swap_at` による修復
* prefix 正規化
* truncation
* scheduler bridge

という流れができています。

LLF でも大筋は同じです。
ただし EDF と違って、LLF は優先度が `deadline(j)` ではなく

* `laxity jobs sched j t`

という **schedule-dependent / time-dependent metric** です。
このため、単純に EDF の repair をコピーするだけでは足りず、**laxity に基づく交換補題**を新たに作る必要があります。

---

# LLF optimality への新ロードマップ

## Phase 1. LLF canonical 層を追加する

まず EDF の `EDFLemmas.v` に相当する `LLFLemmas.v` を作るのが最優先です。

ここで入れるべきものは次です。

### 1-1. choose の prefix 不変性

`choose_min_metric_agrees_before` はすでに一般化されているので、LLF 用に薄いラッパだけ作ればよいです。

必要なのは例えば次です。

* `choose_llf_agrees_before`
* `llf_dispatch_agrees_before`

LLF の metric は `laxity` ですが、`laxity` は時刻 `t` 以前の prefix だけで決まるので、`agrees_before` から不変性を引けるはずです。
ここで必要なら先に

* `service_agrees_before`
* `remaining_cost_agrees_before`
* `laxity_agrees_before`

を補題として明示化してください。
`choose_min_metric_agrees_before` を素直に使うには、metric 関数自体が prefix agreement の下で不変だと示せる形にしておくと後が楽です。

### 1-2. canonical LLF step の定義

EDF 版の

* `matches_choose_edf_at_with`
* `matches_choose_edf_before`

に対応する LLF 版を作ります。

たとえば

* `matches_choose_llf_at_with`
* `matches_choose_llf_before`

です。

この段階では、定義は **“schedule が choose_llf の返り値と一致する”** で十分です。
policy 的には tie を含む argmin 仕様ですが、canonicalization 手続きでは具体 chooser との一致に落としておく方が normalization に使いやすいです。

### 1-3. boolean canonical predicate

EDF 版の `is_canonical_at_b` に対応する LLF 版を作ります。

* `is_llf_canonical_at_b`
* `..._true_iff`
* `..._false_iff`

これは normalization ループでそのまま使えます。

---

## Phase 2. LLF の局所違反抽出を作る

次に、EDF の「より早い deadline job がある」に対応する LLF 版を作ります。

### 2-1. canonical でない step から “より良い job” を取り出す

EDF 版の

* `canonical_non_edf_step_has_other_min_or_better_eligible_job`

に対応する LLF 版を作ります。

おすすめの形はこれです。

```coq
Lemma canonical_non_llf_step_has_other_min_or_better_eligible_job :
  ...
  ~ matches_choose_llf_at_with jobs candidates_of sched t ->
  sched t 0 = Some j ->
  J j ->
  exists j',
    In j' (candidates_of jobs 1 sched t) /\
    eligible jobs 1 sched j' t /\
    (laxity jobs 1 sched j' t <= laxity jobs 1 sched j t)%Z /\
    choose_llf jobs 1 sched t (candidates_of jobs 1 sched t) = Some j'.
```

さらに、tie と strict improvement を分ける補題もあると良いです。

* strict case: `laxity j' t < laxity j t`
* tie case: `laxity j' t = laxity j t`

### 2-2. canonical LLF step の否定補題

canonical LLF step なら、「strict に小さい laxity の eligible job は存在しない」を証明します。

これは repair の正当性を使う前に、局所的な priority violation を除去するための基本補題になります。

---

## Phase 3. laxity の時間発展を repair 用に強化する

ここは既に基礎補題がありますが、repair に足りる形まで強化が必要です。

現状の `ScheduleFacts.v` には、

* 実行すれば laxity 保存
* 実行しなければ laxity が 1 減る

が入っています。
これは非常に良いです。

次に必要なのは、**swap の前後で、対象 2 job の laxity / service がどう変わるか**です。

### 3-1. swap 後の remaining_cost / laxity 比較補題

`ScheduleTransform.v` には EDF 用の交換補題が多数ありますが、その多くは

* `deadline(j') <= deadline(j)`

という deadline 順序で組まれています。

LLF ではここを、

* `laxity(j', t) <= laxity(j, t)`

に置き換えたいです。

ただし注意点として、laxity は `t` 時点の値であり、その後 `t'` では変わります。
なので、必要なのは単なる置換ではなく、例えば次のような補題です。

* `j'` を `t` で前倒しし、`j` を `t'` に後ろ倒ししても、`j'` の deadline miss は起きない
* 適切な条件の下で、`j` も新たな miss を起こさない
* 他 job の service / miss は保たれる

この層はおそらく **LLF 用に新設**した方がよいです。
EDF の `swap_at_preserves_feasible_schedule_on_le` をそのまま一般化するより、LLF 用に独立補題を作る方が安全です。

### 3-2. 交換で必要な十分条件を明示する

LLF repair では、前に出す job `j'` が時刻 `t` でより小さい laxity を持つことが鍵です。
したがって repair lemma の仮定として、少なくとも次を明示するとよいです。

* `eligible jobs 1 sched j' t`
* `sched t 0 = Some j \/ sched t 0 = None`
* `laxity jobs 1 sched j' t <= laxity jobs 1 sched j t`
* feasible witness なので `j'` は将来 deadline 前にどこかで走っている

特に最後は、既にある

* `eligible_feasible_implies_runs_later_before_deadline`

をそのまま使えます。

---

## Phase 4. LLF repair lemma を作る

ここが LLF optimality の核心です。

EDF 版の `repair_non_canonical_at` に対応する LLF 版を作ります。

### 4-1. statement の形

ほぼ EDF と同じ形でよいです。

* 非 canonical at `t`
* valid
* feasible
* `J` only
* single CPU only

から、

* `sched'`
* valid preserved
* feasible preserved
* `J` only preserved
* single CPU only preserved
* `agrees_before sched sched' t`
* `matches_choose_llf_at_with jobs candidates_of sched' t`

を返す。

### 4-2. ここで EDF と違う点

EDF 版では `swap_at` の feasibility preservation が、deadline 順序補題でかなり直接通っています。
LLF 版ではそこが一段重いです。

したがってこの Phase は、さらに 2 段に分けるのが現実的です。

#### 4-2-a. tie-only repair

まずは `laxity(j',t) = laxity(j,t)` の場合だけ repair を作る。
これは最も簡単です。

#### 4-2-b. strict better repair

次に `laxity(j',t) < laxity(j,t)` の場合の交換補題を作る。
ここで本格的な LLF 特有の argument が必要になります。

この順番にすると、canonicalization の骨格を早めに回せます。

---

## Phase 5. LLF normalization to canonical

repair lemma ができたら、EDF 版の `edf_normalize_to_canonical` をほぼ写経できます。

作るべきものは

* `llf_normalize_to_canonical`

です。

役割は EDF 版と同じで、

* feasible witness schedule を
* horizon `H` まで canonical LLF に正規化し
* validity / feasibility / J-only / single-CPU-only を保つ

ことです。

ここで使う horizon も EDF 版と同じく `deadline_horizon jobs enumJ` でよいです。
finite job set 版ならこれで十分です。

---

## Phase 6. truncation と bridge

この段階は EDF 版の再利用率が高いです。

### 6-1. truncation 後も canonical

EDF 版の

* `trunc_sched_canonical`

の LLF 版を作る。

### 6-2. canonical + idle から scheduler_rel

EDF 版の

* `canonical_and_idle_implies_scheduler_rel`

の LLF 版を作る。

ただしここは、すでに `llf_bundle` と `single_cpu_algorithm_schedule` があるので、
実際には **generic bridge に寄せて共通化する余地**があります。

つまり、

* 「canonical choose-X に一致」
* 「horizon 後は idle」

から

* `scheduler_rel (single_cpu_algorithm_schedule alg candidates_of) ...`

を導く共通補題

を先に一般化してしまうと、EDF / LLF で共有できます。

これはかなりおすすめです。
LLF optimality を入れる前に、**EDFOptimality の終盤 2 補題を generic 化**すると、LLF 側のコード量がかなり減ります。

---

## Phase 7. 最終定理 `llf_optimality_on_finite_jobs`

最後に EDF とほぼ同じ 6 ステップで閉じます。

1. feasible witness を取り出す
2. `mk_single_cpu` + `J_restrict`
3. `llf_normalize_to_canonical`
4. `trunc_sched`
5. bridge で `scheduler_rel`
6. `schedulable_by_on` を得る

つまり、最終的には EDF 版 theorem の LLF 版をほぼそのまま書けます。
本質的に新しいのは、**Phase 3–4 の LLF repair 層**です。

---

# 実際の着手順

いまの実装状況を踏まえると、最も良い順番はこれです。

## Step A

`UniPolicies/LLFLemmas.v` を作る。

まず入れるものは

* `choose_llf_agrees_before`
* `matches_choose_llf_at_with`
* `matches_choose_llf_before`
* `is_llf_canonical_at_b`
* true/false iff
* canonical LLF step の局所補題

です。

## Step B

`ScheduleLemmas` に、repair で使う一般補題を足す。

特に

* `service_agrees_before`
* `remaining_cost_agrees_before`
* `laxity_agrees_before`

がまだ明示されていないなら追加する価値があります。

## Step C

`UniPolicies/LLFTransform.v` を新設する。

ここに

* first violation witness
* tie repair
* strict laxity repair
* repair preserves validity / feasibility

を入れます。

EDF の `EDFTransform.v` と対応させるのがよいです。

## Step D

`UniPolicies/LLFOptimality.v` を作る。

ここで

* normalize
* trunc canonical
* canonical + idle -> scheduler_rel
* `llf_optimality_on_finite_jobs`

をまとめます。

---

# 先にやると得なリファクタリング

この LLF optimality に入る前に、EDF から 2 つだけ共通化するとかなり楽です。

### 1. canonical + idle -> scheduler_rel の generic 化

EDF 固有でなく、

* 任意の `GenericSchedulingAlgorithm`
* 任意の `candidates_of`

について書けるはずです。

### 2. `choose_*_agrees_before` の共通パターン整理

`MetricChooser.v` にすでに基盤があるので、

* EDF
* LLF

両方で使う小さな補題群を揃えると見通しが良くなります。

---

# 結論

最新版を踏まえると、LLF optimality へのロードマップはこう要約できます。

**すでに完了している層**

* `remaining_cost`
* `laxity : Z`
* LLF chooser
* min-laxity 補題
* LLF scheduler spec / bundle

**次に必要な層**

* LLF canonicalization 補題
* prefix agreement 下での LLF chooser 不変性
* non-canonical LLF step の局所違反抽出
* laxity ベースの repair / swap 補題
* LLF normalization
* generic bridge 再利用
* finite-job optimality theorem

言い換えると、次の本命タスクは
**`UniPolicies/LLFLemmas.v` と `UniPolicies/LLFTransform.v` を追加し、EDF optimality の骨格を LLF に持ち込める状態にすること**です。
