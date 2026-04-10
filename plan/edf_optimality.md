ロードマップ上の **Phase 6 は途中まで完了** しており、次の本丸は

* **schedule transform / swap 補題**
* **finite horizon 上の EDF 正規化**
* **EDF 最適性定理本体**

です。

特に重要なのは、今の実装ではすでに **tie を考慮した strict violation (`<`)** と、**canonical choose_edf との一致** が分離されていることです。これは良い設計です。
したがって、次の証明は **`matches_choose_edf_at_with` を直接追うより、まず `respects_edf_priority_at_on` を中間目標にする** のが自然です。

---

## 次のタスク plan

### 0. まず主定理の形を固定する

最初に、最終到達点を 2 段階に分けるのがよいです。

**段階A: 抽象EDF最適性**

```coq
forall J jobs sched_edf,
  valid_schedule jobs 1 sched_edf ->
  (forall t, respects_edf_priority_at_on J jobs sched_edf t) ->
  feasible_on J jobs 1 ->
  feasible_schedule_on J jobs 1 sched_edf.
```

**段階B: canonical EDF への具体化**

```coq
forall J candidates_of
       (cand_spec : CandidateSourceSpec J candidates_of)
       jobs,
  feasible_on J jobs 1 ->
  schedulable_by_on J (edf_scheduler candidates_of) jobs 1.
```

この順にすると、**tie の問題**と**canonical scheduler の問題**を分離できます。

---

### 1. `EDFLemmas.v` に「交換相手が後ろに存在する」補題を追加する

今の `edf_violation_exposes_exchange_pair` では、
「時刻 `t` に、今走っている job より deadline が早い eligible job `j'` がある」
ところまでは出ています。

次に必要なのは、

> feasible な witness schedule では、その `j'` は将来どこかで実行される

という補題です。

狙う形は例えば次です。

```coq
Lemma eligible_feasible_implies_runs_later_before_deadline :
  forall J jobs sched j t,
    J j ->
    valid_schedule jobs 1 sched ->
    feasible_schedule_on J jobs 1 sched ->
    eligible jobs 1 sched j t ->
    exists t',
      t <= t' /\
      t' < job_abs_deadline (jobs j) /\
      sched t' 0 = Some j.
```

priority violation の場面では `sched t 0 = Some j_run` かつ `j <> j_run` なので、実際には `t < t'` まで出せます。
この補題が、swap の「交換相手の後ろの実行スロット」を与えます。

---

### 2. `ScheduleTransform.v` を追加して swap を独立させる

ここは `EDFLemmas.v` に詰め込まず、別ファイル化した方が見通しが良いです。

推奨ファイル:

* `theories/UniPolicies/ScheduleTransform.v`
* その後 `EDFOptimality.v`

まず single-CPU 用に、CPU 0 の二時刻を交換する変換を入れます。

```coq
Definition swap_cpu0 (sched : Schedule) (t1 t2 : Time) : Schedule := ...
```

次に必要な補題はこの順です。

1. **prefix 保存**

   * `t < t1` では schedule 不変
   * `agrees_before sched (swap_cpu0 sched t1 t2) t1`

2. **service への影響**

   * swap 区間外では影響なし
   * `H <= t1` なら `service_job ... H` 不変
   * `H >= t2` なら各 job の `service_job ... H` は保存

3. **局所交換の効果**

   * `t1` で late job を外し、`t2` で early job を外したとき、
     `t1` 以前の prefix は壊さず、`t1` の選択だけ修正できる

4. **validity 保存**
   ここが核心です。必要条件は大体次です。

   * `sched t1 0 = Some j_late`
   * `sched t2 0 = Some j_early`
   * `eligible jobs 1 sched j_early t1`
   * `t1 < t2`
   * single CPU
   * 元の schedule は valid

   これで `swap_cpu0 sched t1 t2` も valid であることを示す

5. **feasibility 保存**
   `job_abs_deadline (jobs j_early) < job_abs_deadline (jobs j_late)` のもとで、
   swap により deadline miss が悪化しないことを示す

---

### 3. 一歩の修正補題を作る

EDF 最適性本体の前に、まず 1 step repair を作るのがよいです。

```coq
Lemma repair_first_priority_violation :
  forall J jobs sched t,
    valid_schedule jobs 1 sched ->
    feasible_schedule_on J jobs 1 sched ->
    (* t が最初の strict EDF priority violation *)
    ...
    exists sched',
      valid_schedule jobs 1 sched' /\
      feasible_schedule_on J jobs 1 sched' /\
      agrees_before sched sched' t /\
      respects_edf_priority_at_on J jobs sched' t.
```

ここで重要なのは **「canonical choose_edf と一致」ではなく「strict earlier deadline job を無視しない」** を修正目標にすることです。
equal deadline のジョブはこの段階では区別しない方が証明が素直です。

---

### 4. finite horizon 上の正規化補題を証明する

次に、上の 1 step repair を帰納で回します。

```coq
Definition respects_edf_priority_before_on ... H := ...

Lemma normalize_to_edf_priority_before :
  forall J jobs sched H,
    valid_schedule jobs 1 sched ->
    feasible_schedule_on J jobs 1 sched ->
    exists sched',
      valid_schedule jobs 1 sched' /\
      feasible_schedule_on J jobs 1 sched' /\
      respects_edf_priority_before_on J jobs sched' H.
```

ここでは `H` までの有限 prefix だけを正規化対象にします。
finite horizon にしておくと、「最初の violation 時刻」を使う帰納が回しやすいです。

---

### 5. 抽象EDF最適性を証明する

そのあとで、priority-respecting EDF schedule の feasible 性を出します。

証明の流れは次です。

* 仮に EDF-priority schedule `sched_edf` がある job `j` の deadline を初めて落とすとする
* `d = job_abs_deadline (jobs j)` とする
* feasible witness schedule を `H = d` まで EDF-priority に正規化する
* すると `sched_edf` と比較して、`d` までに必要な service を失えない
* よって `j` が `d` で未完了になるのは矛盾

ここで `service_between` と prefix 補題が活きます。
今の `EDFLemmas.v` の Section 1–3 はこのための良い土台になっています。

---

### 6. 最後に canonical `edf_scheduler` に接続する

ここが実装上の最後の関門です。

現状の `edf_scheduler` は **relation** であり、一般の jobs に対して
「その relation を満たす schedule が存在する」
という補題はまだありません。
例では hand-written schedule を witness にしていましたが、一般定理ではこれでは足りません。

なので最後にどちらかが必要です。

#### 方針A: 先に schedule-parametric 定理を完成させる

つまり、

* `scheduler_rel (edf_scheduler candidates_of) jobs 1 sched`
* `valid_schedule jobs 1 sched`

なら feasible である、という形を先に証明する

そのあとで existence を別タスクにする

#### 方針B: canonical EDF schedule を再帰的に構成する

`CandidateSourceSpec.candidates_prefix_extensional` を使って、
時刻帰納で EDF schedule を直接定義し、bridge relation を満たすことを示す

最終的に `schedulable_by_on` まで出したいなら、**B が必要**になります。
ただし、証明の重心としては **A を先に完成** した方が安全です。

---

## いちばん自然な実装順

実作業の順番としては、これが一番きれいです。

1. `EDFLemmas.v`

   * future execution lemma
   * strict violation repair に必要な補題の追加

2. `UniPolicies/ScheduleTransform.v`

   * `swap_cpu0`
   * service 保存
   * valid 保存
   * feasibility 保存

3. `UniPolicies/EDFOptimality.v`

   * one-step repair
   * finite-horizon normalization
   * abstract EDF optimality

4. 余力があれば

   * canonical EDF schedule の existence/construction
   * `schedulable_by_on J (edf_scheduler candidates_of) jobs 1`
