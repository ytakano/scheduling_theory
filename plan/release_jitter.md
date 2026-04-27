結論：次のロードマップは **「既存の `TaskModels/Jitter/*` を、有限 witness ベースから、無限時間 EDF 解析・抽出 checker まで昇格する」** こと。
ただし一点だけ釘を刺す。**Release Jitter を `Schedule` や `Task` 本体に混ぜてはいけない**。現在の方針どおり、jitter は task-generation layer のパラメータとして扱うべき。将来 LLF にも使うなら、なおさら policy 非依存の層に閉じ込める。まったく、ここを雑にすると後で証明全体が濁る。

なお、zip 内の構造は確認した。ただし、この環境には `rocq/coqc` が無かったのでコンパイル確認は未実施。

---

## 0. 現状整理

現在の実装はかなり良い位置にいる。

既にあるもの：

* 有限周期タスク集合
* リリースオフセット
* 無限時間 EDF schedulability 解析
* periodic EDF の extraction / certificate / final checker 系
* jittered periodic の初期層
* finite-horizon の jittered EDF / LLF wrapper
* `JitteredPeriodicDemandBound.v` などの demand 系の初期部品

特に既存の jitter モデルは、おおむね次の意味になっている。

```coq
nominal_release <= actual_release <= nominal_release + jitter
```

つまり **早出しではなく、最大 `J` だけ遅延する release jitter** だ。一般的にも release jitter は「リリース時刻が最大量だけ遅れる・揺れる」モデルとして扱われることが多い。([ヨーク大学][1])

さらに現在の `valid_job_of_task` により、

```coq
job_abs_deadline = job_release + task_relative_deadline
```

なので、**deadline は actual release 基準**になっている。これは重要。nominal release 基準の deadline jitter モデルとは別物だから、後で混ぜないこと。

---

## 1. 基本方針

Release Jitter 拡張の中心方針はこれ。

```text
Task / Job / Schedule は変更しない
  ↓
JitteredPeriodicTasks で actual release の許容範囲を定義する
  ↓
JitteredPeriodicCodec / Enumeration / Candidates を作る
  ↓
jitter-aware window DBF を定義する
  ↓
EDF infinite bridge に接続する
  ↓
Extraction / certificate checker へ落とす
  ↓
同じ基盤を LLF infinite bridge に再利用する
```

この方向は、プロジェクト全体を reusable framework として育てる方針にも合っている。既存整理でも、個別定理だけでなく、`Schedule / SchedulingAlgorithm / Scheduler / Analysis / Refinement` の層構造を作ることが研究上の強みとして位置づけられている。

---

# Roadmap

## Phase J0: Jitter semantics の仕様を固定する

まず、現在の実装が採用している jitter semantics を明文化する。

### 採用するモデル

```text
nominal_release(τ, k) = offset τ + k * period τ

actual_release(τ, k) ∈
  [nominal_release(τ, k),
   nominal_release(τ, k) + jitter τ]

absolute_deadline =
  actual_release + relative_deadline
```

このモデルでは、release jitter は **job の生成時刻を遅らせる**。
`Task` には入れず、`TaskId -> Time` 型の `jitter` 関数として持つのがよい。

### 追加・強化するファイル

```text
theories/TaskModels/Jitter/ReleaseJitter.v
theories/TaskModels/Jitter/JitteredPeriodicTasks.v
```

### 追加すべき lemma

```coq
within_jitter_refl_zero
within_jitter_actual_ge_nominal
within_jitter_actual_le_nominal_plus_jitter

generated_by_jittered_periodic_release_lb
generated_by_jittered_periodic_release_ub
generated_by_jittered_periodic_deadline_eq
generated_by_jittered_periodic_cost_le
generated_by_jittered_periodic_zero_jitter_iff_periodic
```

最後の zero-jitter lemma は重要。既存の periodic pipeline と互換性を取るための橋になる。

```coq
jitter τ = 0 ->
generated_by_jittered_periodic_task tasks offset jitter jobs j <->
generated_by_periodic_task tasks offset jobs j.
```

---

## Phase J1: JitteredPeriodicCodec と無限 jobset を作る

現在の periodic infinite EDF pipeline は codec に依存している。
jittered periodic でも同じ形が必要。

### 追加ファイル

```text
theories/TaskModels/Jitter/JitteredPeriodicCodec.v
theories/TaskModels/Jitter/JitteredPeriodicInfiniteJobset.v
theories/TaskModels/Jitter/JitteredPeriodicPrefixCoherence.v
```

### 目的

`(TaskId, index)` と `JobId` の対応を与える。

```coq
Record JitteredPeriodicCodec := {
  jp_job_of : TaskId -> nat -> JobId;

  jp_codec_sound :
    forall τ k,
      generated_by_jittered_periodic_task
        tasks offset jitter jobs (jp_job_of τ k);

  jp_codec_complete :
    forall j,
      generated_by_jittered_periodic_task tasks offset jitter jobs j ->
      exists τ k, j = jp_job_of τ k;

  jp_codec_inj :
    forall τ1 k1 τ2 k2,
      jp_job_of τ1 k1 = jp_job_of τ2 k2 ->
      τ1 = τ2 /\ k1 = k2;
}.
```

ただし、ここに注意。

periodic では `(τ,k)` から release が完全に決まる。
jittered periodic では `(τ,k)` だけでは actual release は決まらない。

だから codec は **job identity の codec** であって、release を再構成する codec ではない。
actual release は `jobs : JobId -> Job` から読む。ここを勘違いすると、まあ、きれいに破綻する。

### prefix coherence

EDF の生成 scheduler では、時刻 `t` で候補集合を作る必要がある。

```coq
jittered_periodic_candidates_before t :=
  enum jobs such that job_release j < S t.
```

periodic 版と同様に、次を証明する。

```coq
jittered_periodic_candidates_before_sound
jittered_periodic_candidates_before_complete
jittered_periodic_candidates_before_nodup
jittered_periodic_candidates_prefix_monotone
```

---

## Phase J2: Jitter-aware window DBF を定義する

ここが一番危ない。
現在の `JitteredPeriodicDemandBound.v` にあるような「deadline ≤ H なら periodic DBF に落とす」方向は、初期区間 `[0,H]` には使えるが、**任意 window `[t1,t2]` の EDF 解析には足りない**。

なぜか。

nominal release が `t1` より前でも、jitter によって actual release が `t1` 以降に入ることがある。

例：

```text
nominal release = 0
jitter = 5
actual release = 5
relative deadline = 10

window = [5,15]
```

この job は window 内に入る。
しかし nominal release を基準に

```text
release >= 5
```

と判定すると見逃す。

したがって **jittered window DBF** を新しく定義する必要がある。EDF の processor-demand 系の解析は、sporadic や zero-offset periodic では exact、arbitrary offset では十分条件として使われる古典的基盤なので、ここを正しく切る必要がある。([York Computer Science][2])

### 追加ファイル

```text
theories/TaskModels/Jitter/JitteredPeriodicWindowDemandBound.v
```

### 中核定義

Coq 風にはこう。

```coq
Definition jittered_index_may_be_in_window
  (τ : TaskId) (k : nat) (t1 t2 : Time) : Prop :=
  exists δ,
    δ <= jitter τ /\
    let r := expected_release tasks offset τ k + δ in
    t1 <= r /\
    r + task_relative_deadline (tasks τ) <= t2.
```

これを boolean 化する。

```coq
Definition jittered_index_may_be_in_window_b
  (τ : TaskId) (k : nat) (t1 t2 : Time) : bool := ...
```

実装上は `exists δ` を探索しなくてもよい。
区間制約を整理すればよい。

```text
actual release r must satisfy:

r ∈ [nominal, nominal + J]
r ∈ [t1, t2 - D]
```

したがって、交差が非空ならよい。

```text
max nominal t1 <= min (nominal + J) (t2 - D)
```

この形にすれば executable DBF にできる。

### DBF 定義

```coq
Definition jittered_periodic_dbf_window
  (τ : TaskId) (t1 t2 : Time) : nat :=
  sum over k such that
    jittered_index_may_be_in_window τ k t1 t2
  of task_cost (tasks τ).

Definition taskset_jittered_periodic_dbf_window
  (ts : list TaskId) (t1 t2 : Time) : nat :=
  sum over τ in ts of jittered_periodic_dbf_window τ t1 t2.
```

### 証明すべき性質

```coq
jittered_window_dbf_bounds_actual_workload :
  actual jobs with
    t1 <= job_release j /\
    job_abs_deadline j <= t2
  have total cost <=
    taskset_jittered_periodic_dbf_window ts t1 t2.

jittered_window_dbf_zero_jitter_eq_periodic_window_dbf :
  all jitter τ = 0 ->
  taskset_jittered_periodic_dbf_window ts t1 t2 =
  taskset_periodic_dbf_window ts t1 t2.

jittered_window_dbf_monotone_right
jittered_window_dbf_monotone_left
jittered_window_dbf_perm
jittered_window_dbf_app
```

### 保守的な scalar helper

実装しやすい十分条件として、これも用意するとよい。

```coq
jittered_dbf_len τ Δ :=
  periodic_dbf τ (Δ + jitter τ)
```

つまり window 長 `Δ` に jitter 分だけ横幅を足す。
これは exact ではなく conservative でよい。まず checker を通すには使える。

---

## Phase J3: EDF の有限 horizon bridge を jitter-window DBF に接続する

次は EDF 側。
既に finite-horizon の `JitteredPeriodicEDFBridge.v` はあるが、これは witness ベースの有限 jobset optimality lift に近い。
無限時間解析へ進めるには、window DBF と EDF finite feasibility を接続する橋が必要。

### 追加・拡張ファイル

```text
theories/TaskModels/Jitter/JitteredPeriodicEDFWindowBridge.v
theories/TaskModels/Jitter/JitteredPeriodicEDFBridge.v
```

### 推奨設計

ここは EDF 専用に作りすぎない。
将来 LLF にも使うなら、以下のような policy 非依存 record を先に作るのがよい。

```coq
Record WindowDemandModel := {
  model_jobset : JobId -> Prop;
  model_candidates_before : Time -> list JobId;
  model_window_dbf : Time -> Time -> nat;

  model_window_dbf_sound :
    forall t1 t2,
      workload_of_jobs_deadline_between
        model_jobset t1 t2 <= model_window_dbf t1 t2;
}.
```

EDF はこの `WindowDemandModel` を使って theorem を立てる。
LLF は同じ `WindowDemandModel` を再利用する。これで重複を避ける。

### EDF theorem の形

```coq
Theorem jittered_periodic_edf_schedulable_on_finite_horizon_by_window_dbf :
  forall H,
    valid_jittered_periodic_taskset tasks offset jitter jobs ->
    taskset_jittered_periodic_dbf_window ts 0 H <= H ->
    edf_schedulable_on_finite_horizon
      jobs
      (jittered_periodic_candidates_before H).
```

最終的には `[0,H]` だけでなく任意 window にする。

```coq
Theorem jittered_periodic_edf_no_deadline_miss_by_window_dbf :
  (forall t1 t2,
      t1 <= t2 ->
      taskset_jittered_periodic_dbf_window ts t1 t2 <= t2 - t1) ->
  no_deadline_miss_under_generated_edf ...
```

---

## Phase J4: 無限時間 EDF bridge を作る

ここで、現在の periodic infinite EDF pipeline に並ぶ jittered 版を作る。

### 追加ファイル

```text
theories/TaskModels/Jitter/JitteredPeriodicEDFPrefixCoherence.v
theories/TaskModels/Jitter/JitteredPeriodicEDFInfiniteBridge.v
theories/TaskModels/Jitter/JitteredPeriodicEDFAnalysisEntryPoints.v
```

### 目標 theorem

```coq
Theorem jittered_periodic_edf_schedulable_by_window_dbf_on :
  valid_jittered_periodic_taskset tasks offset jitter jobs ->
  JitteredPeriodicCodec tasks offset jitter jobs ->
  (forall t1 t2,
      t1 <= t2 ->
      taskset_jittered_periodic_dbf_window
        tasks offset jitter ts t1 t2 <= t2 - t1) ->
  busy_prefix_or_no_carry_in_condition ... ->
  schedulable_by_on
    jobs
    (generated_jittered_periodic_edf_schedule
       tasks offset jitter jobs)
    ts
    1.
```

### 重要な注意：hyperperiod transport はそのまま使えない

現在の offset periodic EDF では、hyperperiod による completion transport / checked sidecar が使える。
しかし jittered periodic では、各 job の actual release が自由に揺れるため、

```text
job k と job k + hyperperiod/period の actual release pattern が同じ
```

とは限らない。

つまり、arbitrary jitter では、**生成 schedule の hyperperiod 周期性を勝手に仮定できない**。

ここは二段階に分けるべき。

### Track A: arbitrary jitter 用

hyperperiodic schedule transport に依存しない。
window DBF の全 window 条件から直接 schedulability を出す。

```text
全 window DBF 条件
  + generated EDF prefix coherence
  + busy-prefix/no-carry-in bridge
  -> infinite EDF schedulability
```

最初はこちらを優先。

### Track B: periodic jitter pattern 用

実装上の checker を強くしたければ、別途、jitter pattern が hyperperiod で繰り返すという sidecar を導入する。

```coq
jitter_delta τ (k + hp / period τ) = jitter_delta τ k
```

この条件がある場合だけ、既存の periodic completion transport に近いものを再利用する。

---

## Phase J5: cutoff 付き executable DBF checker を作る

無限個の window をそのまま検査できないので、cutoff が必要。

### 追加ファイル

```text
theories/TaskModels/Jitter/JitteredPeriodicOffsetWindowCutoff.v
theories/TaskModels/Jitter/JitteredPeriodicConcreteAnalysis.v
```

### まずは保守的 cutoff でよい

最初は tight である必要はない。
安全側で十分。

候補：

```text
cutoff =
  max_offset
  + max_jitter
  + max_relative_deadline
  + hyperperiod
```

または、既存 periodic offset cutoff に `max_jitter` を足す。

```coq
jittered_offset_window_cutoff :=
  periodic_offset_window_cutoff + max_jitter.
```

### 証明すべきこと

```coq
jittered_window_dbf_shift_by_hyperperiod :
  taskset_jittered_periodic_dbf_window ts t1 t2 =
  taskset_jittered_periodic_dbf_window ts (t1 + hp) (t2 + hp)
```

ただしこれは **DBF の may-be-in-window bound** に対して成立させる。
actual release sequence の周期性ではなく、nominal release + jitter bound の周期性を使う。

### checker

```coq
Definition jittered_offset_window_dbf_check_by_cutoff
  (ts : list ExtractedJitteredPeriodicTask) : bool := ...
```

counterexample 付きも作る。

```coq
Definition jittered_offset_window_dbf_counterexample
  (ts : list ExtractedJitteredPeriodicTask)
  : option (Time * Time) := ...
```

---

## Phase J6: Extraction-facing task type を追加する

既存の `ExtractedPeriodicTask` を壊す必要はない。
むしろ新 record を作る方が安全。

### 追加ファイル

```text
theories/TaskModels/Jitter/JitteredPeriodicEDFExtractionTypes.v
theories/TaskModels/Jitter/JitteredPeriodicEDFExtractionDecision.v
theories/TaskModels/Jitter/JitteredPeriodicEDFExtractionSoundness.v
theories/TaskModels/Jitter/JitteredPeriodicEDFExtraction.v
```

### record

```coq
Record ExtractedJitteredPeriodicTask := {
  ejp_cost : nat;
  ejp_period : nat;
  ejp_relative_deadline : nat;
  ejp_offset : nat;
  ejp_release_jitter : nat;
}.
```

zero-jitter coercion も作る。

```coq
Definition extracted_periodic_as_jittered
  (t : ExtractedPeriodicTask)
  : ExtractedJitteredPeriodicTask :=
  {| ejp_cost := ep_cost t;
     ejp_period := ep_period t;
     ejp_relative_deadline := ep_relative_deadline t;
     ejp_offset := ep_offset t;
     ejp_release_jitter := 0 |}.
```

### decision procedure

```coq
Definition jittered_periodic_edf_schedulability_decide
  (ts : list ExtractedJitteredPeriodicTask) : bool :=
  jittered_offset_window_dbf_check_by_cutoff ts.
```

### soundness theorem

```coq
Theorem jittered_periodic_edf_schedulability_decide_sound :
  jittered_periodic_edf_schedulability_decide ts = true ->
  forall jobs,
    generated_by_jittered_periodic_taskset ts jobs ->
    schedulable_by_edf jobs.
```

実際には codec / finite generation / candidate coherence / busy-prefix 条件が入るので、最初は theorem を分解しておく。

---

## Phase J7: Certificate / sidecar checker に接続する

periodic EDF には final certificate checker がある。
jittered EDF でも同じことをやりたいが、さっき言ったように hyperperiod transport には注意。

### 追加ファイル

```text
theories/TaskModels/Jitter/JitteredPeriodicEDFCertificate.v
theories/TaskModels/Jitter/JitteredPeriodicEDFCertificateSoundness.v
theories/TaskModels/Jitter/JitteredPeriodicEDFFinalCertificateChecker.v
```

### 2種類の certificate を分ける

#### A. DBF-only certificate

```coq
Record JitteredEDFDbfCertificate := {
  jedf_cutoff : Time;
  jedf_checked_windows : list (Time * Time);
  jedf_all_windows_checked : bool;
}.
```

これは arbitrary jitter 用。
release delta の列は不要。

#### B. Patterned-jitter certificate

```coq
Record JitteredEDFPatternCertificate := {
  jedf_delta : TaskId -> nat -> Time;
  jedf_delta_within_jitter :
    forall τ k, jedf_delta τ k <= jitter τ;
  jedf_delta_periodic :
    forall τ k, jedf_delta τ (k + hp / period τ) = jedf_delta τ k;
}.
```

これは completion transport を使いたい場合用。
最初から B をやると重い。A を先に完成させるべき。

---

## Phase J8: LLF への拡張点を先に確保する

将来 LLF も扱うなら、EDF 専用の深い依存を作らないこと。

LLF は policy としては、

```text
laxity = absolute_deadline - current_time - remaining_cost
```

を使う。
Release Jitter は absolute deadline と release availability に影響するが、LLF policy 自体には直接入らない。

つまり LLF 対応で必要なのは、ほぼ次の共有部品。

```text
JitteredPeriodicTasks
JitteredPeriodicCodec
JitteredPeriodicEnumeration
JitteredPeriodicWindowDemandBound
JitteredPeriodicFiniteHorizon
```

EDF と LLF で分けるべきなのは scheduler policy bridge 以降だけ。

### 追加ファイル

```text
theories/TaskModels/Jitter/JitteredPeriodicLLFInfiniteBridge.v
theories/TaskModels/Jitter/JitteredPeriodicLLFAnalysisEntryPoints.v
```

### LLF theorem の形

```coq
Theorem jittered_periodic_llf_schedulable_by_window_dbf_on :
  valid_jittered_periodic_taskset tasks offset jitter jobs ->
  JitteredPeriodicCodec tasks offset jitter jobs ->
  (forall t1 t2,
      t1 <= t2 ->
      taskset_jittered_periodic_dbf_window
        tasks offset jitter ts t1 t2 <= t2 - t1) ->
  busy_prefix_or_no_carry_in_condition ... ->
  schedulable_by_on
    jobs
    (generated_jittered_periodic_llf_schedule
       tasks offset jitter jobs)
    ts
    1.
```

内部構成としては、

```text
window DBF
  -> finite feasibility
  -> LLF finite optimality / LLF bridge
  -> infinite LLF
```

の流れが自然。

既に finite-horizon の jittered LLF wrapper があるなら、それを infinite bridge に持ち上げるだけで済むように設計する。

---

## Phase J9: examples / tutorials / regression を追加する

証明だけでなく、使える例を増やす。

### 追加例

```text
theories/Examples/JitteredPeriodicEDFExamples.v
theories/Examples/JitteredPeriodicInfiniteEDFExamples.v
theories/Examples/JitteredPeriodicOffsetJitterDBFExamples.v
theories/Examples/JitteredPeriodicZeroJitterCompatExamples.v
theories/Examples/JitteredPeriodicLLFExamples.v
```

### tutorial

```text
theories/Tutorials/JitteredEDFInfiniteSchedulability.v
theories/Tutorials/JitteredLLFInfiniteSchedulability.v
```

### regression test

最低限、次を確認する。

```text
1. jitter = 0 で既存 periodic EDF checker と一致する
2. offset ≠ 0, jitter = 0 で offset periodic に一致する
3. offset ≠ 0, jitter > 0 の DBF checker が動く
4. EDF finite wrapper が既存 example を通す
5. LLF finite wrapper が同じ jittered jobset で通る
```

---

# 実装順序

優先順位はこう。

## PR 1: Semantics / Codec / Enumeration

```text
ReleaseJitter.v 強化
JitteredPeriodicTasks.v 強化
JitteredPeriodicCodec.v 追加
JitteredPeriodicInfiniteJobset.v 追加
JitteredPeriodicPrefixCoherence.v 追加
```

成果物：

```coq
generated_by_jittered_periodic_zero_jitter_iff_periodic
jittered_periodic_candidates_before_sound
jittered_periodic_candidates_before_complete
```

---

## PR 2: Jittered window DBF

```text
JitteredPeriodicWindowDemandBound.v 追加
```

成果物：

```coq
jittered_window_dbf_bounds_actual_workload
jittered_window_dbf_zero_jitter_eq_periodic_window_dbf
```

ここが最重要。ここを雑にすると全部嘘になる。理解してる？

---

## PR 3: EDF finite / infinite bridge

```text
JitteredPeriodicEDFWindowBridge.v
JitteredPeriodicEDFInfiniteBridge.v
JitteredPeriodicEDFAnalysisEntryPoints.v
```

成果物：

```coq
jittered_periodic_edf_schedulable_by_window_dbf_on
```

---

## PR 4: cutoff checker

```text
JitteredPeriodicOffsetWindowCutoff.v
JitteredPeriodicConcreteAnalysis.v
```

成果物：

```coq
jittered_offset_window_dbf_check_by_cutoff_sound
```

---

## PR 5: Extraction

```text
JitteredPeriodicEDFExtractionTypes.v
JitteredPeriodicEDFExtractionDecision.v
JitteredPeriodicEDFExtractionSoundness.v
JitteredPeriodicEDFExtraction.v
```

成果物：

```text
extracted Haskell checker
```

将来的に実 OS trace から scheduler model / checker に接続するなら、こうした checker 抽出はかなり相性がよい。既存整理でも、trace から scheduler model を照合し、Rocq checker と theorem に接続する方向が提案されている。

---

## PR 6: LLF infinite bridge

```text
JitteredPeriodicLLFInfiniteBridge.v
JitteredPeriodicLLFAnalysisEntryPoints.v
```

成果物：

```coq
jittered_periodic_llf_schedulable_by_window_dbf_on
```

EDF で作った `JitteredPeriodicWindowDemandBound` と codec をそのまま使う。

---

# 注意すべき落とし穴

## 1. `Task` に jitter を入れない

`Task` は cost / period / relative deadline のままでよい。
offset と同じく、jitter も外部関数で渡す。

```coq
offset : TaskId -> Time
jitter : TaskId -> Time
```

これにより、同じ taskset に対して複数の release environment を比較できる。

---

## 2. Jittered DBF を periodic DBF で代用しない

`[0,H]` の deadline count なら、jittered job の deadline が遅れるため periodic bound に落ちる場合がある。
だが arbitrary window では違う。

特に infinite EDF では window DBF が中核になる。
ここは専用定義が必要。

---

## 3. `sporadic_separation_on` を jitter だけから導かない

jitter があると、連続 job の actual release 間隔は短くなりうる。

```text
job k     : nominal = 0, actual = J
job k + 1 : nominal = P, actual = P
```

このとき間隔は

```text
P - J
```

になる。
だから `generated_by_jittered_periodic_task -> generated_by_sporadic_task` は、追加の separation 仮定なしには危険。現在の実装が explicit に `sporadic_separation_on` を要求しているのは正しい。

---

## 4. Hyperperiod transport を arbitrary jitter に使わない

periodic release なら hyperperiod shift が自然に効く。
jittered release では actual release pattern が周期的とは限らない。

DBF bound は周期化できても、生成 schedule 自体の transport は別問題。
ここを混同しない。

---

## 5. Deadline semantics を分ける

現在は、

```text
deadline = actual_release + relative_deadline
```

である。

もし将来、

```text
deadline = nominal_release + relative_deadline
```

を扱いたいなら、別モデルにする。

```text
JitteredPeriodicTasks.v
NominalDeadlineJitteredPeriodicTasks.v
```

のように分けるのがよい。混ぜると theorem の仮定が読めなくなる。

---

# 最終的な到達点

最終的には、次の theorem を公開 API にするのがよい。

```coq
Theorem extracted_jittered_periodic_edf_schedulability_sound :
  jittered_periodic_edf_schedulability_decide ts = true ->
  forall jobs,
    generated_by_extracted_jittered_periodic_taskset ts jobs ->
    schedulable_by_edf jobs.
```

そして LLF 版：

```coq
Theorem extracted_jittered_periodic_llf_schedulability_sound :
  jittered_periodic_llf_schedulability_decide ts = true ->
  forall jobs,
    generated_by_extracted_jittered_periodic_taskset ts jobs ->
    schedulable_by_llf jobs.
```

ただし実装順としては、**EDF を先に完成**させる。
LLF は policy bridge の問題であって、jitter semantics / DBF / codec は EDF と共通化する。これが一番きれいで、将来の multicore/global EDF/LLF にも伸ばしやすい。

要するに次の一手は、**`JitteredPeriodicWindowDemandBound.v` を中核にして、jittered periodic を infinite EDF pipeline に接続すること**。
そこさえ正しく切れば、LLF はかなり自然に乗る。

[1]: https://www-users.york.ac.uk/~rd17/papers/SingleProcessorSchedulingReview.pdf?utm_source=chatgpt.com "A Review of Fixed Priority and EDF Scheduling for Hard ..."
[2]: https://www.cs.york.ac.uk/rts/static/papers/R%3ABaruah%3A2006.pdf?utm_source=chatgpt.com "Sustainable Scheduling Analysis"
