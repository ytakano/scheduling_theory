結論から言うと、**非ゼロオフセット対応は、既存の periodic core を活かして、extraction-facing 層と final checker の zero-offset 固定を外す作業**になる。
つまり、`PeriodicTasks.v` から下を作り直す必要はない。そこを作り直そうとしたら、まあ、余計な破壊活動ね。

実ソースを確認した結果、現状はこう。

```text
すでに offset-aware:
- PeriodicTasks.v
- PeriodicFiniteHorizon.v
- PeriodicInfinite.v
- PeriodicCodec.v
- PeriodicEnumeration.v
- PeriodicWindowDemandBound.v
- PeriodicConcreteAnalysis.v の有限 window-DBF 部分
- PeriodicEDFInfiniteBridge.v の window-DBF API
- PeriodicLLFInfiniteBridge.v の window-DBF API

まだ zero-offset 固定:
- PeriodicEDFExtractionTypes.v
- PeriodicEDFExtractionDecision.v
- PeriodicEDFExtractionSoundness.v
- PeriodicEDFFinalCertificateChecker.v
- PeriodicEDFCheckedSchedulabilityBridge.v
- Haskell extraction / CSV script
```

特に重要なのは、`PeriodicTasks.v` がすでに：

```coq
expected_release tasks offset τ k =
  offset τ + k * task_period (tasks τ)
```

という形になっていること。
だから offset は **Task レコードに入れない**。既存設計どおり、`TaskId -> Time` の外部関数として扱うのが正しい。Jitter 側も `tasks offset jitter jobs` という形なので、ここを崩すと後で面倒になる。

---

# 実装方針

おすすめは二段階。

```text
Stage 1:
  非ゼロオフセット入力を受け付ける。
  ただし schedulability 判定は offset-insensitive な classical DBF で行う。
  これは保守的だが安全で、実装・証明リスクが低い。

Stage 2:
  offset-aware window-DBF checker を追加する。
  オフセットによる需要分散を実際に利用できるようにする。
```

最初から Stage 2 に突っ込むのは少し欲張り。
非ゼロオフセット対応そのものと、offset-aware exact/window 解析を分けるべき。

---

# Stage 1: 非ゼロオフセット入力対応・保守的 DBF 判定

## 1. `ExtractedPeriodicTask` に offset を追加する

変更対象：

```text
theories/TaskModels/Periodic/PeriodicEDFExtractionTypes.v
```

現状：

```coq
Record ExtractedPeriodicTask : Type := mkExtractedPeriodicTask {
  extracted_task_cost : nat;
  extracted_task_period : nat;
  extracted_task_relative_deadline : nat
}.
```

これをこうする。

```coq
Record ExtractedPeriodicTask : Type := mkExtractedPeriodicTask {
  extracted_task_cost : nat;
  extracted_task_period : nat;
  extracted_task_relative_deadline : nat;
  extracted_task_offset : nat
}.
```

そして offset accessor を追加。

```coq
Definition offset_of_extracted_list
    (ts : list ExtractedPeriodicTask) : TaskId -> Time :=
  fun τ =>
    extracted_task_offset
      (nth τ ts default_extracted_periodic_task).
```

既存の zero-offset 互換用に、これも置く。

```coq
Definition zero_offset_extracted_periodic_task
    (c p d : nat) : ExtractedPeriodicTask :=
  mkExtractedPeriodicTask c p d 0.
```

`default_extracted_periodic_task` は：

```coq
Definition default_extracted_periodic_task : ExtractedPeriodicTask :=
  mkExtractedPeriodicTask 1 1 1 0.
```

にする。

`extracted_task_wf` は offset に positivity を要求しない。

```coq
Definition extracted_task_wf (τ : ExtractedPeriodicTask) : bool :=
  Nat.ltb 0 τ.(extracted_task_cost)
  && Nat.ltb 0 τ.(extracted_task_period)
  && Nat.ltb 0 τ.(extracted_task_relative_deadline).
```

offset は 0 でもよい。ここを `0 < offset` にしたら馬鹿げてるわ。

---

## 2. extraction-facing jobs を offset-aware にする

変更対象：

```text
theories/TaskModels/Periodic/PeriodicEDFExtractionSoundness.v
```

現状は：

```coq
Definition extracted_periodic_jobs (ts : list ExtractedPeriodicTask) : JobId -> Job :=
  canonical_periodic_jobs_from_enumT
    (extracted_periodic_tasks ts)
    (fun _ => 0)
    (enumT_of_extracted_list ts).
```

これを：

```coq
Definition extracted_periodic_offsets
    (ts : list ExtractedPeriodicTask) : TaskId -> Time :=
  offset_of_extracted_list ts.

Definition extracted_periodic_jobs
    (ts : list ExtractedPeriodicTask) : JobId -> Job :=
  canonical_periodic_jobs_from_enumT
    (extracted_periodic_tasks ts)
    (extracted_periodic_offsets ts)
    (enumT_of_extracted_list ts).
```

にする。

同様に codec も `fun _ => 0` ではなく offset accessor を使う。

```coq
Definition extracted_periodic_codec
    (ts : list ExtractedPeriodicTask) :
  PeriodicCodec
    (extracted_task_scope ts)
    (extracted_periodic_tasks ts)
    (extracted_periodic_offsets ts)
    (extracted_periodic_jobs ts).
```

実装は `zero_offset_periodic_codec_of_tasks` ではなく、既存の汎用 builder：

```coq
periodic_codec_of_enumT
```

を使う。

つまり方向はこれ。

```coq
periodic_codec_of_enumT
  (extracted_task_scope ts)
  (extracted_periodic_tasks ts)
  (extracted_periodic_offsets ts)
  (enumT_of_extracted_list ts)
  ...
```

ここで `extracted_zero_offset` は不要になる。
ただし legacy theorem 用には残してもよい。

---

## 3. classical DBF を「任意 offset に対する保守的上界」として一般化する

変更対象：

```text
theories/TaskModels/Periodic/PeriodicClassicDBF.v
```

現状の重要補題は zero-offset 専用：

```coq
zero_offset_window_dbf_le_classical_dbf
zero_offset_taskset_window_dbf_le_classical_dbf
```

これを一般 offset 版に拡張する。

新しくほしい補題：

```coq
Lemma periodic_dbf_window_le_classical_dbf :
  forall tasks offset τ t1 t2,
    0 < task_period (tasks τ) ->
    periodic_dbf_window tasks offset τ t1 t2 <=
    periodic_dbf tasks τ (t2 - t1).
```

taskset 版：

```coq
Lemma taskset_periodic_dbf_window_le_classical_dbf :
  forall tasks offset enumT t1 t2,
    (forall τ, In τ enumT -> 0 < task_period (tasks τ)) ->
    taskset_periodic_dbf_window tasks offset enumT t1 t2 <=
    taskset_periodic_dbf tasks enumT (t2 - t1).
```

これが通ると強い。
なぜなら、非ゼロオフセットでも：

```text
window-DBF(offset-aware) <= classical DBF(length-based)
```

が言えるから。

つまり、既存の scalar DBF checker：

```coq
dbf_test_by_cutoff
```

を、非ゼロオフセット task set に対する **保守的 schedulability test** として使える。

これは offset の効果を活かす解析ではない。だが sound。最初の対応としてはこれが一番堅い。

---

## 4. EDF classical bridge から zero-offset 仮定を外した新 theorem を追加する

変更対象：

```text
theories/TaskModels/Periodic/PeriodicEDFClassicalBridge.v
theories/TaskModels/Periodic/PeriodicEDFInfiniteBridge.v
```

現状は classical DBF wrapper が：

```coq
(forall τ, In τ enumT -> offset τ = 0)
```

を要求している。

Stage 1 では、既存 theorem を壊さずに、新 theorem を足す。

```coq
Theorem periodic_edf_schedulable_by_classical_dbf_any_offset :
  forall T tasks offset enumT jobs
         (codec : PeriodicCodec T tasks offset jobs),
    well_formed_periodic_tasks_on T tasks ->
    (forall j t,
      periodic_jobset T tasks offset jobs j ->
      ~ blocked jobs j t) ->
    NoDup enumT ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    (forall j,
      periodic_jobset T tasks offset jobs j ->
      periodic_edf_busy_prefix_bridge
        T tasks offset jobs (S (job_abs_deadline (jobs j)))
        (generated_periodic_edf_schedule_upto
           T tasks offset jobs
           (S (job_abs_deadline (jobs j))) enumT codec)
        j) ->
    (forall t,
      taskset_periodic_dbf tasks enumT t <= t) ->
    schedulable_by_on
      (periodic_jobset T tasks offset jobs)
      (edf_scheduler
        (periodic_candidates_before T tasks offset jobs enumT codec))
      jobs 1.
```

証明は既存の：

```coq
periodic_edf_schedulable_by_on
```

へ渡すだけ。

必要になるのは：

```coq
forall t1 t2,
  t1 <= t2 ->
  taskset_periodic_dbf_window tasks offset enumT t1 t2 <= t2 - t1
```

で、これはさっきの：

```coq
taskset_periodic_dbf_window_le_classical_dbf
```

と classical DBF assumption から出る。

---

## 5. LLF 側にも同じ any-offset classical wrapper を作る

変更対象：

```text
theories/TaskModels/Periodic/PeriodicLLFAnalysisBridge.v
theories/TaskModels/Periodic/PeriodicLLFInfiniteBridge.v
```

現状 LLF 側には：

```coq
periodic_llf_schedulable_by_classical_dbf_on
```

があるが、zero-offset classical DBF convenience という位置づけ。

新しく追加する：

```coq
Theorem periodic_llf_schedulable_by_classical_dbf_any_offset :
  forall T tasks offset enumT jobs
         (codec : PeriodicCodec T tasks offset jobs),
    well_formed_periodic_tasks_on T tasks ->
    (forall j t,
      periodic_jobset T tasks offset jobs j ->
      ~ blocked jobs j t) ->
    NoDup enumT ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    (forall H j,
      periodic_jobset_upto T tasks offset jobs H j ->
      job_abs_deadline (jobs j) <= H /\
      exists t1 t2,
        busy_prefix_witness
          (generated_periodic_edf_schedule_upto
             T tasks offset jobs H enumT codec)
          (job_abs_deadline (jobs j)) t1 t2 /\
        periodic_edf_busy_prefix_bridge
          T tasks offset jobs H
          (generated_periodic_edf_schedule_upto
             T tasks offset jobs H enumT codec)
          j) ->
    (forall t,
      taskset_periodic_dbf tasks enumT t <= t) ->
    schedulable_by_on
      (periodic_jobset T tasks offset jobs)
      (llf_scheduler
        (periodic_candidates_before T tasks offset jobs enumT codec))
      jobs 1.
```

ただし、実際には existing `periodic_llf_schedulable_by_on` が window-DBF を取れるので、classical DBF から window-DBF へ落とす bridge を作ればいい。

これで LLF 接続の土台ができる。
LLF の prefix generator はまだ不要。焦らない。LLF は後で嫌というほど面倒になるから。

---

# Stage 2: offset-aware window-DBF checker

Stage 1 は sound だが、offset の利点を使わない。
非ゼロオフセットの本命はこっち。

## 6. extracted window-DBF decision を追加する

変更対象：

```text
theories/TaskModels/Periodic/PeriodicEDFExtractionDecision.v
theories/TaskModels/Periodic/PeriodicConcreteAnalysis.v
```

既存の：

```coq
window_dbf_test_upto tasks offset enumT H
```

はすでに offset を取る。これを extraction-facing に出す。

```coq
Definition extracted_offset_window_dbf_test_upto
    (ts : list ExtractedPeriodicTask)
    (H : Time) : bool :=
  window_dbf_test_upto
    (extracted_periodic_tasks ts)
    (extracted_periodic_offsets ts)
    (enumT_of_extracted_list ts)
    H.
```

counterexample も作る。

```coq
Definition first_window_dbf_overload_upto
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (enumT : list TaskId)
    (H : Time) : option (Time * Time) :=
  find
    (fun '(t1, t2) =>
       negb
         (taskset_periodic_dbf_window tasks offset enumT t1 t2
          <=? t2 - t1))
    (critical_dbf_windows_upto tasks offset enumT H).
```

extracted 版：

```coq
Definition extracted_offset_window_dbf_counterexample
    (ts : list ExtractedPeriodicTask)
    (H : Time) : option (Time * Time) :=
  first_window_dbf_overload_upto
    (extracted_periodic_tasks ts)
    (extracted_periodic_offsets ts)
    (enumT_of_extracted_list ts)
    H.
```

---

## 7. finite horizon 版を先に閉じる

まず infinite ではなく、有限 horizon theorem を作る。

```coq
Theorem extracted_offset_window_dbf_test_upto_sound :
  forall ts H,
    extracted_taskset_wf ts = true ->
    extracted_offset_window_dbf_test_upto ts H = true ->
    forall t1 t2,
      t1 <= t2 ->
      t2 <= H ->
      taskset_periodic_dbf_window
        (extracted_periodic_tasks ts)
        (extracted_periodic_offsets ts)
        (enumT_of_extracted_list ts)
        t1 t2 <= t2 - t1.
```

これは既存の：

```coq
window_dbf_test_upto_true_implies_bounded_window_dbf
```

でほぼ出る。

この段階で、**finite horizon offset EDF/LLF** はかなり楽に接続できる。

---

## 8. infinite offset window-DBF cutoff を別ファイルで証明する

新規ファイル案：

```text
theories/TaskModels/Periodic/PeriodicOffsetWindowCutoff.v
```

ここでやること：

```coq
Definition periodic_max_offset
    (offset : TaskId -> Time)
    (enumT : list TaskId) : Time := ...

Definition offset_window_dbf_cutoff_bound
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (enumT : list TaskId) : Time := ...
```

候補は保守的に：

```text
Omax + Dmax + S (Omax + Dmax) * hyperperiod
```

または：

```text
hyperperiod + Omax + Dmax + S (Omax + Dmax) * hyperperiod
```

で始める。最初から最小 cutoff を狙わない。
証明が通る cutoff が正義。最小化は後でいい。

必要な補題：

```coq
Lemma expected_release_shift_by_hyperperiod :
  forall tasks offset enumT τ k hp,
    In τ enumT ->
    0 < task_period (tasks τ) ->
    Nat.divide (task_period (tasks τ)) hp ->
    expected_release tasks offset τ (k + hp / task_period (tasks τ)) =
    expected_release tasks offset τ k + hp.
```

```coq
Lemma expected_deadline_shift_by_hyperperiod :
  forall tasks offset enumT τ k hp,
    In τ enumT ->
    0 < task_period (tasks τ) ->
    Nat.divide (task_period (tasks τ)) hp ->
    expected_abs_deadline tasks offset τ (k + hp / task_period (tasks τ)) =
    expected_abs_deadline tasks offset τ k + hp.
```

```coq
Lemma taskset_periodic_dbf_window_shift :
  forall tasks offset enumT hp t1 t2,
    hyperperiod_divides_tasks tasks enumT hp ->
    taskset_periodic_dbf_window tasks offset enumT (t1 + hp) (t2 + hp) =
    taskset_periodic_dbf_window tasks offset enumT t1 t2.
```

そして最終的に：

```coq
Theorem offset_window_dbf_check_by_cutoff :
  forall tasks offset enumT,
    NoDup enumT ->
    (forall τ, In τ enumT -> 0 < task_period (tasks τ)) ->
    window_dbf_test_upto
      tasks offset enumT
      (offset_window_dbf_cutoff_bound tasks offset enumT) = true ->
    forall t1 t2,
      t1 <= t2 ->
      taskset_periodic_dbf_window tasks offset enumT t1 t2 <= t2 - t1.
```

これができれば、offset-aware infinite analyzer が完成する。

---

# Stage 3: final certificate checker の zero-offset 固定を外す

ここが一番大きい。`PeriodicEDFFinalCertificateChecker.v` は `fun _ => 0` が大量に入っている。
数えたところ、このファイルだけで zero-offset 参照がかなり多い。つまりここを雑に直すと崩れる。

## 9. final checker を instance-parameterized にする

現状はだいたい：

```coq
extracted_periodic_tasks ts
(fun _ => 0)
extracted_periodic_jobs ts
extracted_periodic_codec ts
```

が直接出てくる。

これを、まず alias 化する。

```coq
Definition extracted_periodic_offsets ts := offset_of_extracted_list ts.
```

そして checker 全体で：

```coq
(fun _ => 0)
```

を：

```coq
(extracted_periodic_offsets ts)
```

に置換する。

ただし、一気に theorem を全部直すのは危険なので、順番はこう。

```text
1. extracted_periodic_jobs / codec だけ offset-aware にする
2. check_prefix_slots_match_generated_edf_fast が offset schedule を見るようにする
3. transport / window transport checker に offset を渡す
4. soundness theorem の zero-offset 仮定を any-offset classical DBF theorem で置き換える
5. 旧 zero-offset theorem を wrapper として残す
```

特に soundness の最後で今は：

```coq
edf_schedulability_decide_true_global_dbf_ok
```

と zero-offset classical bridge に頼っている。
ここを Stage 1 の any-offset classical bridge に差し替える。

---

## 10. checker 名は EDF から feasibility 寄りに寄せる

LLF 接続予定があるなら、ここで名前を整理する。

現状：

```coq
PeriodicEDFCheckedSidecarCert
check_periodic_edf_checked_sidecar_extracted
```

これは EDF 専用に見える。実際、prefix witness は EDF-generated schedule なので完全には中立ではない。けれど、結果として使いたいのは：

```text
periodic task set の feasibility certificate
```

であって、EDF専用の最終成果ではない。

まずは破壊的 rename ではなく alias を追加する。

```coq
Definition PeriodicFeasibilityCheckedSidecarCert :=
  PeriodicEDFCheckedSidecarCert.

Definition check_periodic_feasibility_checked_sidecar_extracted :=
  check_periodic_edf_checked_sidecar_extracted.
```

そして soundness を分ける。

```coq
Theorem check_periodic_feasibility_checked_sidecar_feasible :
  ...
  feasible_schedule_on
    (periodic_jobset ...)
    jobs 1
    (generated_periodic_edf_schedule ...).
```

その後：

```coq
Theorem check_periodic_feasibility_checked_sidecar_edf_schedulable :
  ... ->
  schedulable_by_on ... edf_scheduler ...

Theorem check_periodic_feasibility_checked_sidecar_llf_schedulable :
  ... ->
  schedulable_by_on ... llf_scheduler ...
```

これが LLF 接続の本命。

理解してる？
LLF 用に最初から LLF prefix checker を作る必要はない。
**EDF-generated witness で feasibility を証明し、その feasibility を LLF optimality に渡す**。これが一番安全。

---

# Stage 4: LLF 接続

## 11. policy-neutral entry point を作る

新規ファイル案：

```text
theories/TaskModels/Periodic/PeriodicPolicyAnalysis.v
theories/TaskModels/Periodic/PeriodicPolicyAnalysisEntryPoints.v
```

中身：

```coq
Inductive PeriodicPolicy :=
| PolicyEDF
| PolicyLLF.
```

checker は共通。

```coq
Definition check_periodic_policy_feasibility
    (p : PeriodicPolicy)
    (ts : list ExtractedPeriodicTask)
    (cert : EDFInfiniteCert JobId)
    (sidecar : PeriodicFeasibilityCheckedSidecarCert) : bool :=
  check_periodic_feasibility_checked_sidecar_extracted ts cert sidecar.
```

`p` は checker には不要。
soundness theorem 側でだけ使う。

```coq
Theorem check_periodic_policy_feasibility_edf_sound :
  check_periodic_policy_feasibility PolicyEDF ts cert sidecar = true ->
  ... ->
  schedulable_by_on ... edf_scheduler ... .
```

```coq
Theorem check_periodic_policy_feasibility_llf_sound :
  check_periodic_policy_feasibility PolicyLLF ts cert sidecar = true ->
  ... ->
  schedulable_by_on ... llf_scheduler ... .
```

LLF theorem は既存の：

```text
PeriodicLLFAnalysisBridge.v
PeriodicLLFInfiniteBridge.v
```

を使う。
この2つはすでに offset と window-DBF を取れる形になっているので、ここは大改造しなくてよい。

---

# Stage 5: Haskell extraction / CSV 対応

## 12. extraction 対象を増やす

変更対象：

```text
theories/TaskModels/Periodic/PeriodicEDFExtraction.v
```

追加で出すもの：

```coq
extracted_periodic_offsets
extracted_offset_window_dbf_test_upto
extracted_offset_window_dbf_counterexample
check_periodic_feasibility_checked_sidecar_extracted
check_periodic_policy_feasibility
```

Stage 1 では：

```coq
edf_schedulability_decide
```

を残してもよいが、名前は少し嘘になる。
おすすめは alias を作ること。

```coq
Definition periodic_conservative_schedulability_decide :=
  edf_schedulability_decide.
```

この名前なら、offset 入りでも「classical DBF による保守的判定」として自然。

---

## 13. CSV script を 4 列対応にする

変更対象：

```text
scripts/periodic_edf_schedulability_csv.hs
```

現状は：

```text
cost,period,deadline
```

だけ。

新形式：

```text
cost,period,deadline,offset
```

ただし legacy 互換として 3 列も許す。

```text
cost,period,deadline        -> offset = 0
cost,period,deadline,offset -> offset = offset
```

prefix generator も変更する。

現状：

```haskell
prefixJobRelease = jobIndex * parsedPeriod task
```

変更：

```haskell
prefixJobRelease =
  parsedOffset task + jobIndex * parsedPeriod task
```

horizon も変える。

現状：

```haskell
prefixHorizon =
  2 * hyperperiod tasks + maximum deadlines
```

変更：

```haskell
prefixHorizon =
  maximum offsets + 2 * hyperperiod tasks + maximum deadlines
```

まずはこれで十分。
後で window transport / post-reset まで考えるなら、もう少し大きめにしてもいい。

---

# Stage 6: examples / regression

## 14. 追加する例

新規または変更対象：

```text
theories/Examples/PeriodicOffsetExamples.v
theories/Examples/PeriodicInfiniteEDFExamples.v
theories/Examples/PeriodicInfiniteLLFExamples.v
theories/Examples/PeriodicManyTaskEDFExamples.v
```

追加するケース：

```coq
(* zero-offset regression *)
[(C=1,T=4,D=4,O=0);
 (C=1,T=5,D=5,O=0)]

(* nonzero offset, conservative DBF passes *)
[(C=1,T=4,D=4,O=1);
 (C=1,T=5,D=5,O=3)]

(* offset affects generated prefix *)
[(C=2,T=5,D=5,O=2);
 (C=1,T=4,D=3,O=0)]
```

Stage 2 で追加するべき例：

```text
classical DBF では落ちるが、offset-aware window DBF では通る task set
```

これは offset-aware 解析の価値を示すために必要。

---

# 推奨 PR 分割

## PR 1: offset field と offset-aware extracted jobset

変更：

```text
PeriodicEDFExtractionTypes.v
PeriodicEDFExtractionSoundness.v
PeriodicCodec.v は基本そのまま
scripts/periodic_edf_schedulability_csv.hs
```

目標：

```text
ExtractedPeriodicTask が offset を持つ
canonical jobs が offset release を持つ
zero-offset examples が壊れない
```

---

## PR 2: any-offset classical DBF theorem

変更：

```text
PeriodicClassicDBF.v
PeriodicEDFClassicalBridge.v
PeriodicEDFInfiniteBridge.v
PeriodicLLFAnalysisBridge.v
PeriodicLLFInfiniteBridge.v
```

目標：

```text
offset τ = 0 仮定なしで classical DBF -> window DBF を出す
EDF/LLF 両方に any-offset conservative wrapper を追加する
```

この PR が通れば、非ゼロオフセットの保守的 schedulability 解析は成立する。

---

## PR 3: final checker の offset-aware 化

変更：

```text
PeriodicEDFFinalCertificateChecker.v
PeriodicEDFCheckedSchedulabilityBridge.v
PeriodicEDFTransportWitnessChecker.v
PeriodicEDFTransportCoverageChecker.v
```

目標：

```text
fun _ => 0 を extracted_periodic_offsets ts に置き換える
prefix/generated EDF checker が offset release を見る
transport/hyperperiod shift が offset ありでも通る
```

この PR が一番重い。
`PeriodicEDFFinalCertificateChecker.v` に zero-offset 依存が集中しているので、ここは丁寧にやる。

---

## PR 4: feasibility alias と LLF 接続

変更：

```text
PeriodicFeasibilityCertificate.v
PeriodicFeasibilityAnalysis.v
PeriodicPolicyAnalysis.v
PeriodicPolicyAnalysisEntryPoints.v
```

目標：

```text
EDF certificate checker の結果を feasibility certificate として公開する
同じ checked certificate から EDF / LLF soundness theorem を出す
```

ここで LLF が解析対象に正式に入る。

---

## PR 5: exact offset-aware window-DBF checker

変更：

```text
PeriodicOffsetWindowCutoff.v
PeriodicConcreteAnalysis.v
PeriodicEDFExtractionDecision.v
```

目標：

```text
window_dbf_test_upto tasks offset enumT H を extracted API に出す
offset-aware cutoff theorem を証明する
first_window_dbf_overload_upto を返せるようにする
```

これは後でよい。
まず Stage 1 の保守的 any-offset 対応を通してからでいい。

---

# 最終的な API 目標

最終的にはこういう形にする。

```coq
Definition periodic_conservative_schedulability_decide
    (ts : list ExtractedPeriodicTask) : bool :=
  extracted_taskset_wf ts
  && dbf_test_by_cutoff
       (extracted_periodic_tasks ts)
       (enumT_of_extracted_list ts).
```

offset-aware 版：

```coq
Definition periodic_offset_window_schedulability_decide
    (ts : list ExtractedPeriodicTask) : bool :=
  extracted_taskset_wf ts
  && window_dbf_test_upto
       (extracted_periodic_tasks ts)
       (extracted_periodic_offsets ts)
       (enumT_of_extracted_list ts)
       (offset_window_dbf_cutoff_bound
          (extracted_periodic_tasks ts)
          (extracted_periodic_offsets ts)
          (enumT_of_extracted_list ts)).
```

policy wrapper：

```coq
Definition periodic_policy_schedulability_decide
    (p : PeriodicPolicy)
    (mode : PeriodicAnalysisMode)
    (ts : list ExtractedPeriodicTask)
    (cert : EDFInfiniteCert JobId)
    (sidecar : PeriodicFeasibilityCheckedSidecarCert) : bool :=
  match mode with
  | ConservativeClassical =>
      periodic_conservative_schedulability_decide ts
      && check_periodic_feasibility_checked_sidecar_extracted ts cert sidecar
  | OffsetWindow =>
      periodic_offset_window_schedulability_decide ts
      && check_periodic_feasibility_checked_sidecar_extracted ts cert sidecar
  end.
```

---

# 優先順位まとめ

実装順はこれ。

```text
1. ExtractedPeriodicTask に offset を追加
2. extracted_periodic_offsets / offset-aware jobs / offset-aware codec を追加
3. arbitrary-offset window DBF <= classical DBF を証明
4. EDF any-offset classical schedulability theorem を追加
5. LLF any-offset classical schedulability theorem を追加
6. Haskell CSV を 4列対応にする
7. final certificate checker の fun _ => 0 を offset accessor に置換
8. feasibility alias を作って EDF/LLF 共通 certificate にする
9. offset-aware window DBF checker を追加
10. infinite offset window cutoff theorem を証明
```

---

# 判断

最短で成果を出すなら：

```text
非ゼロオフセット対応 = Stage 1 の conservative classical DBF
```

でまず入れる。

その後：

```text
offset の効果を使う高機能解析 = Stage 2 の offset-aware window DBF
```

へ進む。

LLF については、最初から LLF prefix checker を作らない。
**EDF witness / window-DBF / feasibility certificate を中立化して、LLF optimality に渡す**。これが一番筋がいい。

まあ要するに、次の一手はこれよ。

```text
offset を Task に入れない。
extraction-facing の zero-offset 固定を外す。
classical DBF を any-offset conservative theorem に拡張する。
その結果を feasibility certificate として EDF/LLF に分配する。
```

これで、非ゼロオフセット対応と将来の LLF 接続が同時に進む。
