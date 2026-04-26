# Stage 2: offset-aware window-DBF checker

Stage 2 の目的は、Stage 1 の conservative classical DBF 判定を維持したまま、
非ゼロ offset の需要分散を実際に利用できる window-DBF checker を追加する
ことである。

最初の実装単位は finite horizon checker とする。infinite cutoff theorem は
別スライスに分ける。Stage 2 v1 では horizon `H` は caller が明示的に渡す。

- タスク終了時に、このファイルに進捗状況を保存すること。
- 実装中、大きな計画変更が必要なことに気づいた場合、それをタスク終了時に
  知らせること。

## Summary

- finite horizon の offset-aware window-DBF checker は実装済みである。
- finite EDF / LLF wrapper layer は実装済みである。
- infinite cutoff infrastructure は部分実装済みで、hyperperiod shift と
  explicit-shift cutoff theorem まで閉じている。
- finite offset-window check と classical DBF cutoff guard を合成する
  guarded arbitrary-window theorem は実装済みである。
- 残る主要作業は pure offset-window check だけで arbitrary-window cutoff を
  任意 window へ持ち上げる最終 theorem である。
- Stage 1 の `edf_schedulability_decide` / classical DBF path は保守的 path として
  維持する。
- final certificate の arbitrary-offset completion transport とは混ぜない。

## 1. Semantic assumptions

- `Task` record に offset field は追加しない。offset は引き続き
  `TaskId -> Time` の外部関数として扱う。
- periodic release は既存の
  `expected_release tasks offset tau k = offset tau + k * task_period ...`
  に従う。
- offset 正規化条件、例えば `offset tau < task_period ...` や
  `offset tau < periodic_hyperperiod ...` は追加しない。
- Stage 2 finite checker は次の window-DBF condition を直接検査する。

```coq
taskset_periodic_dbf_window tasks offset enumT t1 t2 <= t2 - t1
```

- Stage 2 v1 は finite horizon analyzer である。infinite guarantee は
  cutoff theorem が追加されるまで主張しない。
- Stage 1 の offset-insensitive classical DBF checker は保守的 path として残す。
- arbitrary offset の final certificate soundness は Stage 1 と同様に
  completion transport obligation を別問題として扱う。
- 任意長 window の cutoff 縮約は hyperperiod shift だけでは足りない。
  shift は window length を保存するため、長い window には
  load/utilization 側の補題が必要である。

## 2. Required observable events

- extraction-facing finite window-DBF decision は追加済みである。

```coq
extracted_offset_window_dbf_test_upto
extracted_offset_window_dbf_counterexample
extracted_offset_window_dbf_decide
```

- `extracted_offset_window_dbf_decide ts H` は
  `extracted_taskset_wf ts && extracted_offset_window_dbf_test_upto ts H`
  とする。
- counterexample witness は `option (Time * Time)` とする。
- Stage 1 の scalar DBF counterexample `option Time` は互換用に残す。
- Haskell/Rust-facing CLI/API を追加する場合は、Stage 1 checker と区別する。
  例: `check-offset-window-dbf`。
- pure offset-window infinite checker は pure arbitrary-window cutoff theorem が
  閉じるまで公開しない。classical guard 付き checker は保守的 path として扱う。
- runtime scheduler trace、OS event、dispatch detail は追加しない。

## 3. Interface delta

### `PeriodicConcreteAnalysis.v`

- 既存の `critical_dbf_windows_upto` と `window_dbf_test_upto` を再利用する。
- overload witness finder は追加済みである。

```coq
Definition first_window_dbf_overload_upto
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (enumT : list TaskId)
    (H : Time) : option (Time * Time) := ...
```

- `Some (t1, t2)` ならその window が overload していることを示す soundness
  lemma を追加する。

```coq
Lemma first_window_dbf_overload_upto_some :
  forall tasks offset enumT H t1 t2,
    first_window_dbf_overload_upto tasks offset enumT H = Some (t1, t2) ->
    t2 - t1 <
      taskset_periodic_dbf_window tasks offset enumT t1 t2.
```

### `PeriodicEDFExtractionDecision.v`

- extraction-facing finite wrapper は追加済みである。

```coq
Definition extracted_offset_window_dbf_test_upto
    (ts : list ExtractedPeriodicTask)
    (H : Time) : bool := ...

Definition extracted_offset_window_dbf_counterexample
    (ts : list ExtractedPeriodicTask)
    (H : Time) : option (Time * Time) := ...

Definition extracted_offset_window_dbf_decide
    (ts : list ExtractedPeriodicTask)
    (H : Time) : bool := ...
```

- proof-facing property を追加する。

```coq
Definition extracted_offset_window_dbf_ok_upto
    (ts : list ExtractedPeriodicTask)
    (H : Time) : Prop :=
  forall t1 t2,
    t1 <= t2 ->
    t2 <= H ->
    taskset_periodic_dbf_window
      (extracted_periodic_tasks ts)
      (extracted_periodic_offsets ts)
      (enumT_of_extracted_list ts)
      t1 t2 <= t2 - t1.
```

- soundness theorem を追加する。

```coq
Theorem extracted_offset_window_dbf_test_upto_sound :
  forall ts H,
    extracted_taskset_wf ts = true ->
    extracted_offset_window_dbf_test_upto ts H = true ->
    extracted_offset_window_dbf_ok_upto ts H.

Lemma extracted_offset_window_dbf_decide_true_ok :
  forall ts H,
    extracted_offset_window_dbf_decide ts H = true ->
    extracted_offset_window_dbf_ok_upto ts H.

Lemma extracted_offset_window_dbf_counterexample_sound :
  forall ts H t1 t2,
    extracted_offset_window_dbf_counterexample ts H = Some (t1, t2) ->
    t2 - t1 <
      taskset_periodic_dbf_window
        (extracted_periodic_tasks ts)
        (extracted_periodic_offsets ts)
        (enumT_of_extracted_list ts)
        t1 t2.
```

### `PeriodicEDFExtraction.v`

- extraction list には次を追加済みである。

```coq
extracted_offset_window_dbf_test_upto
extracted_offset_window_dbf_counterexample
extracted_offset_window_dbf_decide
```

- Stage 1 の exported functions は削除しない。

### `PeriodicEDFAnalysisEntryPoints.v`

- EDF finite window-DBF package wrapper は既存の
  `periodic_edf_schedulable_by_window_dbf_on_finite_horizon_generated_from_obligations`
  を Stage 2 finite EDF wrapper として扱う。

### `PeriodicLLFAnalysisEntryPoints.v`

- LLF finite wrapper は追加済みである。
- LLF feasibility bridge は busy-prefix witness を要求するため、
  `periodic_llf_schedulable_by_window_dbf_on_finite_horizon_generated_from_obligations`
  は `PeriodicEDFConcreteWindowObligations` に加えて explicit busy-prefix
  bridge premise を残す。

### `PeriodicOffsetWindowCutoff.v`

- infinite cutoff 用の proof-facing infrastructure は追加済みである。
- 実装済み:
  - `periodic_max_offset`
  - `offset_window_dbf_cutoff_bound`
  - `offset_window_dbf_test_by_cutoff`
  - hyperperiod release/deadline shift lemmas
  - `periodic_dbf_window_shift_by_hyperperiod`
  - `taskset_periodic_dbf_window_shift_by_hyperperiod`
  - `offset_window_dbf_check_by_cutoff_post_offset_shifted`
  - `offset_window_dbf_test_by_cutoff_with_classical_guard`
  - `offset_window_dbf_check_by_cutoff_with_classical_guard`
  - `periodic_dbf_window_hyperperiod_load_lower`
  - `taskset_periodic_dbf_window_hyperperiod_load_lower`
  - `offset_window_hyperperiod_load_le_hyperperiod`
  - `periodic_dbf_window_add_hyperperiod_upper`
  - `taskset_periodic_dbf_window_add_hyperperiod_upper`
  - `taskset_periodic_dbf_window_add_hyperperiod_upper_n`
- 未実装:
  - pure offset-window check だけを仮定する arbitrary-window 版
    `offset_window_dbf_check_by_cutoff`

## 4. Proof obligations

### Finite checker soundness

完了済み。`extracted_offset_window_dbf_test_upto_sound` は既存 theorem に
委譲する。

```coq
window_dbf_test_upto_true_implies_bounded_window_dbf
```

必要な proof steps:

- unfold `extracted_offset_window_dbf_test_upto`
- unfold `extracted_offset_window_dbf_ok_upto`
- apply `window_dbf_test_upto_true_implies_bounded_window_dbf`
- `t1 <= t2` と `t2 <= H` をそのまま渡す

`extracted_taskset_wf ts = true` は v1 theorem の interface に残すが、
bounded finite checker soundness 自体で不要なら proof body では使わなくてよい。
これは後続 schedulability wrapper と interface を揃えるための前提である。

### Counterexample soundness

完了済み。`first_window_dbf_overload_upto_some` は `find` の soundness から
導く。

Expected proof shape:

- unfold `first_window_dbf_overload_upto`
- apply `find_some` or equivalent list lemma
- destruct `(t1, t2)`
- unfold predicate
- convert `negb (x <=? y) = true` to `y < x` with `Nat.leb_gt`

extracted version は generic lemma に委譲する。

### Finite EDF / LLF connection

完了済み。

- EDF wrapper は既存 finite generated theorem を package-facing entry point として使う。
- LLF wrapper は explicit busy-prefix bridge premise を残す。

### Infinite cutoff

部分実装済み。次のファイルに分離済みである。

```text
theories/TaskModels/Periodic/PeriodicOffsetWindowCutoff.v
```

実装済み:

- `periodic_max_offset`
- `offset_window_dbf_cutoff_bound`
- `expected_release_shift_by_hyperperiod`
- `expected_deadline_shift_by_hyperperiod`
- `taskset_periodic_dbf_window_shift_by_hyperperiod`
- `offset_window_dbf_check_by_cutoff_post_offset_shifted`
- `offset_window_dbf_test_by_cutoff_with_classical_guard`
- `offset_window_dbf_check_by_cutoff_with_classical_guard`
- `periodic_dbf_window_hyperperiod_load_lower`
- `taskset_periodic_dbf_window_hyperperiod_load_lower`
- `offset_window_hyperperiod_load_le_hyperperiod`
- `periodic_dbf_window_add_hyperperiod_upper`
- `taskset_periodic_dbf_window_add_hyperperiod_upper`
- `taskset_periodic_dbf_window_add_hyperperiod_upper_n`

残る proof obligation:

- pure offset-window check だけを仮定する arbitrary-window 版
  `offset_window_dbf_check_by_cutoff` を証明する。
- cutoff bound は最小化を狙わず、証明しやすい保守的 bound を維持する。

## 5. Implementation order

完了済み:

1. `PeriodicConcreteAnalysis.v` に
   `first_window_dbf_overload_upto` と generic soundness lemma を追加した。
2. `PeriodicEDFExtractionDecision.v` に extracted finite window-DBF API と
   soundness lemmas を追加した。
3. `PeriodicEDFExtraction.v` の extraction list に新 API を追加した。
4. finite EDF / LLF wrapper layer を追加・確認した。
5. `PeriodicOffsetWindowCutoff.v` に cutoff infrastructure と explicit-shift
   theorem を追加した。
6. pure offset-window finite cutoff check から hyperperiod load bound を取り出す
   load/utilization 補題を追加した。
7. hyperperiod だけ window 終端を伸ばしたときの DBF 増分を
   `hyperperiod_load` で上から抑える upper-extension 補題を追加した。

次の実装順:

1. upper-extension n-step 補題と
   `offset_window_hyperperiod_load_le_hyperperiod` を組み合わせて
   long-window を cutoff 内 representative に縮約する。
2. post-offset/prefix window と long-window ケースを分けて
   arbitrary-window cutoff theorem を構成する。
3. `plan/stage2.md` の Progress に実装済み項目と残作業を追記する。
4. commit する場合は Stage 2 関連ファイルだけを stage する。

## 6. Acceptance checks

- finite API:
  - `make theories/TaskModels/Periodic/PeriodicConcreteAnalysis.vo`
  - `make theories/TaskModels/Periodic/PeriodicEDFExtractionDecision.vo`
  - `make theories/TaskModels/Periodic/PeriodicEDFExtraction.vo`
  - `make theories/TaskModels/Periodic/PeriodicEDFExtractionSoundness.vo`
- wrapper layer:
  - `make theories/TaskModels/Periodic/PeriodicEDFAnalysisEntryPoints.vo`
  - `make theories/TaskModels/Periodic/PeriodicLLFAnalysisEntryPoints.vo`
- cutoff layer:
  - `make theories/TaskModels/Periodic/PeriodicOffsetWindowCutoff.vo`
- docs / whitespace:
  - `git diff --check -- plan/stage2.md`
  - changed `.v` files when implementation files are touched.

If Haskell extraction artifacts are regenerated, also run the relevant CSV checker
smoke tests for 3-column and 4-column inputs.

## 7. Risks for the Rust design

- Stage 2 finite checker depends on horizon `H`; do not present it as an
  infinite schedulability checker until `offset_window_dbf_check_by_cutoff` exists.
- Stage 1 scalar DBF reject and Stage 2 window-DBF reject have different witness
  shapes. Rust/API code must not force both into one scalar witness type.
- Caller-chosen `H` is part of the Stage 2 v1 contract.
- offset-aware window DBF is an analysis-layer feature. Runtime dispatch,
  timer delay, migration, and OS-specific behavior stay outside the common
  periodic layer.

## 8. Progress

### 2026-04-26: Finite offset window-DBF API added

- `PeriodicConcreteAnalysis.v` に `first_window_dbf_overload_upto` と
  overload witness soundness lemma を追加した。
- `PeriodicEDFExtractionDecision.v` に finite horizon の
  `extracted_offset_window_dbf_test_upto`、
  `extracted_offset_window_dbf_counterexample`、
  `extracted_offset_window_dbf_decide` と対応する soundness lemmas を追加した。
- Haskell extraction list に Stage 2 finite window-DBF API を追加した。

残作業:

- finite EDF / LLF schedulability wrapper を必要に応じて追加する。
- infinite cutoff theorem を後続スライスで設計・証明する。

### 2026-04-26: finite EDF / LLF wrapper layer checked

- EDF finite window-DBF package wrapper は既存の
  `periodic_edf_schedulable_by_window_dbf_on_finite_horizon_generated_from_obligations`
  を Stage 2 の finite EDF wrapper として確認した。
- `PeriodicLLFAnalysisEntryPoints.v` に
  `periodic_llf_schedulable_by_window_dbf_on_finite_horizon_generated_from_obligations`
  を追加した。
- LLF 側の既存 finite feasibility bridge は busy-prefix witness を要求するため、
  LLF wrapper は `PeriodicEDFConcreteWindowObligations` に加えて
  explicit busy-prefix bridge premise を残す形にした。

残作業:

- infinite cutoff theorem を後続スライスで設計・証明する。

### 2026-04-26: offset window cutoff 基礎 lemmas 追加

- `PeriodicOffsetWindowCutoff.v` を追加し、future infinite cutoff theorem
  用の proof-facing infrastructure を分離した。
- `periodic_max_offset`、`offset_window_dbf_cutoff_bound`、
  `periodic_max_offset_ge` を追加した。
- hyperperiod が各 task period の倍数である事実を取り出す
  `hyperperiod_as_task_period_multiple` と、
  release/deadline を hyperperiod 分だけ shift するための
  `expected_release_shift_by_hyperperiod`、
  `expected_deadline_shift_by_hyperperiod` を追加した。

残作業:

- `taskset_periodic_dbf_window_shift` を設計・証明する。
- `offset_window_dbf_check_by_cutoff` を設計・証明する。

### 2026-04-26: window-DBF hyperperiod shift lemmas 追加

- `PeriodicOffsetWindowCutoff.v` に単一 task の
  `periodic_index_in_window_shift_by_hyperperiod` と
  `periodic_index_in_shifted_window_sub_hyperperiod` を追加した。
- 未正規化 offset を扱うため、shift 前 window の開始時刻に
  `periodic_max_offset offset enumT <= t1` を要求する形にした。
- `periodic_dbf_window_shift_by_hyperperiod` と
  `taskset_periodic_dbf_window_shift_by_hyperperiod` を追加し、
  window-DBF が hyperperiod shift で保存される proof-facing API を閉じた。

残作業:

- `offset_window_dbf_check_by_cutoff` を設計・証明する。

### 2026-04-26: explicit-shift cutoff theorem 追加

- `offset_window_dbf_test_by_cutoff` を追加した。
- `offset_window_dbf_check_by_cutoff_post_offset_shifted` を追加し、
  caller が cutoff 内へ戻す hyperperiod shift 量 `n` を明示できる場合に、
  finite cutoff check から元 window の DBF bound を導けるようにした。
- 当初検討した任意長 post-offset window の cutoff theorem は、
  hyperperiod shift が window length を保存するためそのままでは成立しない。
  長い window を扱うには utilization/load 側の別補題が必要である。

残作業:

- 長い window を cutoff へ縮約するための load/utilization 補題を設計する。
- `offset_window_dbf_check_by_cutoff` の arbitrary-window 版を設計・証明する。

### 2026-04-26: guarded arbitrary-window cutoff theorem 追加

- `offset_window_dbf_test_by_cutoff_with_classical_guard` を追加した。
- finite offset-window cutoff check と既存の scalar DBF cutoff guard を
  合成し、arbitrary-window soundness theorem
  `offset_window_dbf_check_by_cutoff_with_classical_guard` を追加した。
- long-window soundness は `taskset_periodic_dbf_window_le_classical_dbf`
  と `dbf_check_by_cutoff` に委譲するため、pure offset-window cutoff の
  load/utilization 補題は後続作業として残した。

残作業:

- pure offset-window check だけで arbitrary-window cutoff を閉じる
  load/utilization 補題を設計・証明する。
- pure offset-window check だけを仮定する arbitrary-window 版
  `offset_window_dbf_check_by_cutoff` を設計・証明する。

### 2026-04-26: pure offset-window load bound 追加

- `periodic_dbf_window_hyperperiod_load_lower` を追加し、post-offset window が
  任意の hyperperiod-like block `hp` について task 単位の load を下から含むことを
  示した。
- `taskset_periodic_dbf_window_hyperperiod_load_lower` を追加し、同じ `hp` を
  taskset 全体へ畳み上げる proof-facing API にした。
- `offset_window_hyperperiod_load_le_hyperperiod` を追加し、
  `offset_window_dbf_test_by_cutoff` から
  `hyperperiod_load tasks enumT (periodic_hyperperiod tasks enumT) <=
   periodic_hyperperiod tasks enumT`
  を導けるようにした。

残作業:

- load bound と explicit-shift theorem を組み合わせ、pure offset-window check
  だけを仮定する arbitrary-window 版
  `offset_window_dbf_check_by_cutoff` を設計・証明する。

### 2026-04-26: pure arbitrary-window cutoff 実装時の懸念

- `periodic_dbf_window_hyperperiod_load_lower` と
  `taskset_periodic_dbf_window_hyperperiod_load_lower` は、long post-offset
  window が少なくとも hyperperiod load block を含むことを示す下界である。
- arbitrary-window soundness には、window 終端を hyperperiod 分だけ伸ばした
  ときに追加される DBF が `hyperperiod_load` 以下であるという上界が必要である。
- そのため、最終 theorem の前に次の補題を追加する必要がある。

```coq
Lemma periodic_dbf_window_add_hyperperiod_upper :
  forall tasks offset tau t1 t2 hp,
    0 < task_period (tasks tau) ->
    Nat.divide (task_period (tasks tau)) hp ->
    periodic_dbf_window tasks offset tau t1 (t2 + hp) <=
    periodic_dbf_window tasks offset tau t1 t2 +
      (hp / task_period (tasks tau)) * task_cost (tasks tau).

Lemma taskset_periodic_dbf_window_add_hyperperiod_upper :
  forall tasks offset enumT t1 t2 hp,
    (forall tau, In tau enumT -> 0 < task_period (tasks tau)) ->
    (forall tau, In tau enumT -> Nat.divide (task_period (tasks tau)) hp) ->
    taskset_periodic_dbf_window tasks offset enumT t1 (t2 + hp) <=
    taskset_periodic_dbf_window tasks offset enumT t1 t2 +
      hyperperiod_load tasks enumT hp.
```

残作業:

- 上記 upper-extension 補題と n-step 版を証明する。
- それを `offset_window_hyperperiod_load_le_hyperperiod` と組み合わせ、
  pure offset-window check だけを仮定する arbitrary-window 版
  `offset_window_dbf_check_by_cutoff` を証明する。

### 2026-04-26: DBF upper-extension 補題追加

- `periodic_dbf_window_add_hyperperiod_upper` を追加し、単一 task の
  offset-window DBF について、window 終端を `hp` だけ伸ばしたときの増分を
  `(hp / task_period ...) * task_cost ...` で上から抑えた。
- `taskset_periodic_dbf_window_add_hyperperiod_upper` を追加し、taskset 全体の
  増分を `hyperperiod_load tasks enumT hp` へ畳み上げた。
- `taskset_periodic_dbf_window_add_hyperperiod_upper_n` を追加し、n-step の
  hyperperiod extension を `q * hyperperiod_load tasks enumT hp` で抑えた。

残作業:

- upper-extension n-step 補題と `offset_window_hyperperiod_load_le_hyperperiod` を
  組み合わせて long-window を cutoff 内 representative に縮約する。
- pure offset-window check だけを仮定する arbitrary-window 版
  `offset_window_dbf_check_by_cutoff` を証明する。
