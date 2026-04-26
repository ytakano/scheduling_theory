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

- `window_dbf_test_upto` はすでに `offset` を取るので、これを
  extraction-facing API として公開する。
- Stage 1 の `edf_schedulability_decide` / classical DBF path は維持する。
- Stage 2 の reject witness は scalar `t` ではなく window `(t1, t2)` とする。
- finite horizon soundness を先に閉じ、infinite cutoff は後続タスクへ分離する。
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

## 2. Required observable events

- extraction-facing に finite window-DBF decision を追加する。

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
- Haskell/Rust-facing CLI/API を追加する場合は、Stage 1 checker と区別する
  名前にする。例: `check-offset-window-dbf`。
- runtime scheduler trace、OS event、dispatch detail は追加しない。

## 3. Interface delta

### `PeriodicConcreteAnalysis.v`

- 既存の `critical_dbf_windows_upto` と `window_dbf_test_upto` を再利用する。
- 新しく overload witness finder を追加する。

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

- extraction-facing wrapper を追加する。

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

- extraction list に次を追加する。

```coq
extracted_offset_window_dbf_test_upto
extracted_offset_window_dbf_counterexample
extracted_offset_window_dbf_decide
```

- Stage 1 の exported functions は削除しない。

## 4. Proof obligations

### Finite checker soundness

`extracted_offset_window_dbf_test_upto_sound` は既存 theorem に委譲する。

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

`first_window_dbf_overload_upto_some` は `find` の soundness から導く。

Expected proof shape:

- unfold `first_window_dbf_overload_upto`
- apply `find_some` or equivalent list lemma
- destruct `(t1, t2)`
- unfold predicate
- convert `negb (x <=? y) = true` to `y < x` with `Nat.leb_gt`

extracted version は generic lemma に委譲する。

### Finite EDF / LLF connection

Stage 2 v1 は DBF checker API までを必須とする。
Finite EDF / LLF schedulability wrapper は次スライスで追加してよい。
追加する場合は、既存 finite horizon window-DBF theorem に
`extracted_offset_window_dbf_ok_upto` を渡す薄い wrapper に限定する。

### Infinite cutoff

Stage 2 v1 では実装しない。後続スライスで次を新規ファイルに分離する。

```text
theories/TaskModels/Periodic/PeriodicOffsetWindowCutoff.v
```

後続スライスの証明対象:

- `periodic_max_offset`
- `offset_window_dbf_cutoff_bound`
- `expected_release_shift_by_hyperperiod`
- `expected_deadline_shift_by_hyperperiod`
- `taskset_periodic_dbf_window_shift`
- `offset_window_dbf_check_by_cutoff`

cutoff bound は最小化を狙わず、まず証明しやすい保守的 bound を使う。

## 5. Implementation order

1. `PeriodicConcreteAnalysis.v` に
   `first_window_dbf_overload_upto` と generic soundness lemma を追加する。
2. `PeriodicEDFExtractionDecision.v` に extracted finite window-DBF API と
   soundness lemmas を追加する。
3. `PeriodicEDFExtraction.v` の extraction list に新 API を追加する。
4. 関連 `.vo` を個別にビルドする。
5. `plan/stage2.md` の Progress に実装済み項目と残作業を追記する。
6. 実装完了後に commit する場合は、Stage 2 関連ファイルだけを stage する。

## 6. Acceptance checks

- `make theories/TaskModels/Periodic/PeriodicConcreteAnalysis.vo`
- `make theories/TaskModels/Periodic/PeriodicEDFExtractionDecision.vo`
- `make theories/TaskModels/Periodic/PeriodicEDFExtraction.vo`
- `make theories/TaskModels/Periodic/PeriodicEDFExtractionSoundness.vo`
- `git diff --check -- theories/TaskModels/Periodic/PeriodicConcreteAnalysis.v theories/TaskModels/Periodic/PeriodicEDFExtractionDecision.v theories/TaskModels/Periodic/PeriodicEDFExtraction.v plan/stage2.md`

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
