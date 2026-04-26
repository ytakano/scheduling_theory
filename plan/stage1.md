# Stage 1: 非ゼロオフセット入力対応・保守的 DBF 判定

この段階の目的は、既存の periodic core を作り直さずに、extraction-facing
層と checked entry point から zero-offset 固定を外すことである。
判定自体は offset-aware exact/window 解析ではなく、任意 offset の
window DBF を offset-insensitive な classical DBF で上から抑える
保守的な schedulability test として位置づける。

- タスク終了時に、このファイルに進捗状況を保存すること
- 実装中、大きな計画変更が必要なことに気づいた場合、それをタスク終了時に協調して知らせること

## Progress

### 2026-04-26: First slice completed

- `ExtractedPeriodicTask` に `extracted_task_offset` を追加した。
- `default_extracted_periodic_task` と extracted Haskell artifact の task
  constructor を 4 フィールドに更新した。
- `zero_offset_extracted_periodic_task` と `offset_of_extracted_list` を追加した。
- CSV script は `cost,period,deadline` と `cost,period,deadline,offset`
  の両方を受け付ける。3 列入力は offset `0` として扱う。
- offset は `extracted_task_wf` の positivity 条件に含めていない。

残作業:

- `extracted_periodic_jobs` を `extracted_periodic_offsets` へ切り替える作業は、
  any-offset classical DBF wrapper がまだないため次スライスへ残した。
- `PeriodicClassicDBF.v` の任意 offset comparison lemma と
  EDF/LLF any-offset schedulability wrappers は未実装。
- prefix certificate checker の offset-aware 化は、jobs/codec の offset-aware 化と
  同じスライスで行う。

### 2026-04-26: Any-offset classical DBF bridge completed

- `PeriodicClassicDBF.v` に任意 offset 版の single-task / taskset DBF
  comparison lemma を追加した。
- `PeriodicEDFInfiniteBridge.v` に zero-offset premise を要求しない
  any-offset classical DBF wrapper 群を追加した。
- 既存の zero-offset theorem 名と互換 path は維持した。

残作業:

- `extracted_periodic_jobs` と `extracted_periodic_codec` を
  `extracted_periodic_offsets` に切り替える。
- extraction-facing soundness theorem を any-offset EDF wrapper へ接続する。
- checked transport / final certificate checker の extracted offset 化を行う。
- LLF 側の any-offset classical wrapper は未実装。

### 2026-04-26: Extraction soundness offset path added

- `extracted_periodic_offsets` と `extracted_offset_periodic_jobs` を
  extraction-facing soundness 層に追加した。
- offset-aware jobs に対する
  `edf_schedulability_decide_schedulable_by_on_with_offsets` を追加し、
  any-offset classical DBF wrapper に接続した。
- Haskell extraction に `extracted_periodic_offsets` と
  `extracted_offset_periodic_jobs` を公開した。
- checked transport の generic wrapper は zero-offset premise を要求しない
  any-offset classical DBF theorem に接続した。

計画調整:

- 既存 `extracted_periodic_jobs` は final certificate checker の後方互換 entry が
  zero-offset transport proof に依存しているため、このスライスでは
  zero-offset jobs のまま残した。
- `extracted_periodic_jobs` 自体を offset-aware に置き換える作業は、
  final certificate / transport checker の offset-aware migration と同じ
  スライスで行う。

残作業:

- final certificate / transport checker の zero-offset transport 補題を
  offset-aware に一般化する。
- prefix certificate checker の generated checker 呼び出しを
  `extracted_periodic_offsets` と offset-aware jobs へ切り替える。
- LLF 側の any-offset classical wrapper は未実装。

### 2026-04-26: LLF any-offset classical DBF wrappers completed

- `PeriodicLLFAnalysisBridge.v` に finite-horizon LLF の any-offset
  classical DBF wrapper を追加した。
- `PeriodicLLFInfiniteBridge.v` に no-deadline-miss / feasible schedule /
  schedulable-by の any-offset classical DBF wrapper を追加した。
- LLF 側も EDF 側と同じく、classical DBF premise から window DBF premise への
  変換を `taskset_periodic_dbf_window_le_classical_dbf` に委譲する。
- 既存の zero-offset theorem 名と互換 path は維持した。

残作業:

- final certificate / transport checker の zero-offset transport 補題を
  offset-aware に一般化する。
- prefix certificate checker の generated checker 呼び出しを
  `extracted_periodic_offsets` と offset-aware jobs へ切り替える。
- `extracted_periodic_jobs` 自体を offset-aware に置き換える作業は、
  final certificate / transport checker の offset-aware migration と同じ
  スライスで行う。

### 2026-04-26: Extracted offset codec and prefix checker path added

- `extracted_offset_periodic_codec` を追加し、
  `extracted_periodic_offsets` / `extracted_offset_periodic_jobs` に対する
  extraction-facing codec を公開した。
- checked transport wrapper に offset-aware extraction-facing theorem を追加した。
- Haskell extraction list に offset-aware codec を追加した。
- prefix certificate checker の generated EDF 照合を
  `extracted_periodic_offsets` と `extracted_offset_periodic_jobs` へ切り替えた。
- native prefix certificate generator は release を `offset + k * period` とし、
  horizon に最大 offset を含める。

残作業:

- final certificate / transport checker 本体の zero-offset transport 補題を
  offset-aware に一般化する。
- `extracted_periodic_jobs` 自体を offset-aware に置き換える作業は、
  final certificate / transport checker の offset-aware migration と同じ
  スライスで行う。

### 2026-04-26: Non-fast extracted prefix checker removed

- CLI option `--check-prefix-cert-extracted` を削除し、prefix certificate
  checker の実行経路を fast checker に一本化した。
- Haskell extraction list から `check_prefix_slots_match_generated_edf` を外した。
- Rocq 内の `check_prefix_slots_match_generated_edf` は fast checker の
  proof-facing specification として残した。

残作業:

- final certificate / transport checker 本体の zero-offset transport 補題を
  offset-aware に一般化する。
- `extracted_periodic_jobs` 自体を offset-aware に置き換える作業は、
  final certificate / transport checker の offset-aware migration と同じ
  スライスで行う。

### 2026-04-26: Offset-aware final sidecar checker entry added

- final sidecar checker の boolean 本体を
  `check_periodic_edf_checked_sidecar_with_jobs` として
  offset/jobs/codec 引数付きに分離した。
- 既存 `check_periodic_edf_checked_sidecar` と
  `check_periodic_edf_checked_sidecar_extracted` は zero-offset 互換 wrapper
  として維持した。
- `check_periodic_edf_checked_sidecar_extracted_with_offsets` を追加し、
  `extracted_periodic_offsets` / `extracted_offset_periodic_jobs` /
  `extracted_offset_periodic_codec` を使う executable entry を公開した。

残作業:

- final certificate / transport checker 本体の soundness theorem と
  zero-offset transport 補題を offset-aware に一般化する。
- `extracted_periodic_jobs` 自体を offset-aware に置き換える作業は、
  final certificate / transport checker の offset-aware migration と同じ
  スライスで行う。

### 2026-04-26: Any-offset generated-checks transport wrapper added

- `PeriodicEDFTransportWitnessChecker.v` に
  `periodic_edf_schedulable_by_classical_dbf_any_offset_with_periodic_hyperperiod_transport_generated_checks`
  を追加した。
- 既存の periodic hyperperiod transport / generated-checks obligations は維持し、
  zero-offset premise だけを要求しない path を追加した。
- DBF 側は any-offset classical DBF wrapper に委譲し、no-carry-in bridge は
  既存 periodic hyperperiod transport theorem に委譲する。

残作業:

- final certificate checker の extracted offset entry から any-offset
  generated-checks transport wrapper へ接続する soundness theorem を追加する。
- final certificate / transport checker 本体の zero-offset transport 補題を
  offset-aware に一般化する。
- `extracted_periodic_jobs` 自体を offset-aware に置き換える作業は、
  final certificate / transport checker の offset-aware migration と同じ
  スライスで行う。

### 2026-04-26: Offset final sidecar soundness wrapper added

- `check_periodic_edf_checked_sidecar_with_jobs_fields` を追加し、
  final sidecar checker 本体の boolean 分解を offset/jobs/codec 引数付きで
  再利用できるようにした。
- `check_periodic_edf_checked_sidecar_extracted_with_offsets_sound_with_hyperperiod_transport`
  を追加し、extracted offset entry を any-offset generated-checks transport
  wrapper へ接続した。
- periodic hyperperiod backlog transport はこの段階では明示的な proof
  obligation として残し、checker 内部での構成は次スライスへ分離した。

残作業:

- final certificate / transport checker 本体の zero-offset transport 補題を
  offset-aware に一般化し、checker が
  `PeriodicHyperperiodBacklogTransportObligation` を内部で構成できるようにする。
- `extracted_periodic_jobs` 自体を offset-aware に置き換える作業は、
  final certificate / transport checker の offset-aware migration と同じ
  スライスで行う。

## 1. Semantic assumptions

- `Task` レコードには offset を入れない。既存設計どおり、offset は
  `TaskId -> Time` の外部関数として扱う。
- periodic release は既存の
  `expected_release tasks offset tau k = offset tau + k * task_period ...`
  に従う。Stage 1 ではこの core semantics を変更しない。
- extraction-facing 入力では `cost > 0`、`period > 0`、
  `relative_deadline > 0` だけを well-formedness 条件にする。
  `offset = 0` は有効であり、`offset > 0` は要求しない。
- `edf_schedulability_decide` は、非ゼロ offset 入力に対しても
  classical DBF checker を使い続ける。この checker は offset の利点を
  利用しないが、任意 offset に対する sound な十分条件として使う。
- 既存 zero-offset theorem と zero-offset tutorial path は壊さず、
  any-offset theorem / wrapper を追加して新しい経路を作る。

## 2. Required observable events

- extraction-facing task input に `offset` フィールドを追加する。
  標準 CSV/API 形は `cost,period,deadline,offset` とする。
- 後方互換として、既存の 3 列 CSV `cost,period,deadline` は
  `offset = 0` と解釈する。
- Haskell CSV checker の usage、header detection、row parser、
  `ParsedTask`、`toEDFTask` を 4 列対応に更新する。
- prefix certificate checker で明示的に渡している offset 引数は
  `fun _ => 0` ではなく `extracted_periodic_offsets input` を使う。
- scheduler trace、runtime event、OS-specific event は追加しない。
  Stage 1 の proof-facing observable は release offset だけである。

## 3. Interface delta

- `theories/TaskModels/Periodic/PeriodicEDFExtractionTypes.v`
  - `ExtractedPeriodicTask` に `extracted_task_offset : nat` を追加する。
  - `default_extracted_periodic_task` を
    `mkExtractedPeriodicTask 1 1 1 0` に更新する。
  - `offset_of_extracted_list : list ExtractedPeriodicTask -> TaskId -> Time`
    を追加する。
  - zero-offset 互換 constructor として
    `zero_offset_extracted_periodic_task c p d :=
     mkExtractedPeriodicTask c p d 0` を追加する。
  - `extracted_task_wf` は offset を検査しないままにする。

- `theories/TaskModels/Periodic/PeriodicEDFExtractionSoundness.v`
  - `extracted_periodic_offsets ts := offset_of_extracted_list ts` を追加する。
  - `extracted_periodic_jobs ts` を
    `canonical_periodic_jobs_from_enumT ... (extracted_periodic_offsets ts) ...`
    に変更する。
  - `extracted_periodic_nonblocking` と extraction-facing
    schedulability wrapper の `periodic_jobset` / scheduler 引数を
    `extracted_periodic_offsets ts` 版に揃える。
  - final proof は zero-offset wrapper ではなく any-offset classical
    DBF wrapper を使う。

- `theories/TaskModels/Periodic/PeriodicEDFFinalCertificateChecker.v`
  - `extracted_periodic_codec` の型を
    `PeriodicCodec ... (extracted_periodic_offsets ts) ...` に変更する。
  - nonempty case は `zero_offset_periodic_codec_of_tasks` ではなく
    `periodic_codec_of_enumT` で構成する。
  - 空リスト case も同じ offset accessor を使う。
  - local lemmas 内の `(fun _ => 0)` を `extracted_periodic_offsets ts`
    に置き換える。

- `theories/TaskModels/Periodic/PeriodicEDFCheckedSchedulabilityBridge.v`
  - checked transport wrapper から zero-offset premise
    `(forall tau, In tau enumT -> offset tau = 0)` を外した any-offset 版を
    追加する。
  - extraction-facing checked wrapper は
    `extracted_periodic_offsets ts` と any-offset wrapper を使う。
  - zero-offset 既存 theorem は互換用に残してよい。

- `theories/TaskModels/Periodic/PeriodicClassicDBF.v`
  - 任意 offset 版 comparison lemma を追加する。
    `periodic_dbf_window_le_classical_dbf`:
    任意 task/window について
    `periodic_dbf_window tasks offset tau t1 t2 <=
     periodic_dbf tasks tau (t2 - t1)` を示す。
  - taskset 版
    `taskset_periodic_dbf_window_le_classical_dbf` を追加する。
  - 既存 `zero_offset_window_dbf_le_classical_dbf` と
    `zero_offset_taskset_window_dbf_le_classical_dbf` は残す。

- `theories/TaskModels/Periodic/PeriodicEDFInfiniteBridge.v`
  - `periodic_edf_no_deadline_miss_from_classical_dbf_any_offset`
    を追加する。
  - `periodic_edf_feasible_schedule_from_classical_dbf_any_offset`
    を追加する。
  - `periodic_edf_schedulable_by_classical_dbf_any_offset` を追加する。
  - `with_no_carry_in_bridge` 版も必要な existing wrapper に合わせて
    追加する。
  - 既存 `periodic_edf_schedulable_by_classical_dbf_on` は
    zero-offset convenience wrapper として残す。

- `theories/TaskModels/Periodic/PeriodicLLFInfiniteBridge.v` と
  `theories/TaskModels/Periodic/PeriodicLLFAnalysisBridge.v`
  - EDF と同じ方針で any-offset classical wrapper を追加する。
  - classical DBF assumption から window-DBF assumption への変換は
    `taskset_periodic_dbf_window_le_classical_dbf` に委譲する。
  - Stage 1 では LLF 固有の新しい prefix generator は追加しない。

- `theories/TaskModels/Periodic/PeriodicEDFExtractionDecision.v`
  - `extracted_taskset_dbf_test` と `edf_schedulability_decide` は
    `dbf_test_by_cutoff` を使い続ける。
  - コメントと theorem の説明を、zero-offset checker ではなく
    offset-insensitive conservative classical DBF checker として更新する。
  - counterexample は scalar classical DBF overload witness `t` のままにする。
    offset-aware window overload witness `(t1,t2)` は Stage 2 に送る。

- `scripts/periodic_edf_schedulability_csv.hs`
  - `ParsedTask` に `parsedOffset :: Int` を追加する。
  - 3 列 row は offset `0`、4 列 row は明示 offset として parse する。
  - header は `cost,period,deadline` と
    `cost,period,deadline,offset` の両方を受け付ける。
  - `toEDFTask` は
    `EDF.MkExtractedPeriodicTask cost period deadline offset` を呼ぶ。
  - generated prefix checker 呼び出しの offset 引数を
    `EDF.extracted_periodic_offsets input` に更新する。

## 4. Proof obligations

- extraction well-formedness:
  - `extracted_tasks_well_formed_on_enum` は offset 追加後も
    period positivity だけで成立する。
  - `offset_of_extracted_list` は list 範囲外では
    `default_extracted_periodic_task` の offset `0` を返す。

- extraction job semantics:
  - `extracted_periodic_jobs` は
    `extracted_periodic_offsets ts` を使って canonical periodic jobs を生成する。
  - `extracted_periodic_nonblocking` は offset accessor 版 jobs に対して
    既存と同じ構造で成立する。
  - `extracted_periodic_codec` は `periodic_codec_of_enumT` の
    `NoDup`、complete、sound、nonempty obligations を既存 enum lemmas で閉じる。

- classical DBF comparison:
  - single-task lemma:
    `periodic_dbf_window_le_classical_dbf`.
  - taskset lemma:
    `taskset_periodic_dbf_window_le_classical_dbf`.
  - 証明では、任意 offset の window 内 job index count を
    window length だけに依存する classical count で上界する。
  - zero-offset 専用 lemma を削除せず、必要なら any-offset lemma から
    corollary として再証明してもよい。

- EDF any-offset bridge:
  - classical premise
    `forall t, taskset_periodic_dbf tasks enumT t <= t`
    と comparison lemma から、
    `forall t1 t2, t1 <= t2 ->
       taskset_periodic_dbf_window tasks offset enumT t1 t2 <= t2 - t1`
    を導く。
  - その window-DBF premise を既存
    `periodic_edf_*_from_window_dbf*` theorem に渡す。
  - no-carry-in / busy-prefix bridge は Stage 1 では引き続き明示 obligation
    として downstream に残す。

- LLF any-offset bridge:
  - EDF と同じ DBF conversion を使い、既存 LLF window-DBF theorem に委譲する。
  - LLF 側で新しい runtime-specific detail を要求しない。

- extraction-facing final soundness:
  - `edf_schedulability_decide ts = true` から
    `extracted_taskset_global_dbf_ok ts` を得る既存 theorem は維持する。
  - final schedulability theorem は
    `extracted_periodic_offsets ts` 版 jobset/scheduler に対して成立する。
  - checked transport wrapper は transport certificate obligations と
    classical DBF checker result を合成するだけに留める。

- Acceptance checks:
  - `make theories/TaskModels/Periodic/PeriodicEDFExtractionTypes.vo`
  - `make theories/TaskModels/Periodic/PeriodicClassicDBF.vo`
  - `make theories/TaskModels/Periodic/PeriodicEDFInfiniteBridge.vo`
  - `make theories/TaskModels/Periodic/PeriodicLLFInfiniteBridge.vo`
  - `make theories/TaskModels/Periodic/PeriodicEDFExtractionSoundness.vo`
  - `make theories/TaskModels/Periodic/PeriodicEDFFinalCertificateChecker.vo`
  - `make theories/TaskModels/Periodic/PeriodicEDFCheckedSchedulabilityBridge.vo`
  - `cd /awkernel_refinement/scheduling_theory && make -j2`
  - CSV checker を 3 列 input と 4 列 input の両方で動作確認する。

## 5. Risks for the Rust design

- Stage 1 checker は offset-aware exact analysis ではない。
  Rust 側の API 名や error message で「offset の需要分散を利用する判定」
  と誤解させない。
- checker の reject は「unschedulable」ではなく
  「保守的 classical DBF test では受理できない」を意味する。
- scalar DBF counterexample `t` は Stage 1 の witness にすぎない。
  Stage 2 の offset-aware window checker では `(t1,t2)` witness が必要になるため、
  Rust 側で witness shape を過度に固定しない。
- offset を task intrinsic field として深く固定すると、後続の jitter /
  operational delay / adapter-local release modeling と衝突しやすい。
  Rust 側でも release-generation parameter として扱える境界を残す。
- 3 列 CSV 互換は維持するが、長期的な標準形は 4 列
  `cost,period,deadline,offset` とする。
- Stage 1 は public proof-facing abstraction を小さく保つことが目的であり、
  Rust runtime-specific dispatch detail、timer delay、migration detail は
  common periodic layer に持ち込まない。
