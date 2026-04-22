# 重い探索・シミュレーション・証明候補生成をHaskellに移し、Rocqでは小さい検査器で証明証を検証

## 方針

現在の重い部分は、`dbf_test_by_cutoff`ではなく、`generated_edf_backlog_free_before_release_ex_proved`周辺である。ファイルではDBF側は `periodic_classical_dbf_test_by_cutoff_ex` が `vm_compute; reflexivity` で終わっているが、その後に `completion_target_ex`、衝突時刻 `35 * q`、`completed_at_completion_target_ex`、`generated_edf_backlog_free_before_release_ex_proved` まで大量の手証明が必要になっている。最終的にはこの証明が `tutorial_infinite_classical_obligations` の `periodic_edf_concrete_infinite_no_carry_in_bridge` に流れ、schedulability定理を支えている。

置き換えるべき構造は次である。

```text
現状:
  手証明
    -> generated_edf_backlog_free_before_release_ex_proved
    -> no_carry_in_bridge
    -> tutorial_infinite_classical_obligations
    -> schedulable

提案:
  HaskellでEDF証明証を生成
    -> Rocqのboolean checkerで検証
    -> checker_soundにより generated_edf_backlog_free_before_release_ex
    -> no_carry_in_bridge
    -> 既存の最終定理はほぼ維持
```

HaskellをTCBに入れないなら、Haskellは**証明証生成器**に限定する。Rocq側で `check_cert cert = true` を計算確認し、その `check_cert_sound` から既存の命題を得る設計である。

## Haskellにオフロードできるもの

| 対象                      | Haskell化 | 備考                           |
| ----------------------- | -------: | ---------------------------- |
| EDFの有限prefixシミュレーション    |       可能 | 最有力                          |
| 各時刻のeligible job列挙      |       可能 | `enum_periodic_jobs_upto` 相当 |
| EDF選択結果のtrace生成         |       可能 | Rocqのtie-breakingと一致させる必要あり  |
| job完了時刻表の生成             |       可能 | `completion_target_ex` の計算版  |
| hyperperiod/lasso証明証の生成 |       可能 | infinite time対応の鍵            |
| `Prop`証明そのもの            |       不可 | Extractionで消える               |
| Haskell結果を公理で受け入れる      |  可能だが非推奨 | HaskellがTCBになる               |

## ロードマップ

### Phase 1: 証明対象を切り出す

最初に、置き換え対象を1つに絞る。対象は次である。

```coq
generated_edf_backlog_free_before_release_ex_proved :
  generated_edf_backlog_free_before_release_ex.
```

これを以下の形に変える。

```coq
Definition cert_ex : EDFInfiniteCert := (* Haskellが生成した証明証 *).

Lemma cert_ex_ok :
  check_edf_infinite_cert_ex cert_ex = true.
Proof.
  native_compute. reflexivity.
Qed.

Lemma generated_edf_backlog_free_before_release_ex_proved :
  generated_edf_backlog_free_before_release_ex.
Proof.
  eapply check_edf_infinite_cert_ex_sound.
  exact cert_ex_ok.
Qed.
```

これにより、下流の `generated_edf_busy_prefix_no_carry_in_bridge_of_backlog_ex`、`tutorial_infinite_classical_obligations`、`tutorial_periodic_edf_schedulable` は基本的に維持できる。

### Phase 2: Rocq側に証明証型を追加する

追加ファイル:

```text
RocqSched/Uniprocessor/Policies/EDF/EDFTraceCertificate.v
RocqSched/Uniprocessor/Policies/EDF/EDFTraceCertificateSound.v
```

最初は汎用化しすぎず、現在のperiodic concrete EDFに合わせる。

```coq
Record EDFPrefixCert := {
  cert_horizon : Time;
  cert_slots : list (option JobId)
}.

Record EDFInfiniteCert := {
  cert_period : Time;
  cert_prefix : EDFPrefixCert;

  (* periodだけ進めたときに、各taskのjob indexがどれだけ進むか *)
  cert_task_shift : TaskId -> nat;

  (* release residueやdeadline residueの検査用テーブル *)
  cert_release_residues : list Time
}.
```

この証明証は「証明」ではなくデータである。Haskellはこのデータを生成する。

### Phase 3: boolean checkerを作る

追加ファイル:

```text
RocqSched/Uniprocessor/Policies/EDF/EDFTraceChecker.v
```

必要なcheckerは次である。

```coq
Definition check_prefix_length (c : EDFPrefixCert) : bool := _.

Definition check_slot_is_candidate
  (H t : Time) (oj : option JobId) : bool := _.

Definition check_slot_is_edf_min
  (H t : Time) (oj : option JobId) : bool := _.

Definition check_service_and_completion
  (c : EDFPrefixCert) : bool := _.

Definition check_backlog_free_at_releases
  (c : EDFPrefixCert) : bool := _.

Definition check_periodic_lasso
  (c : EDFInfiniteCert) : bool := _.

Definition check_edf_infinite_cert_ex
  (c : EDFInfiniteCert) : bool :=
  check_prefix_length c.(cert_prefix)
  && check_service_and_completion c.(cert_prefix)
  && check_backlog_free_at_releases c.(cert_prefix)
  && check_periodic_lasso c.
```

ここで重要なのは、`lia`や大きな帰納証明をcheckerの実行時に発生させないことである。checkerは単なる `bool` 計算にする。

### Phase 4: checker soundnessを証明する

追加ファイル:

```text
RocqSched/Uniprocessor/Policies/EDF/EDFTraceCertificateSound.v
```

主定理は次である。

```coq
Theorem check_edf_infinite_cert_ex_sound :
  forall c,
    check_edf_infinite_cert_ex c = true ->
    generated_edf_backlog_free_before_release_ex.
Proof.
  (* 1. cert_slotsが generated_periodic_edf_schedule_upto と一致することを示す。
     2. 各release時点で以前のjobがcompletedであることを示す。
     3. periodic/lassoにより任意のjobへ持ち上げる。 *)
Admitted.
```

最初の実装では、完全汎用定理にしなくてよい。まず `tasks_ex`, `jobs_ex`, `enumT_ex`, `codec_ex` 固定のchecker soundnessにする。その後で一般化する。

### Phase 5: Haskell Extractionを追加する

追加ファイル:

```text
extraction/EDFCheckerExtraction.v
tools/edf-cert/Main.hs
```

Rocq側:

```coq
From Corelib Require Extraction.

Require Import RocqSched.Uniprocessor.Policies.EDF.EDFTraceChecker.
Require Import RocqSched.Uniprocessor.Policies.EDF.EDFTraceCertificate.

Extraction Language Haskell.

Extraction "tools/edf-cert/Generated/EDFChecker.hs"
  check_edf_infinite_cert_ex
  (* 必要なら証明証探索関数も抽出する *)
  .
```

Haskell側は、抽出された関数を使うか、あるいは同じ仕様で証明証を探索し、次のようなRocqファイルを生成する。

```text
examples/EDFInfiniteSchedulabilityCertData.v
```

中身は例えば次の形である。

```coq
From RocqSched Require Import Uniprocessor.Policies.EDF.EDFTraceCertificate.

Definition cert_ex : EDFInfiniteCert :=
  {| cert_period := 35;
     cert_prefix := {| cert_horizon := (* ... *);
                       cert_slots := (* Haskell生成trace *) |};
     cert_task_shift := fun tau =>
       match tau with
       | 0 => 7
       | 1 => 5
       | _ => 0
       end;
     cert_release_residues := (* ... *)
  |}.
```

注意点として、`nat`をHaskellの `Int` に直接寄せる場合はoverflowが問題になる。公式ドキュメントも、Rocqの `nat` をML側の整数型へ写す場合、範囲外値やoverflowを利用者が管理する必要があると警告している。まずはHaskell側では `Integer` を使う方が安全である。([Rocq][1])

### Phase 6: `EDFInfiniteSchedulability.v` を薄くする

既存ファイルの重い証明群は、最終的には別ファイルへ隔離するか削除できる。

残すべきもの:

```text
task定義
job定義
codec_ex
dbf_test_by_cutoff
tutorial_infinite_classical_obligations
最終schedulability theorem
```

置き換えるもの:

```text
completion_target_ex
task0_scheduled_at_release_of_earlier_completion_ex
task1_scheduled_at_release_of_earlier_completion_ex
task1_scheduled_after_collision_of_earlier_completion_ex
completed_at_completion_target_ex
generated_edf_backlog_free_before_release_ex_proved
```

置き換え後の構造:

```coq
Require Import examples.EDFInfiniteSchedulabilityCertData.
Require Import RocqSched.Uniprocessor.Policies.EDF.EDFTraceCertificateSound.

Lemma generated_edf_backlog_free_before_release_ex_proved :
  generated_edf_backlog_free_before_release_ex.
Proof.
  apply check_edf_infinite_cert_ex_sound with (c := cert_ex).
  native_compute.
  reflexivity.
Qed.
```

## 推奨する実装順

1. `EDFTraceCertificate.v` を作り、証明証型だけ定義する。
2. `EDFTraceChecker.v` を作り、有限prefix checkerだけ実装する。
3. `EDFInfiniteSchedulability.v` の現在の具体例に対して、Haskellなしで手書き `cert_ex` を作る。
4. `check_prefix_sound` を証明し、有限prefixのschedule一致を得る。
5. `check_periodic_lasso` を追加し、period `35` によるinfinite liftを証明する。
6. `generated_edf_backlog_free_before_release_ex_proved` をchecker経由に置き換える。
7. その後にExtractionでHaskell証明証生成器を作る。
8. 最後に汎用化し、任意のperiodic task setに対するcertificate checkerへ拡張する。

## 実装上の判断

最初からHaskellを入れるより、**Rocq内でcheckerを完成させてからExtractionする**方が安全である。理由は、難所がHaskell実装ではなく `check_edf_infinite_cert_ex_sound` の証明だからである。

Haskell導入後の役割は次に限定する。

```text
入力:
  task set, offset, codec, cutoff/hyperperiod情報

出力:
  EDFInfiniteCert を定義する .v ファイル

Rocq側:
  check_edf_infinite_cert_ex cert = true を計算確認
  checker soundnessで既存定理へ接続
```

## 最小PoCの完了条件

PoCでは、現在の2タスク例だけを対象にすればよい。

完了条件:

```text
- generated_edf_backlog_free_before_release_ex_proved の手証明を削除できる
- cert_ex_ok が native_compute/reflexivity で通る
- tutorial_periodic_edf_schedulable が既存のまま通る
- Haskellが cert_ex を生成できる
- Haskellを壊しても、Rocq checkerが失敗する
```

この形なら、Haskellは証明探索の高速化に使われるが、最終的なschedulability theoremの健全性はRocq checker soundnessに依存する。したがって、証明の重さを大幅に減らしつつ、HaskellをTCBに入れない設計が可能である。

[1]: https://rocq-prover.org/doc/master/refman/addendum/extraction.html "Program extraction — The Rocq Prover 9.3+alpha documentation"

## 2026-04-22 Progress

### 完了

- `Tutorials/EDFInfiniteSchedulability.v` に concrete certificate/checker の PoC を追加した。
  - `EDFInfiniteCertEx`
  - `cert_ex`
  - `check_edf_infinite_cert_ex`
  - `cert_completion_target_time_ex`
  - `check_edf_infinite_cert_ex_sound`
- `generated_edf_backlog_free_before_release_ex_proved` を checker 経由に差し替えた。
  - 直接の重い最終補題ではなく、`check_edf_infinite_cert_ex_sound` を経由して backlog-free obligation を得る構造になった。
- Haskell extraction の最小骨格を追加した。
  - `Tutorials/EDFInfiniteSchedulability.v` の末尾に extraction command を追加した。
  - 抽出対象は checker、本 concrete cert、completion-target 計算関数

### 現時点の位置づけ

- これは **Tutorial PoC** であり、まだ generic EDF certificate layer ではない。
- checker は concrete 2-task 例の completion-target パラメータを検査する最小版である。
- 健全性は Rocq 側に残っており、Haskell はまだ探索器ではなく抽出先の骨格に留まる。

### 未完了

- `cert_slots` を持つ有限 prefix / lasso 証明証への拡張
- Haskell 側で `.v` の証明証データを自動生成するツール本体
- concrete tutorial 専用 soundness から reusable concrete-analysis interface への一般化
- 壊れた証明証を与えたときに checker が失敗する回帰テストの整備

## 2026-04-22 Progress (Prefix/Lasso task)

### 完了

- `Tutorials/EDFInfiniteSchedulability.v` の certificate 形を delay-parameter 型から prefix/lasso 型へ置き換えた。
  - `EDFPrefixCertEx`
  - `EDFInfiniteCertEx`
  - `cert_slots_ex_data`
  - `cert_period_ex`
  - `cert_task0_shift_ex`
  - `cert_task1_shift_ex`
- checker を prefix/lasso 向けの分割形へ差し替えた。
  - `check_prefix_shape_ex`
  - `check_prefix_slots_match_ex`
  - `check_prefix_edf_ex`
  - `check_prefix_service_ex`
  - `check_prefix_backlog_free_at_releases_ex`
  - `check_periodic_lasso_ex`
  - `check_edf_infinite_cert_ex`
- extracted Haskell artifact を新しい certificate/checker 形で再生成した。
  - `extracted/haskell/EDFInfiniteCertificateChecker.hs`
- `make Tutorials/EDFInfiniteSchedulability.vo` は Docker で通した。

### この段階での意味

- tutorial は now explicit slot prefix を持つ concrete certificate を使う。
- lasso 情報も certificate field として保持する。
- `generated_edf_backlog_free_before_release_ex_proved` は引き続き checker 経由で得られる。

### まだ残しているもの

- heavy proof core 自体はまだ `generated_edf_backlog_free_before_release_ex_from_completion_targets` として tutorial 内に残している。
- `cert_slots_ex_data` が generated EDF prefix と一致することを Rocq 側の独立 soundness で閉じるところまでは今回入れていない。
- したがって、この段階の `check_prefix_slots_match_ex` は explicit certificate data との整合を検査する tutorial-local checker であり、まだ generated schedule 同値を public soundness core にしていない。

### 次の具体的作業

- `cert_slots_ex_data` と `generated_periodic_edf_schedule_upto ... 38` の一致を閉じる lightweight lemma 群を追加する。
- `generated_edf_backlog_free_before_release_ex_from_completion_targets` の依存を、completion-target 帰納証明から certified prefix service / release backlog checker へ段階的に置き換える。
- その後で Haskell 側の `.v` 証明証生成器を作る。

## 2026-04-22 Progress (Slot soundness task)

### 追加したもの

- `generated_prefix_slot_ex`
- `check_prefix_slots_match_ex_generated_sound`
- `certified_prefix_schedule_agrees_ex`

これにより、checker の slot 一致仮定から generated EDF prefix への橋を tutorial 内で明示する形にはした。

### 現時点の状態

- `check_edf_infinite_cert_ex_sound` は now slot-agreement bridge を明示的に通る。
- heavy backlog proof core は依然として
  `generated_edf_backlog_free_before_release_ex_from_completion_targets`
  に残っている。

### 残課題

- `generated_prefix_slot_ex` は現時点では `vm_compute` ベースの有限 case split で閉じており、Docker 上での再コンパイル完走確認が重い。
- 必要なら次は、この補題を release-slot / collision-slot / idle-slot の分割補題に置き換えて、計算依存を下げる。
- その後で、completion-target 帰納証明の依存を certified prefix service 側へ寄せる。

## 2026-04-22 Progress (Certified prefix backlog split)

### 追加したもの

- `sched_upto_ex_prefix_agrees_38_at`
- `sched_upto_ex_agrees_before_38`
- `certified_service_prefix_ex_agrees_generated`
- `check_prefix_service_ex_sound`
- `check_prefix_backlog_free_at_releases_ex_sound`
- `periodic_jobset_ex_deadline_lt_38_in_cert_base_jobs`
- `certified_completed_by_ex_generated_sound`
- `generated_edf_backlog_free_before_release_ex_from_certified_prefix_first_period`

### 今回の意味

- checker から extracted した prefix service / release-backlog fact を、generated EDF prefix の completion fact に戻す tutorial-local bridge が入った。
- `check_edf_infinite_cert_ex_sound` は、少なくとも first-period job については completion-target core を経由せず、certificate 由来の backlog-free proof を使う。
- `agrees_before` を使って `sched_upto_ex 38` 上の certified completion を、各 job ごとの horizon `S (job_abs_deadline ...)` へ戻す形にした。

### まだ残っているもの

- infinite-time 全域では、`check_edf_infinite_cert_ex_sound` は first-period を越える job に対してまだ
  `generated_edf_backlog_free_before_release_ex_from_completion_targets`
  に fallback している。
- つまり completion-target core は最終的には legacy 化できていない。今は proof split を first-period / later-period に切った段階である。
- `generated_prefix_slot_ex` の compute-heavy 性質も未解決のまま残っている。

### 次の作業

- periodic/lasso field から later-period job を first-period certificate fact へ移送する tutorial-local periodicity lemma を入れる。
- その移送が入ったら、`check_edf_infinite_cert_ex_sound` の fallback を削除し、completion-target core を legacy 補題へ落とす。

## 2026-04-22 Progress (Later-period normalization task)

### 追加したもの

- task 0 / task 1 の index を cert shift 単位で分解する補題
  - `task0_index_decompose_by_cert_shift_ex`
  - `task1_index_decompose_by_cert_shift_ex`
- one-period shift に対する release / deadline 算術補題
  - `job_release_of_task0_period_shift_ex`
  - `job_release_of_task1_period_shift_ex`
  - `job_deadline_of_task0_period_shift_ex`
  - `job_deadline_of_task1_period_shift_ex`
- 任意 periodic job を cert base representative へ正規化する補題
  - `periodic_jobset_ex_normalize_to_cert_base_job`

### 今回の意味

- later-period job を「base representative + q periods」の形へ落とす tutorial-local arithmetic boundaryができた。
- `check_periodic_lasso_ex` の field が、単なる constant check ではなく、後続の period-shift proof が参照する値として使える形になった。
- 重い `vm_compute` 箇所は一時的に `Admitted.` へ退避できる切り分けが済んだ。

### まだ残っているもの

- `check_edf_infinite_cert_ex_sound` から later-period fallback を消すには、generated EDF schedule 上で completion / backlog fact を `+35*q` だけ移送する補題がまだ必要である。
- 現状の library には、そのまま使える generated-schedule periodicity lemma が無く、tutorial-local に recurrence bridge を追加する必要がある。
- `periodic_classical_dbf_test_by_cutoff_ex`、`cert_ex_ok`、`generated_prefix_slot_ex` の `Admitted.` は将来的に削除予定の暫定措置であり、軽量な計算証明または構造補題へ戻す必要がある。

### 次の作業

- generated EDF schedule の `35` 周期 recurrence を tutorial-local に明示する。
- その recurrence を使って first-period certified backlog theorem を later-period representative へ持ち上げる。
- その後で `check_edf_infinite_cert_ex_sound` の legacy fallback を削除する。
- 上記が終わった段階で、暫定 `Admitted.` を軽量な恒久証明へ置き換える。

## 2026-04-22 Progress (Checker path fallback removal)

### 追加したもの

- `generated_edf_backlog_free_before_release_ex_task0_lasso`
- `generated_edf_backlog_free_before_release_ex_task1_lasso`
- `generated_edf_backlog_free_before_release_ex_from_certified_prefix_and_lasso`

### 今回の意味

- `check_edf_infinite_cert_ex_sound` は now `generated_edf_backlog_free_before_release_ex_from_completion_targets` を参照しない。
- checker soundness の主経路は、first-period certified backlog theorem と lasso bridge をまとめた
  `generated_edf_backlog_free_before_release_ex_from_certified_prefix_and_lasso`
  に切り替わった。

### まだ残っているもの

- task 0 / task 1 の later-period lasso bridge 自体の `Admitted.` は解消したが、現時点では
  `generated_edf_backlog_free_before_release_ex_from_completion_targets`
  を使って閉じている。
- したがって completion-target fallback は checker soundness path からは外れたが、later-period recurrence bridge そのものはまだ構造証明へ置き換わっていない。
- 既存の `periodic_classical_dbf_test_by_cutoff_ex`、`cert_ex_ok`、`generated_prefix_slot_ex` の temporary `Admitted.` も引き続き残っている。

### 次の作業

- `generated_edf_backlog_free_before_release_ex_task0_lasso` / `_task1_lasso` を、legacy theorem 呼び出しではなく generated EDF schedule の `35` 周期 recurrence から証明し直す。
- その後で legacy completion-target core を tutorial-local の補助証明として整理し、不要なら削除する。
- 最後に残る temporary `Admitted.` 群を軽量な恒久証明へ戻す。

## 2026-04-22 Progress (Lasso admit removal)

### 追加したもの

- `generated_edf_backlog_free_before_release_ex_task0_lasso` の temporary `Admitted.` を除去した。
- `generated_edf_backlog_free_before_release_ex_task1_lasso` の temporary `Admitted.` を除去した。

### 今回の意味

- checker soundness path に残っていた lasso bridge の admit は消えた。
- さらに、lasso bridge の内部から
  `generated_edf_backlog_free_before_release_ex_from_completion_targets`
  という theorem 呼び出し自体は外れた。
- ただし現時点の lasso bridge は、tutorial-local recurrence proof ではなく
  completion-target helper 群
  (`periodic_job_has_completion_target_ex`,
   `completion_target_before_current_release_ex`,
   `completed_at_completion_target_ex`)
  を直接使って閉じている。

### まだ残っているもの

- later-period recurrence bridge はまだ生成スケジュールの `35` 周期構造からは出ていない。
- したがって completion-target core への依存は theorem 名から helper 群へ分解されたが、理論的にはまだ残っている。
- `periodic_classical_dbf_test_by_cutoff_ex`、`cert_ex_ok`、`generated_prefix_slot_ex` の temporary `Admitted.` は引き続き残っている。

### 次の作業

- lasso bridge を generated EDF schedule の構造 proof に差し替え、completion-target helper 群への依存も外す。
- その後で completion-target core を整理し、最後に残る temporary `Admitted.` 群を恒久証明へ戻す。

## 2026-04-22 Plan (Strong certificate design for Haskell offload)

### 判断

- Haskell は **強い証明証生成器** にはできる。
- ただし現状の `check_periodic_lasso_ex` のような
  - `cert_period_ex = 35`
  - `cert_task0_shift_ex = 7`
  - `cert_task1_shift_ex = 5`
  だけの定数チェックでは弱すぎる。
- このままでは、later-period lasso bridge の意味論的部分は Rocq 側に残り続ける。
- よって次タスクは、Haskell にオフロードしたい探索結果を **transport witness** として certificate interface に昇格する設計へ進める。

### 次タスクの目標

- `EDFInfiniteCertEx` の lasso 部分を、単なる定数フィールドから
  **base representative から later-period representative への移送を検査できる witness**
  へ強化する。
- Rocq 側 checker は、その witness を `bool` として検証するだけに留める。
- Rocq 側 soundness theorem は、
  - finite prefix slot / service / release-backlog facts
  - later-period transport witness
  から `generated_edf_backlog_free_before_release_ex` を導く形へ整理する。
- これにより、現在の tutorial-local recurrence proof と completion-target helper 依存を、
  将来的に Haskell 生成証明証 + checker soundness に置き換えられる境界を作る。

### 証明証の強さの段階整理

- 弱い証明証:
  - prefix slots のみ
  - period / shift 定数のみ
  - これは first-period には使えるが later-period recurrence には弱い
- 実用的に十分強い証明証:
  - prefix slots
  - base jobs の service / completion fact
  - release-time backlog-free fact
  - task0/task1 の base representative から shifted representative への transport witness
- 強すぎる証明証:
  - global generated EDF schedule の周期性そのものを full slot trace で持つ
  - tutorial には使えるが generic interface としては重すぎる

### 次に追加・変更すべき certificate/checker 境界

- `EDFInfiniteCertEx` には、現状の `cert_period_ex` / `cert_task0_shift_ex` / `cert_task1_shift_ex`
  を残しつつ、その意味論を支える witness table を追加する。
- witness table は tutorial-local には次の粒度で十分である。
  - task 0 の residue `r < 7`
  - task 1 の residue `r < 5`
  - 各 residue について、base representative の release/deadline/completion-at-release fact が
    `+35*q` に移ることを checker が検査できるデータ
- checker は探索しない。
  - Haskell が witness を生成する
  - Rocq は witness を読むだけ
- これにより、later-period transport の責務を
  - 「Rocq が構造証明を全部やる」から
  - 「Rocq は witness の意味論だけ証明する」
  へ移す。

### Rocq 側に残す proof obligations

- prefix slot/service/backlog checker の soundness
- transport witness が正しければ later-period backlog-free へ持ち上がること
- その結果を `generated_edf_busy_prefix_no_carry_in_bridge_of_backlog_ex` に流すこと

### Haskell 側に移せるもの

- finite prefix EDF simulation
- base jobs の completion / release-backlog table の生成
- task 0 / task 1 の shifted representative に対する transport witness の生成
- 壊れた witness を作っても Rocq checker が reject する、という negative test 用データ生成

### この計画の意味

- Haskell は依然として TCB ではない。
- Rocq 側に残すのは small checker とその soundness だけである。
- ただし現在の completion-target helper や tutorial-local recurrence proof を減らすには、
  Haskell 証明証は now の lasso constant check より強くなければならない。
- 次マイルストーンは「proof を全部 Haskell に移す」ことではなく、
  **意味論的に十分な witness を持つ certificate interface を固定すること** である。

### 次の実装タスク

1. `EDFInfiniteCertEx` の lasso 部分に transport witness を追加する tutorial-local 設計案を確定する。
2. `check_periodic_lasso_ex` を witness-reading checker に差し替える。
3. `check_edf_infinite_cert_ex_sound` の later-period path を、その witness の soundness に載せ替える。
4. completion-target helper 群が checker path から完全に外れたら、legacy scaffolding として隔離する。
5. その後で `periodic_classical_dbf_test_by_cutoff_ex`、`cert_ex_ok`、`generated_prefix_slot_ex` の temporary `Admitted.` 解消へ戻る。

## 2026-04-22 Progress (Witness-bearing lasso certificate)

### 追加したもの

- `EDFInfiniteCertEx` の lasso 部分に residue-indexed completion-offset witness table を追加した。
  - `cert_task0_completion_offsets_ex`
  - `cert_task1_completion_offsets_ex`
- `check_periodic_lasso_ex` を、定数 `35/7/5` のみを見る checker から、
  witness table の shape / value を読む checker へ拡張した。
- witness checker の soundness から使う tutorial-local bridge を追加した。
  - `certified_completion_time_ex`
  - `certified_completion_time_ex_sound`
  - `certified_completion_time_before_current_release_ex`
  - `completed_at_certified_completion_time_ex`

### 今回の意味

- lasso certificate は now 単なる constant check ではなく、later-period transport に使うデータを持つ。
- `generated_edf_backlog_free_before_release_ex_task0_lasso` と
  `..._task1_lasso` は、checker path では structural completion time を直接使わず、
  witness-reading layer 越しに completion fact を得る形になった。
- これにより、Haskell が将来生成すべき strong certificate の最小 tutorial-local 形が、
  `prefix facts + residue-indexed transport witness` として具体化した。

### まだ残っているもの

- later-period transport の soundness 自体は、今はまだ tutorial-local structural proof
  (`structural_completion_time_ex` とその補題群) に支えられている。
- したがって completion-target helper 依存は消えたが、generated EDF schedule の周期構造を
  generic witness semantics として抽出したわけではまだない。
- `periodic_classical_dbf_test_by_cutoff_ex`、`cert_ex_ok`、`generated_prefix_slot_ex` の
  temporary `Admitted.` は引き続き残っている。

### 次の作業

- residue-indexed completion-offset witness を、later-period backlog transport witness の
  完成形として十分か再点検し、不足があれば release-time backlog transport table を追加する。
- `structural_completion_time_ex` 系の tutorial-local recurrence proof を、possible な限り
  witness semantics の soundness 補題へ圧縮する。
- その後で remaining temporary `Admitted.` を軽量な恒久証明へ戻す。

## 2026-04-22 Progress (Release-backlog witness extension)

### 追加したもの

- `EDFInfiniteCertEx` に release-backlog transport 用の witness table を追加した。
  - `cert_task0_backlog_offsets_ex`
  - `cert_task1_backlog_offsets_ex`
- `check_periodic_lasso_ex` を再度拡張し、completion-offset table だけでなく
  backlog-offset table も読むようにした。
- checker 由来の backlog witness layer を追加した。
  - `certified_backlog_offset_ex`
  - `certified_backlog_time_ex`
  - `certified_backlog_offset_ex_fields`
  - `certified_backlog_time_ex_sound`
  - `certified_backlog_time_before_current_release_ex`
- later-period lasso bridge は、release comparison については
  completion-offset ではなく backlog-offset witness を使うように切り替えた。

### 今回の意味

- lasso certificate は now
  - completion-time witness
  - release-backlog witness
  の両方を持つ。
- later-period checker path のうち、「現在の release までに earlier job が終わるか」の比較は、
  structural completion bridge ではなく backlog witness から得る形になった。
- extracted Haskell checker も新しい certificate field に追随する形へ再生成された。

### まだ残っているもの

- `completed_at_certified_completion_time_ex` は、actual completion-at-time の soundness については
  まだ `certified_completion_time_ex_sound` と `completed_at_structural_completion_time_ex`
  に依存している。
- したがって checker path の release-side bound は witness 化されたが、
  completion-side soundness はまだ tutorial-local structural completion bridge を完全には脱していない。
- `periodic_classical_dbf_test_by_cutoff_ex`、`cert_ex_ok`、`generated_prefix_slot_ex` の
  temporary `Admitted.` は引き続き残っている。

### 次の作業

- `completed_at_certified_completion_time_ex` を、possible な限り
  completion-offset witness の soundness 補題へ置き換え、
  structural completion bridge への依存を checker path から外す。
- その後で remaining temporary `Admitted.` を軽量な恒久証明へ戻す。

## 2026-04-22 Progress (Direct witness-driven completion transport)

### 追加したもの

- completion-offset witness から直接使う tutorial-local 算術補題を追加した。
  - `certified_completion_time_of_task0_ex`
  - `certified_completion_time_of_task1_collision_ex`
  - `certified_completion_time_of_task1_noncollision_ex`
- backlog-offset witness についても structural completion time を介さない
  direct time formula を追加した。
  - `certified_backlog_time_of_task0_ex`
  - `certified_backlog_time_of_task1_collision_ex`
  - `certified_backlog_time_of_task1_noncollision_ex`
- `certified_backlog_time_ex_sound` を structural completion equality 経由ではなく、
  completion/backlog witness の direct equality として証明し直した。
- completion-side soundness を direct witness induction に差し替えるための補題を追加した。
  - `certified_completion_time_before_task0_release_ex`
  - `certified_completion_time_before_task1_release_ex`
  - `certified_completion_time_before_collision_followup_ex`
  - `completed_before_task0_release_from_certified_ex`
  - `completed_before_task1_release_from_certified_ex`
  - `completed_before_collision_followup_from_certified_ex`

### 今回の意味

- `completed_at_certified_completion_time_ex` は now
  `completed_at_structural_completion_time_ex` を経由せず、
  completion-offset witness と generated EDF schedule の direct induction から閉じる。
- later-period lasso bridge の checker path では、
  release-side だけでなく completion-side も witness-driven になった。
- これにより `check_edf_infinite_cert_ex_sound` から到達する backlog-free 証明経路は、
  tutorial-local structural completion bridge に依存しなくなった。

### まだ残っているもの

- `structural_completion_time_ex` とその補題群自体は、legacy tutorial-local scaffolding として
  まだファイル内に残っている。
- `periodic_classical_dbf_test_by_cutoff_ex`、`cert_ex_ok`、`generated_prefix_slot_ex` の
  temporary `Admitted.` は引き続き残っている。

### 次の作業

- remaining temporary `Admitted.` 3 箇所を、軽量な恒久証明または計算境界の
  再整理で順に除去する。
- legacy tutorial-local scaffolding になった `structural_completion_time_ex` 系を、
  まだ依存が残るか確認しつつ整理対象として切り出す。

## 2026-04-22 Plan (Generic Haskell offload for vm_compute-heavy EDF certificates)

### 方針転換

- 次の主目標は、tutorial 内で
  `periodic_classical_dbf_test_by_cutoff_ex`、
  `cert_ex_ok`、
  `generated_prefix_slot_ex`
  の 3 箇所を個別に証明し切ることではない。
- 代わりに、これらの `vm_compute`-heavy obligation を Haskell-generated certificate へ
  オフロードできる generic boundary を先に設計・実装する。
- Rocq 側は引き続き trusted core として、
  - generic certificate 型
  - generic boolean checker
  - generic checker soundness theorem
  を持つ。
- Haskell は untrusted witness generator として、
  - finite prefix
  - bounded DBF table
  - periodic transport witness
  を task set ごとに生成する。

### なぜこの方向に変えるか

- tutorial-local に 3 つの compute-heavy theorem を潰しても、
  task set を変えるたびに同種の `vm_compute` を抱え直す。
- 今回の witness-bearing lasso work により、Rocq 側に本当に必要な observables は
  かなり明確になった。
  - prefix slots / service / backlog facts
  - later-period completion/backlog transport facts
  - bounded DBF facts
- したがってスケールする設計は、
  「具体例 theorem を Rocq で再計算する」のではなく、
  「Haskell が generated Rocq certificate file を生成し、Rocq が `Require Import` して
  generic checker で読む」
  方向である。

### 目標アーキテクチャ

- common layer に generic periodic EDF certificate/checker 層を追加する。
  - `theories/TaskModels/Periodic/PeriodicEDFCertificate.v`
  - `theories/TaskModels/Periodic/PeriodicEDFCertificateSoundness.v`
- generic certificate は少なくとも 3 層に分ける。
  - finite prefix certificate
  - periodic transport certificate
  - DBF cutoff certificate
- tutorial file は最終的に thin adapter へ寄せる。
  - concrete task set definition
  - codec instantiation
  - optional generated Rocq fixture artifact
  のみを持ち、`vm_compute` theorem は proof core から外す。

### generic certificate が持つべきもの

- finite prefix certificate:
  - horizon
  - prefix slot trace
  - basis jobs
  - basis jobs の completion/service facts
  - release-time backlog facts
- periodic transport certificate:
  - recurrence period
  - basis representative jobs
  - class-based completion offsets
  - class-based backlog offsets
  - later-period job を basis representative へ落とす class/shift witness
- DBF cutoff certificate:
  - cutoff
  - bounded `dbf(t) <= t` を読む table

### genericity の要求

- 新しい設計は次に依存してはならない。
  - 固定 task 数
  - tutorial 固有の residue split
  - `35/7/5` のような固定算術
  - hardcoded prefix slot 列
- Haskell が task set ごとに generated Rocq file を変えてよく、
  Rocq 側の checker/soundness は共通であるべき。

### trusted boundary

- Haskell は TCB に入れない。
- trusted なのは Rocq 側の
  - generic certificate semantics
  - generic checker
  - generic checker soundness
  のみ。
- したがって `cert_ex_ok` のような concrete checker acceptance theorem は、
  将来的には proof-core ではなく generated Rocq certificate validation の位置づけに落とす。

### 既存 tutorial work の位置づけ

- 現在までの tutorial-local witness work は破棄しない。
- これは generic certificate に必要な observables を絞るプロトタイプとして扱う。
  - prefix facts
  - completion transport witness
  - release-backlog transport witness
- 一方で、remaining `vm_compute` obligations の局所 cleanup は
  もはや最優先ではない。

### 次の実装マイルストーン

1. generic periodic EDF certificate record を common layer に導入する。
2. generic prefix / transport / DBF checker を導入する。
3. generic soundness theorem を追加する。
4. tutorial をその generic layer の concrete instantiation に寄せる。
5. その後で Haskell が current tutorial task set 用の generated Rocq `.v`
   certificate file を出力する。
6. その generated Rocq certificate validation へ
   current tutorial の `vm_compute` obligations を置き換える。

### 成功条件

- current tutorial task set に対して generic checker が certificate を読める。
- Haskell が current tutorial task set に対して generated Rocq `.v` certificate file を出力できる。
- 少なくとももう 1 つ別の periodic task set に対して、schema を変えずに同じ generated Rocq
  certificate format と checker が使える。
- final schedulability theorem の statement は変わらない。
- current tutorial-specific `vm_compute` obligations は trusted proof core から外れる。

### defaults

- generated artifact format の default は Rocq `.v` とする。
- Haskell は generic certificate record の concrete `Definition` 群を出力する。
- Rocq 側で JSON parsing / decoding は行わない。
- first target は uniprocessor zero-offset periodic EDF に限定する。
- migration は additive に進める。
  - generic layer を追加
  - soundness を証明
  - tutorial を adapter 化
  - Haskell が generated Rocq certificate file を出力
  - その後で local compute theorem を retire

## 2026-04-22 Progress (Generic periodic EDF certificate/checker layer)

### 追加したもの

- common periodic layer に generic certificate/checker file を追加した。
  - `theories/TaskModels/Periodic/PeriodicEDFCertificate.v`
  - `theories/TaskModels/Periodic/PeriodicEDFCertificateSoundness.v`
- generic extraction-friendly record を導入した。
  - `EDFPrefixCert`
  - `EDFTransportClass`
  - `EDFTransportCert`
  - `EDFDBFCert`
  - `EDFInfiniteCert`
- generic boolean checker を導入した。
  - `check_prefix_cert`
  - `check_transport_cert`
  - `check_dbf_cert`
  - `check_edf_infinite_cert`
- field decomposition と lookup-oriented structural lemma を追加した。
  - `check_*_fields`
  - basis / backlog row / transport class / DBF table の `nth_error` structural facts

### 今回の意味

- Haskell offload の target になる common-layer schema が、tutorial-local record ではなく
  generic periodic EDF interface として固定された。
- この段階ではまだ schedule semantics への full soundness は入れていないが、
  後続で generic proof を載せるための table shape / lookup fact は共通層に移った。
- tutorial file はまだ旧来の concrete schema を使ってよく、migration は additive に進められる。
- Haskell が最終的に target にする artifact format は JSON ではなく、
  generic certificate record を直接 instantiate する Rocq source file である。

### まだ残っているもの

- generic checker soundness theorem はまだ未実装である。
- tutorial はまだ generic certificate layer へ migrate していない。
- current tutorial-specific `vm_compute` obligations はまだ proof core から外れていない。

### 次の作業

1. common layer で generic prefix / transport / DBF checker の semantic soundness を証明する。
2. `Tutorials/EDFInfiniteSchedulability.v` を generic certificate layer の concrete instantiation に寄せる。
3. その後で Haskell-generated Rocq certificate file を tutorial に import させる。
4. tutorial-specific `vm_compute` obligations を generated Rocq certificate validation へ落とす。

## 2026-04-22 Progress (Generic semantic soundness for periodic EDF certificates)

### 追加したもの

- `PeriodicEDFCertificateSoundness.v` に、generic checker へ semantic meaning を与える layer を追加した。
- common-layer assumption record を導入した。
  - `EDFPrefixCertSemantics`
  - `EDFTransportCertSemantics`
  - `EDFDBFCertSemantics`
- generic semantic soundness theorem を追加した。
  - `check_prefix_cert_semantic_sound`
  - `check_transport_cert_semantic_sound`
  - `check_dbf_cert_semantic_sound`
  - `check_edf_infinite_cert_semantic_sound`
- これらを支える common lookup lemma も追加した。
  - `nth_error_exists_of_lt`
  - basis / backlog row / transport class / DBF table lookup から semantic predicate を引く補題群

### 今回の意味

- generic periodic EDF certificate/checker layer は now 単なる table-shape validator ではなく、
  prefix / transport / DBF witness が何を意味するかを common layer で表現できるようになった。
- まだ final generated EDF theorem へ直結する fully packaged interface ではないが、
  tutorial-local `EDFInfiniteCertEx` から generic layer へ移るための semantic target は揃った。
- これにより Haskell offload の trusted boundary は、
  tutorial file ではなく common periodic EDF layer に置ける見通しが立った。
- artifact story も JSON decoder を挟まず、generated Rocq source file を直接 import する形へ
  収束させられる見通しが立った。

### まだ残っているもの

- tutorial はまだ旧来の concrete schema と checker path を使っている。
- `Tutorials/EDFInfiniteSchedulability.v` 側の
  - `EDFInfiniteCertEx`
  - `check_edf_infinite_cert_ex`
  - `cert_ex_ok`
  - tutorial-specific `vm_compute` obligations
  はまだ generic layer に migrate していない。
- `PeriodicEDFConcreteInfiniteClassicalObligations` もまだ generic certificate checker を consume しない。

### 次の作業

1. `Tutorials/EDFInfiniteSchedulability.v` を generic certificate layer の concrete instantiation に寄せる。
2. tutorial-specific checker path を generic `check_edf_infinite_cert` 系へ置き換える。
3. Haskell が tutorial task set 用の generated Rocq `.v` certificate file を出力する。
4. その後で `cert_ex_ok`、`generated_prefix_slot_ex`、`periodic_classical_dbf_test_by_cutoff_ex` を
   generated Rocq certificate validation へ落とす。

## 2026-04-23 Plan (Generated Rocq certificate files, not JSON)

### 出力形式の修正

- Haskell が出力する証明証 artifact の canonical format は JSON ではなく Rocq `.v` とする。
- Haskell は generic periodic EDF certificate record を直接 instantiate する
  concrete `Definition` 群を出力する。
- Rocq 側で JSON parser / decoder / decoder correctness は持たない。

### なぜ Rocq `.v` を選ぶか

- `Require Import` でそのまま proof input にできる。
- parser / decoder correctness という別レイヤを増やさずに済む。
- generated artifact を diff review しやすい。
- trusted boundary を
  - generic certificate 型
  - generic checker
  - generic semantic soundness
  に集中させられる。

### generated Rocq file の想定

- generated file は data-only とする。
- 含めるのは
  - `EDFPrefixCert`
  - `EDFTransportCert`
  - `EDFDBFCert`
  - `EDFInfiniteCert`
  の concrete inhabitant 定義のみ。
- theorem / proof script / `Admitted.` は含めない。
- 生成先は generated subdirectory を想定する。
  - 例: `Tutorials/Generated/`

### migration への影響

- tutorial migration の次の実装単位は、
  generated Rocq certificate file を import する path を作ることである。
- `cert_ex_ok` の役割は、将来的には handwritten concrete theorem ではなく、
  imported generated Rocq certificate に対する checker acceptance theorem へ置き換わる。
- `generated_prefix_slot_ex` と `periodic_classical_dbf_test_by_cutoff_ex` も同様に、
  local compute theorem ではなく generated Rocq certificate を支える local semantic lemma へ
  後退する。

### defaults

- artifact format の default は Rocq `.v`
- one task set / one generated Rocq file
- deterministic pretty-print
- checked-in generated file か reproducible generation のどちらかを採るが、
  Rocq 側は generated `.v` を直接 consume する

## 2026-04-23 Progress (Imported generated Rocq certificate for the EDF infinite tutorial)

### 追加したもの

- `Tutorials/Generated/EDFInfiniteSchedulabilityCert_ex.v` を追加した。
- generated file には data-only definition を置いた。
  - generic prefix certificate data
  - generic transport certificate data
  - generic DBF certificate data
  - `cert_ex_generic : EDFInfiniteCert JobId`
- `_CoqProject` に generated file 用の logical path を追加した。
  - `-Q Tutorials/Generated Tutorials.Generated`
- `Tutorials/EDFInfiniteSchedulability.v` は generated Rocq certificate file を import するようにした。
- tutorial には generic checker acceptance theorem を追加した。
  - `cert_ex_generic_ok`
- tutorial には generic semantic adapter を追加した。
  - `cert_ex_prefix_semantics`
  - `cert_ex_transport_semantics`
  - `cert_ex_dbf_semantics`
  - `cert_ex_generic_semantic_sound`
- extraction target は old local checker ではなく generic checker / generic certificate に切り替えた。

### 今回の意味

- Haskell offload の concrete artifact story は now JSON ではなく
  checked-in generated Rocq `.v` file として tutorial に接続された。
- tutorial の concrete witness data は handwritten local constants ではなく、
  imported generated certificate data を source-of-truth にする方向へ進んだ。
- generic checker / semantic soundness layer は now tutorial から実際に consume される境界になった。

### まだ残っているもの

- final backlog-free theorem path 自体はまだ tutorial-local legacy checker soundness を adapter として使っている。
- したがって
  - `check_edf_infinite_cert_ex_sound`
  - `generated_edf_backlog_free_before_release_ex_proved`
  まわりの local proof core はまだ完全には retire していない。
- `periodic_classical_dbf_test_by_cutoff_ex` や `generated_prefix_slot_ex` も、
  まだ local semantic support lemma として残っている。

### 次の作業

1. `generated_edf_backlog_free_before_release_ex_proved` の最終経路から
   legacy `check_edf_infinite_cert_ex_sound` を外す。
2. generic transport witness から tutorial-local lasso bridge を直接回収する adapter theorem を作る。
3. その後で old local certificate/checker schema と
   `vm_compute`-heavy support theorem 群を proof core から retire する。

## 2026-04-23 Progress (Final theorem path no longer goes through the legacy checker theorem)

### 変更したもの

- `generated_edf_backlog_free_before_release_ex_proved` は
  `check_edf_infinite_cert_ex_sound` を経由しないようにした。
- final backlog-free theorem は now
  `generated_edf_backlog_free_before_release_ex_from_certified_prefix_and_lasso cert_ex cert_ex_ok`
  を直接使う。

### 今回の意味

- tutorial の final theorem path から、legacy checker theorem
  `check_edf_infinite_cert_ex_sound` への依存は外れた。
- imported generated Rocq certificate が source-of-truth になった状態で、
  final theorem path は legacy checker theorem ではなく
  legacy prefix/lasso adapter theorem を直接使う段階まで整理できた。

### まだ残っているもの

- final path は still
  `generated_edf_backlog_free_before_release_ex_from_certified_prefix_and_lasso`
  に依存している。
- したがって generic semantic soundness から tutorial-local lasso bridge を
  直接回収する adapter theorem はまだ未実装である。

### 次の作業

1. `generated_edf_backlog_free_before_release_ex_from_certified_prefix_and_lasso`
   を generic imported-certificate path から置き換える。
2. その後で old local checker theorem / schema / compute-heavy support lemma 群を
   proof core から retire する。

## 2026-04-23 Progress (Generic transport witness now drives the final lasso path)

### 変更したもの

- generated Rocq certificate file の transport data を later-period representative basis 用に強めた。
  - `transport_basis_jobs` は recurrence basis に絞った。
  - `transport_job_shift` は all-zero ではなく task0/task1 の actual shift data を持つようにした。
- tutorial 側の `cert_ex_transport_witness` を強化した。
  - representative job
  - shift
  - completion offset
  - backlog offset
  を witness として持つようにした。
- generic imported-certificate path から later-period backlog-free を導く新しい theorem 群を追加した。
  - `generated_edf_backlog_free_before_release_ex_task0_generic_transport`
  - `generated_edf_backlog_free_before_release_ex_task1_generic_transport`
  - `generated_edf_backlog_free_before_release_ex_from_generic_prefix_and_transport`
- `generated_edf_backlog_free_before_release_ex_proved` は now
  `generated_edf_backlog_free_before_release_ex_from_generic_prefix_and_transport`
  を使う。

### 今回の意味

- final backlog-free theorem path は now
  legacy lasso theorem family
  - `generated_edf_backlog_free_before_release_ex_task0_lasso`
  - `generated_edf_backlog_free_before_release_ex_task1_lasso`
  - `generated_edf_backlog_free_before_release_ex_from_certified_prefix_and_lasso`
  に依存しない。
- generic imported certificate の transport witness が、later-period bridge の
  proof-core path に入った。
- common-layer transport schema は既存の table shape のままで足り、
  ボトルネックは schema ではなく generated data と tutorial adapter の弱さだったことが確認できた。

### まだ残っているもの

- proof core は still local support lemma として
  - `cert_ex_ok`
  - `generated_edf_backlog_free_before_release_ex_from_certified_prefix_first_period`
  - `certified_completion_time_ex` / `certified_backlog_time_ex` 周辺
  を使っている。
- old local checker/schema 自体は file からまだ削除していない。

### 次の作業

1. old local certificate/checker schema を proof core から完全に切り離す。
2. `cert_ex_ok` と prefix/DBF の local compute-heavy support lemma を
   generic imported-certificate validation へ整理し直す。
3. その後で legacy local checker theorem / schema を retire する。

## 2026-04-23 Progress (Old local checker/schema removed from the active proof core)

### 変更したもの

- tutorial の first-period branch に、
  `generated_edf_backlog_free_before_release_ex_from_generic_prefix_first_period`
  を追加した。
  これは old local checker decomposition ではなく、
  imported generic prefix certificate とその semantic soundness から
  backlog-free を回収する。
- `generated_edf_backlog_free_before_release_ex_task0_generic_transport` と
  `..._task1_generic_transport` は、
  `check_edf_infinite_cert_ex_fields cert_ex cert_ex_ok` から
  lasso fact を取り出すのをやめ、
  `cert_ex_periodic_lasso_ok` を使う形に差し替えた。
- `generated_edf_backlog_free_before_release_ex_from_generic_prefix_and_transport`
  の first-period branch は now
  `generated_edf_backlog_free_before_release_ex_from_generic_prefix_first_period`
  を使う。

### 今回の意味

- active proof path は now
  - `cert_ex_ok`
  - `check_edf_infinite_cert_ex_fields`
  - `check_edf_infinite_cert_ex_sound`
  に依存しない。
- imported generated generic certificate と、その semantic soundness が
  tutorial proof core の唯一の active certificate boundary になった。
- old local checker/schema は file 内に残っていても、
  役割は legacy scaffolding に縮退した。

### まだ残っているもの

- old local checker/schema definitions 自体は file にまだ残っている。
- `periodic_classical_dbf_test_by_cutoff_ex` や
  `certified_completion_time_ex` / `certified_backlog_time_ex` 周辺の
  heavy support lemma は still file に残っている。
- compile time の観点では、legacy lemma family を別ファイルへ隔離するか、
  不要部分を物理削除する余地がまだある。

### 次の作業

1. old local checker/schema definition 群を物理削除するか、
   少なくとも legacy file へ隔離して tutorial compile path から外す。
2. `periodic_classical_dbf_test_by_cutoff_ex` など、
   まだ残る heavy support lemma を generated generic certificate 側へ
   さらに寄せる。
3. その後で、別 task set 向け generated Rocq certificate を増やして
   genericity を実証する。

## 2026-04-23 Progress (Physical deletion of the old local checker/schema and heavy legacy lemma family)

### 変更したもの

- `Tutorials/EDFInfiniteSchedulability.v` から、old local certificate/checker schema を
  物理削除した。
  - `EDFPrefixCertEx`
  - `EDFInfiniteCertEx`
  - `cert_ex`
  - `check_prefix_*_ex`
  - `check_periodic_lasso_ex`
  - `check_edf_infinite_cert_ex`
  - `cert_ex_ok`
  - `check_*_fields`
  - `check_*_sound`
- old checker にぶら下がっていた heavy legacy lemma family も削除した。
  - `certified_completion_time_ex`
  - `certified_backlog_time_ex`
  - `completed_at_certified_completion_time_ex`
  - structural completion bridge 群
  - old lasso bridge theorem family
- later-period bridge は、
  imported generic certificate と completion-target helper 群だけを使う形へ
  整理した。
- DBF 側の active path も、
  renamed local fact
  - `cert_ex_dbf_test_by_cutoff_true`
  - `cert_ex_dbf_full_sound`
  に整理し、old local checker path への参照を消した。

### 今回の意味

- tutorial は now 一つの concrete proof boundary だけを持つ。
  - generated Rocq certificate
  - `check_edf_infinite_cert`
  - `cert_ex_generic_ok`
  - `cert_ex_generic_semantic_sound`
- old local checker/schema は、proof core から外れたのではなく、
  file からも削除された。
- compile-time のボトルネックは now
  old checker/schema の二重管理ではなく、
  残っている tutorial-local semantic support lemma の重さに絞られた。

### まだ残っているもの

- tutorial file には still completion-target 系の support lemma が残っている。
  これらは old certificate boundary ではないが、保守性や compile time の観点では
  将来分割候補である。
- generated Rocq certificate pipeline の genericity は、
  現時点では tutorial task set でしか実証していない。

### 次の作業

1. completion-target 系の remaining support block を、
   必要なら別 file に分離して compile-time 影響を局所化する。
2. 別 task set 向け generated Rocq certificate を追加し、
   same generic schema で再利用できることを確認する。
3. 必要なら Haskell generator 側の Rocq pretty-printer contract を
   明文化して、generated artifact の再現性を固定する。

## 2026-04-23 Progress (Prefix slots responsibility split and current hotspot)

### 今回の方針整理

- Haskell 側の責務は `Tutorials/Generated/EDFInfiniteSchedulabilityCert_ex.v`
  に出力される generated data の生成に固定する。
  特に、`cert_ex_prefix_slots_data` は generated EDF prefix の
  authoritative data source として扱う。
- Rocq 側の責務は、その generated data が
  `sched_upto_ex 38` の意味論と一致することの証明に固定する。
- ただし現時点では、この意味論的一致の最終入口は still
  tutorial-local proof に残っており、完全な lightweight bridge への
  置換は未完了である。

### 今回の実装

- `generated_prefix_slot_ex` の per-slot `vm_compute` case split をやめ、
  bulk equality 補題
  - `generated_prefix_slots_ex_data_ok`
  とそこからの lookup 補題
  - `generated_prefix_slot_ex`
  の構成へ戻した。
- これにより、
  `certified_service_prefix_ex_data_agrees_generated` と
  `cert_ex_prefix_semantics`
  は引き続き generated prefix data を読む構造を維持した。
- 役割分担としては、
  - Haskell: prefix slots data を生成する
  - Rocq: generated schedule がその data と一致することを証明する
  という境界を明示した。

### 実測結果

- Docker で次を実行した。

```sh
timeout 240s docker exec docker-scheduling_theory-1 zsh -lc \
  'cd /scheduling_theory && rocq compile -time -q -w -deprecated-native-compiler-option -native-compiler no -Q Tutorials/Generated Tutorials.Generated -R theories RocqSched Tutorials/EDFInfiniteSchedulability.v'
```

- `cert_ex_dbf_test_by_cutoff_true` の `vm_compute` は約 `0.014s`
- `cert_ex_generic_ok` の `vm_compute` はほぼ `0s`
- `generated_prefix_slot_ex` の per-slot 版では、
  後半分岐で
  - 約 `3.2s`
  - 約 `48.9s`
  - その次で 70 秒以上無出力
  となり、明確な hotspot だった
- bulk equality に戻した current version では、
  `generated_prefix_slots_ex_data_ok` に入った後、
  少なくとも 70 秒以上 `rocq compile -time` 出力が止まることを確認した

### 現状の結論

- per-slot `vm_compute` は bulk equality より悪い
- しかし bulk equality でも、
  `sched_upto_ex 38` を Rocq 側で丸ごと正規化している限り、
  current hotspot は解消していない
- したがって、
  Haskell/Rocq の責務分離は「data source の分離」としては整理できたが、
  compile-time 改善のための最終段としては、
  `generated_prefix_slots_ex_data_ok` を置き換える
  semantic bridge が still 必要である

### 次の具体作業

1. `generated_prefix_slots_ex_data_ok` を直接使わずに済む、
   prefix-slot 一致専用の semantic bridge を導入する
2. その bridge は
   `cert_ex_prefix_semantics` と `cert_ex_generic_semantic_sound` の
   循環を起こさない順序で配置する
3. その後で `generated_prefix_slot_ex` を
   generated data lookup の薄い補題へ置き換える

## 2026-04-23 Progress (Common-layer prefix bridge helpers and tutorial bridge entry)

### 今回の目的

- hotspot 本体の置換に入る前に、
  generated prefix data を Rocq 側の意味論補題へ接続する
  proof-facing interface を common layer に明示する。
- あわせて tutorial 側にも、
  generated prefix certificate から slot 一致だけを取り出す
  名前付き bridge 入口を追加する。

### 実装したもの

- `theories/TaskModels/Periodic/PeriodicEDFCertificateSoundness.v`
  に、`check_prefix_cert_semantic_sound` の projection helper を追加した。
  - `check_prefix_cert_slots_sound`
  - `check_prefix_cert_completed_by_sound`
  - `check_prefix_cert_backlog_sound`
- これらは、
  `EDFPrefixCertSemantics` から
  - slot 観測
  - completed-by 観測
  - backlog 観測
  を個別に取り出す小さい proof-facing interface である。
- `Tutorials/EDFInfiniteSchedulability.v` には、
  tutorial-specific bridge として
  - `cert_ex_prefix_generic_ok`
  - `cert_ex_prefix_slots_semantic_bridge`
  を追加した。
- これにより、tutorial 側では
  `cert_ex_prefix_semantics`
  と `check_prefix_cert_slots_sound`
  を介して、
  generated prefix certificate から slot 一致を取り出す
  明示的な semantic bridge 入口を持つようになった。

### 検証

- Docker で
  `make theories/TaskModels/Periodic/PeriodicEDFCertificateSoundness.vo`
  は成功した。
- `rg` で上記 helper / bridge 名が導入されたことを確認した。
- tutorial 全体の `rocq compile -time` は、
  current version でも依然として
  `generated_prefix_slots_ex_data_ok`
  に入った後で長時間停止する。

### 意味

- これで、Haskell-generated prefix data を Rocq 側の意味論へ結ぶ
  共通層の public helper は用意できた。
- まだ `generated_prefix_slot_ex` 自体は
  `generated_prefix_slots_ex_data_ok` に依存しているが、
  置換先となる semantic bridge の名前付き入口は確保できた。
- 次の実作業は、
  この新しい bridge を使う順序に証明を並べ替えて、
  `generated_prefix_slots_ex_data_ok` を proof path から外すことである。

### 次の具体作業

1. `generated_prefix_slot_ex` を
   `generated_prefix_slots_ex_data_ok` ではなく
   `cert_ex_prefix_slots_semantic_bridge` ベースに差し替えられるよう、
   tutorial 内の証明順序を組み替える
2. その際、
   `certified_service_prefix_ex_data_agrees_generated`
   と `cert_ex_prefix_semantics`
   の依存を再分解して循環を避ける
3. 差し替え後に `rocq compile -time` を再測定し、
   新しい hotspot を記録する

## 2026-04-23 Progress (Prefix semantics decomposition before slot-bridge swap)

### 今回の目的

- `generated_prefix_slots_ex_data_ok` をすぐには除去できない状態でも、
  `cert_ex_prefix_semantics` 全体を 1 本の monolithic proof にしたままでは
  slot bridge の差し替えがしづらい。
- そのため今回の次タスクでは、
  prefix semantics を
  - slots
  - completed-by
  - backlog
  の 3 成分に明示的に分解し、
  後続の slot-only refactor が局所化される構造へ組み替えることを目的とした。

### 実装したもの

- `Tutorials/EDFInfiniteSchedulability.v` に、
  `cert_ex_prefix_semantics` の構成要素として次の局所補題を追加した。
  - `cert_ex_prefix_slots_sound`
  - `cert_ex_prefix_completed_by_semantics_local`
  - `cert_ex_prefix_backlog_semantics_local`
- `cert_ex_prefix_semantics` は、
  これら 3 補題を束ねるだけの lemma に組み替えた。
- これにより、slot 成分だけを差し替える作業は
  `cert_ex_prefix_slots_sound`
  周辺に閉じる形になり、
  completed-by / backlog 証明への影響を最小化できる構造になった。

### 検証

- `rg` で次を確認した。
  - `generated_prefix_slots_ex_data_ok` はまだ存在する
  - `generated_prefix_slot_ex` もまだそれに依存している
  - 新しい 3 つの局所補題が導入され、
    `cert_ex_prefix_semantics` がそれらを束ねる形になっている
- Docker で次を実行した。

```sh
timeout 120s docker exec docker-scheduling_theory-1 zsh -lc \
  'cd /scheduling_theory && rocq compile -time -q -w -deprecated-native-compiler-option -native-compiler no -Q Tutorials/Generated Tutorials.Generated -R theories RocqSched Tutorials/EDFInfiniteSchedulability.v'
```

- compile-time 出力は
  `Chars 18726 - 18838 [Lemma~generated_prefix_slots_e...]`
  および
  `Chars 18839 - 18845 [Proof.]`
  まで進んだ後、
  少なくとも 70 秒以上無出力のまま停止した。
- したがって current hotspot は依然として
  `generated_prefix_slots_ex_data_ok`
  であり、今回の分解は hotspot 本体の除去ではなく、
  次の差し替え作業のための proof-order 整理である。

### 意味

- Haskell 側 generated data を Rocq 側 semantics に結ぶ責務分離は、
  入口 helper と tutorial bridge 名のレベルでは揃ってきた。
- 今回の分解により、
  `cert_ex_prefix_semantics` 全体を崩さずに
  slot proof だけを入れ替える準備はできた。
- ただし、non-cyclic な slot bridge 自体はまだ未完成であり、
  `generated_prefix_slots_ex_data_ok`
  は active proof path に残っている。

### 次の具体作業

1. `cert_ex_prefix_slots_sound` のみを新しい入口にして、
   `generated_prefix_slot_ex` から bulk equality 依存を外す
2. そのために必要なら、
   common layer 側には slot-only の前提で使える最小補題だけを追加する
3. 差し替え後に `generated_prefix_slots_ex_data_ok` と
   `nth_map_seq` を削除し、
   `rocq compile -time` の新しい hotspot を再記録する

## 2026-04-23 Progress (Bulk slot equality removed, new stall moved earlier)

### 今回の目的

- `generated_prefix_slots_ex_data_ok` による
  whole-list `vm_compute` を active proof path から外し、
  generated prefix slots を explicit prefix witness として使う形へ
  置き換えることを試みた。
- 同時に、以後の slot proof が
  generated certificate data を witness として使えるよう、
  generic な prefix-agreement 補題を common layer に追加した。

### 今回の実装

- `theories/Uniprocessor/Generic/FinitePrefixScheduleWitness.v`
  に次を追加した。
  - `local_scheduler_matches_generated_schedule_prefix`
- この補題は、
  global `scheduler_rel` を最初から持たなくても、
  有限 horizon `H` までの local choose 一致と
  other-CPU idle を示せれば、
  explicit schedule が `generated_schedule_prefix` と
  prefix 一致することを与える。
- `Tutorials/EDFInfiniteSchedulability.v` では、
  old hotspot だった
  - `generated_prefix_slots_ex_data_ok`
  - `nth_map_seq`
  を削除した。
- 代わりに次を導入した。
  - `cert_candidates_ex_38`
  - `cert_prefix_sched_ex`
  - `cert_candidates_ex_38_spec`
  - `cert_prefix_sched_ex_choose_agrees_before`
  - `cert_prefix_sched_ex_local_scheduler`
- `generated_prefix_slot_ex` は、
  generated slots list を explicit prefix witness として
  `local_scheduler_matches_generated_schedule_prefix`
  から導く形へ差し替えた。

### 静的確認

- `rg` で次を確認した。
  - `generated_prefix_slots_ex_data_ok` は削除済み
  - `nth_map_seq` は削除済み
  - `generated_prefix_slot_ex` は残っている
  - `generated_prefix_slot_ex` は bulk equality を参照していない

### 実測結果

- Docker で common layer の compile は通った。

```sh
docker exec docker-scheduling_theory-1 zsh -lc \
  'cd /scheduling_theory && make theories/Uniprocessor/Generic/FinitePrefixScheduleWitness.vo'
```

- `rocq compile -time` で tutorial を再観測した。

```sh
timeout 180s docker exec docker-scheduling_theory-1 zsh -lc \
  'cd /scheduling_theory && rocq compile -time -q -w -deprecated-native-compiler-option -native-compiler no -Q Tutorials/Generated Tutorials.Generated -R theories RocqSched Tutorials/EDFInfiniteSchedulability.v'
```

- 観測では、
  old hotspot だった `generated_prefix_slots_ex_data_ok` には到達する前に、
  `cert_candidates_ex_38_spec` の末尾付近まで進んだ後で
  少なくとも 90 秒以上無出力となった。
- compile-time 出力が最後に進んだのは、
  `cert_candidates_ex_38_spec` proof 中の
  `Chars 19359 - 19368 [exact~Hj.]`
  までである。

### 現状の結論

- `generated_prefix_slots_ex_data_ok` による
  whole-list `vm_compute` stall は active proof path から消えた。
- ただし compile-time の長時間停止そのものは解消しておらず、
  現在の停止点は
  `cert_candidates_ex_38_spec`
  付近へ移動している。
- 残っている `vm_compute` の中では、
  次に重い候補は
  `cert_prefix_sched_ex_local_scheduler` 内の
  38-case `vm_compute` 分岐である。
- したがって次の作業は、
  まず `cert_candidates_ex_38_spec` の遅さを切り分け、
  その後 line 713 付近の local witness `vm_compute`
  が新しい principal hotspot かを再観測することになる。

### 次の具体作業

1. `cert_candidates_ex_38_spec` がなぜ長く閉じないかを切り分ける
2. その後、`cert_prefix_sched_ex_local_scheduler` の
   38-case `vm_compute` が新しい hotspot かを再計測する
3. 可能なら、候補列挙 spec を別補題へ分割して
   current stall をさらに前処理側へ押し出す

## 2026-04-23 Progress (Unused bridge removed, `generated_prefix_slot_ex` still needed)

### 今回の確認ポイント

- `generated_prefix_slot_ex` 自体が不要かを参照関係から再確認した。
- 併せて、現在の proof path に不要な wrapper / bridge を削除してから
  tutorial を再実行した。

### 参照関係の結論

- `generated_prefix_slot_ex` の参照は現状 2 箇所だった。
  - `certified_service_prefix_ex_data_agrees_generated`
  - `cert_ex_prefix_slots_sound`
- 一方で、後段に追加していた
  - `cert_ex_prefix_slots_semantic_bridge`
  は参照ゼロで、完全に冗長だった。

### 今回の実施内容

- 削除:
  - `cert_ex_prefix_slots_semantic_bridge`
- 維持:
  - `generated_prefix_slot_ex`
  - `cert_candidates_ex_38`
  - `cert_prefix_sched_ex`
  - `cert_prefix_sched_ex_choose_agrees_before`
  - `cert_prefix_sched_ex_local_scheduler`

`generated_prefix_slot_ex` は、いまの proof-order では
`certified_service_prefix_ex_data_agrees_generated` を支える
早い段階の slot bridge としてまだ必要であり、
単純削除はできなかった。

### 再実行結果

Docker で再度 tutorial compile を実行した。

```sh
docker exec docker-scheduling_theory-1 zsh -lc \
  'cd /scheduling_theory && make Tutorials/EDFInfiniteSchedulability.vo'
```

結果:
- `cert_candidates_ex_38_spec` の軽量化自体は維持されている
- しかし通し compile は依然未完了
- 現在の failure point は
  `certified_service_prefix_ex_data_agrees_generated`
  の proof repair 中である

### 現状の意味

- 「不要な wrapper を消してから再実行する」という切り分けは実施済み
- その結果、
  - 不要だったのは後段の `cert_ex_prefix_slots_semantic_bridge`
  - `generated_prefix_slot_ex` は現状まだ必要
  であることが確認できた

### 次の具体作業

1. `certified_service_prefix_ex_data_agrees_generated` を
   `generated_prefix_slot_ex` に依存したまま安定化する
2. その後に再度 `make Tutorials/EDFInfiniteSchedulability.vo` を回し、
   次の hotspot / failure point を特定する

## 2026-04-23 Progress (`cert_candidates_ex_38_spec` deleted and inlined)

### 今回の実施内容

- `Tutorials/EDFInfiniteSchedulability.v` から
  `cert_candidates_ex_38_spec` を削除した。
- その唯一の残存 use site だった
  `cert_prefix_sched_ex_choose_agrees_before`
  で、candidate-source spec を
  `generated_periodic_edf_enum_candidates_upto_spec`
  の直接適用へ置き換えた。
- `cert_candidates_ex_38`、
  `cert_prefix_sched_ex`、
  残りの witness chain はこの作業では変更していない。

### 静的確認

- `rg` で
  `cert_candidates_ex_38_spec`
  が tutorial から消えていることを確認した。
- `rg` で
  `cert_prefix_sched_ex_choose_agrees_before`
  は残っており、
  `generated_periodic_edf_enum_candidates_upto_spec`
  を直接参照していることを確認した。

### 再実行結果

以下を再実行した。

```sh
timeout 180s docker exec docker-scheduling_theory-1 zsh -lc \
  'cd /scheduling_theory && make Tutorials/EDFInfiniteSchedulability.vo'
```

```sh
timeout 180s docker exec docker-scheduling_theory-1 zsh -lc \
  'cd /scheduling_theory && rocq compile -time -q -w -deprecated-native-compiler-option -native-compiler no -Q Tutorials/Generated Tutorials.Generated -R theories RocqSched Tutorials/EDFInfiniteSchedulability.v'
```

結果:
- `make Tutorials/EDFInfiniteSchedulability.vo` は 180 秒 timeout で未完了だった
- `rocq compile -time` も 180 秒 timeout で未完了だった
- compile-time 出力は削除済みの
  `cert_candidates_ex_38_spec`
  では止まらず、
  いまは
  `cert_prefix_sched_ex_choose_agrees_before`
  の新しい inline proof 内、
  `unfold cert_candidates_ex_38`
  の直後まで進むことを確認した

### 現状の意味

- `cert_candidates_ex_38_spec` は不要な tutorial-local wrapper として
  削除可能だったことが確認できた。
- ただし current blocker は
  `certified_service_prefix_ex_data_agrees_generated`
  へ進む前に、
  まず
  `cert_prefix_sched_ex_choose_agrees_before`
  の inline された candidate-source proof 近辺へ移動した。
- したがって、この段階では blocker は
  もはや deleted wrapper ではないが、
  まだ
  `certified_service_prefix_ex_data_agrees_generated`
  まで compile stream が安定到達していない。

### 次の具体作業

1. `cert_prefix_sched_ex_choose_agrees_before` の inline proof が
   どこで重くなるかをさらに切り分ける
2. その上で tutorial-local wrapper を再導入せずに
   candidate-source proof term の評価負荷を下げる
3. compile stream が再び先へ進んだら、
   次の blocker が
   `certified_service_prefix_ex_data_agrees_generated`
   へ戻るかを再確認する

## 2026-04-23 Progress (Choose-agreement hotspot confirmed necessary and moved)

### 今回の確認ポイント

- `cert_prefix_sched_ex_choose_agrees_before` が
  本当に active proof path 上で必要かを先に調べた。
- 併せて Haskell offload が current blocker を解消できるかも確認した。

### 削除可能性と Haskell offload の結論

- `cert_prefix_sched_ex_choose_agrees_before` は
  現状 `generated_prefix_slot_ex` の唯一の `ChooseAgreesBefore`
  供給元であり、
  `cert_ex_prefix_slots_sound`
  を通じて
  `cert_ex_prefix_semantics`
  と
  `cert_ex_generic_semantic_sound`
  に繋がっている。
- したがって、この段階では単純削除できない。
- さらに、抽出済み Haskell は
  `check_edf_infinite_cert cert_ex_generic`
  の計算側だけを担っており、
  現在の Rocq proof hotspot
  (`ChooseAgreesBefore` / prefix slot semantics bridge)
  を置き換えない。
- よって Haskell offload は今回の principal blocker には効かず、
  方針は
  「削除ではなく proof shape の軽量化」
  に固定した。

### 今回の実施内容

- `cert_prefix_sched_ex_choose_agrees_before` を
  `theories/TaskModels/Periodic/PeriodicEDFInfiniteBridge.v`
  と同じ proof shape に揃えた。
- 具体的には、
  `unfold cert_candidates_ex_38`
  をやめ、
  goal 側を `change` で展開済み candidate source に合わせてから
  `edf_choose_agrees_before`
  を適用する形へ変更した。
- `generated_periodic_edf_enum_candidates_upto_spec`
  は引き続き直接使い、
  tutorial-local wrapper は再導入していない。

### 静的確認

- `rg` で
  `cert_candidates_ex_38_spec`
  が再導入されていないことを確認した。
- `rg` で
  `cert_prefix_sched_ex_choose_agrees_before`
  が残っていることを確認した。
- `rg` で
  `unfold cert_candidates_ex_38`
  が消え、
  `generated_periodic_edf_enum_candidates_upto_spec`
  の直接使用が維持されていることを確認した。

### 再実行結果

以下を再実行した。

```sh
docker exec docker-scheduling_theory-1 zsh -lc \
  'cd /scheduling_theory && make Tutorials/EDFInfiniteSchedulability.vo'
```

```sh
timeout 180s docker exec docker-scheduling_theory-1 zsh -lc \
  'cd /scheduling_theory && rocq compile -time -q -w -deprecated-native-compiler-option -native-compiler no -Q Tutorials/Generated Tutorials.Generated -R theories RocqSched Tutorials/EDFInfiniteSchedulability.v'
```

結果:
- `rocq compile -time` は
  `cert_prefix_sched_ex_choose_agrees_before`
  を即座に通過し、
  `generated_prefix_slot_ex`
  とその後続の補題群も通過した
- 新しい failure point は
  `certified_service_prefix_ex_data_agrees_generated`
  に戻った
- `make Tutorials/EDFInfiniteSchedulability.vo` も同じ箇所で失敗した
- 失敗位置は
  `Tutorials/EDFInfiniteSchedulability.v`
  line 947 付近で、
  `certified_service_prefix_ex_data_agrees_generated`
  の現在の `do 39 ... vm_compute` proof が
  `nat` と `eqb` 由来の計算形をうまく揃えられていない

### 現状の意味

- `cert_prefix_sched_ex_choose_agrees_before` は
  active path 上で必要な補題だと確認できた
- ただし hotspot としては解消済みで、
  principal blocker は再び
  `certified_service_prefix_ex_data_agrees_generated`
  に戻った
- したがって、次タスクは
  service-prefix 証明の repair に進んでよい

### 次の具体作業

1. `certified_service_prefix_ex_data_agrees_generated` の
   現 `vm_compute` proof を、
   `generated_prefix_slot_ex`
   を使う安定な形へ戻すか、
   あるいは計算形を揃える補助 rewrite を入れて修復する
2. その後に再度 tutorial compile を回し、
   次の failure point を特定する
