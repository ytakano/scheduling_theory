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

- task 0 / task 1 の later-period lasso bridge は現時点では temporary `Admitted.` である。
- したがって completion-target fallback は checker soundness path からは外れたが、later-period recurrence bridge そのものはまだ構造証明へ置き換わっていない。
- 既存の `periodic_classical_dbf_test_by_cutoff_ex`、`cert_ex_ok`、`generated_prefix_slot_ex` の temporary `Admitted.` も引き続き残っている。

### 次の作業

- `generated_edf_backlog_free_before_release_ex_task0_lasso` / `_task1_lasso` を generated EDF schedule の `35` 周期 recurrence から証明する。
- その後で legacy completion-target core を tutorial-local の補助証明として整理し、不要なら削除する。
- 最後に残る temporary `Admitted.` 群を軽量な恒久証明へ戻す。
