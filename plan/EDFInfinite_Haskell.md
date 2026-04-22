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
