# EDF infinite tutorial handoff note

## Goal

このファイルは `Tutorials/EDFInfiniteSchedulability.v` の current proof state を
次セッションへ引き継ぐための handoff note である。

いまの主題は generic periodic EDF certificate layer の設計ではなく、
generated certificate を使う tutorial proof の残り hotspot を順に潰して
compile を前へ進めることにある。

## Current Status

- generic periodic EDF certificate/checker/soundness layer への移行は完了済み。
- tutorial は `Tutorials/Generated/EDFInfiniteSchedulabilityCert_ex.v` import 構成に移行済み。
- old local checker/schema と bulk slot equality path は active proof core から除去済み。
- `cert_candidates_ex_38_spec` は削除済みで、candidate-source spec は common helper を直接使う。
- `cert_prefix_sched_ex_choose_agrees_before` の hotspot は解消済み。
- `certified_service_prefix_ex_data_agrees_generated` は `service_job_step` と
  `cpu_count_1_some_eq/neq/none` を使う形で通過済み。
- `cert_ex_prefix_completed_by_data_sound` と
  `cert_ex_prefix_completed_by_data_true` は generated finite table の列挙 proof に置き換えて通過済み。
- 未使用だった
  `generated_edf_backlog_free_before_release_ex_from_completion_targets`
  と `_proved` alias は削除済み。
- current principal blocker は `cert_ex_prefix_backlog_matrix_release_lt`。

## Stable Decisions

- `cert_candidates_ex_38_spec` は戻さない。
- `cert_prefix_sched_ex_choose_agrees_before` と `generated_prefix_slot_ex` は現時点で必要。
- Haskell offload は current proof blocker の解決策ではない。
- generated finite data を読む補題は、必要なら brittle な `vm_compute + repeat inversion`
  ではなく finite-table proof に寄せる。

## Current Blocker

対象補題:

```coq
Lemma cert_ex_prefix_backlog_matrix_release_lt :
  forall i row j ji jj,
    nth_error cert_ex_prefix_backlog_matrix_data i = Some row ->
    nth_error row j = Some true ->
    nth_error cert_ex_prefix_basis_jobs_data i = Some ji ->
    nth_error cert_ex_prefix_basis_jobs_data j = Some jj ->
    job_release (jobs_ex jj) < job_release (jobs_ex ji).
```

現状:

- `cert_ex_prefix_basis_job_release_le_38` は finite enumeration に置き換えて通過した。
- `cert_ex_prefix_backlog_matrix_release_lt` と
  `cert_ex_prefix_backlog_matrix_completed_true` は
  `i` 側 (`Hrow`,`Hji`) を先に固定し、そのあと `j` 側 (`Hcell`,`Hjj`) を簡約する
  2 段階 proof shape へ書き換え済み。
- それでも compile は `cert_ex_prefix_backlog_matrix_release_lt` で止まる。
- exact failure shape は、`i` が先頭 row、`j` が 14 以上の residual branch で
  `Hcell : nth_error [] j = Some true`
  と `Hjj : nth_error [] j = Some jj`
  が残り、main script に流れてしまうこと。
- つまり blocker は arithmetic ではなく、
  nested destruct の最後に残る `j` residual branch を局所的に潰し切れていない点にある。

次に試すべき既定方針:

- `cert_ex_prefix_backlog_matrix_release_lt` を explicit finite-branch proof にする。
- 少なくとも residual `j` branch では
  `destruct j; vm_compute in Hcell, Hjj |- *; discriminate`
  を使って impossible case を閉じる。
- その shape が通ったら `cert_ex_prefix_backlog_matrix_completed_true`
  に同じ residual-branch fix を適用する。

## Next Task

1. `cert_ex_prefix_backlog_matrix_release_lt` の residual `j` branch を明示的に潰す。
2. その proof shape を `cert_ex_prefix_backlog_matrix_completed_true` にも適用する。
3. Docker compile を再実行し、next blocker を確定する。
4. このメモを事実ベースで更新する。

再検証コマンド:

```sh
docker exec docker-scheduling_theory-1 zsh -lc \
  'cd /scheduling_theory && make Tutorials/EDFInfiniteSchedulability.vo'
```

```sh
timeout 180s docker exec docker-scheduling_theory-1 zsh -lc \
  'cd /scheduling_theory && rocq compile -time -q -w -deprecated-native-compiler-option -native-compiler no -Q Tutorials/Generated Tutorials.Generated -R theories RocqSched Tutorials/EDFInfiniteSchedulability.v'
```

## History Summary

- generic periodic EDF certificate/checker/soundness layer を common layer に導入した。
- tutorial は generated certificate file import 構成へ移行した。
- old local checker/schema と bulk slot equality path を active proof core から外した。
- `cert_candidates_ex_38_spec` を削除し、common helper 直接利用へ寄せた。
- `cert_prefix_sched_ex_choose_agrees_before` の hotspot を解消した。
- `certified_service_prefix_ex_data_agrees_generated` を修復した。
- `cert_ex_prefix_completed_by_data_sound` / `_true` を finite-table proof に置き換えた。
- 未使用 backlog-free completion-target lemma と `_proved` alias を削除した。
- 現在の stall は backlog matrix generated lookup lemmas に移っている。
