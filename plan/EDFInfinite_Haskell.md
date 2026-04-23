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
- `cert_ex_prefix_backlog_matrix_release_lt` と
  `cert_ex_prefix_backlog_matrix_completed_true` は residual branch を潰して通過済み。
- `cert_ex_prefix_backlog_row_exists` と
  `cert_ex_prefix_backlog_matrix_true_of_release_order` も finite-table proof に直して通過済み。
- `cert_ex_transport_witness` の括弧不足は修正済み。
- `cert_ex_transport_lookup_sound` は theorem statement を transport layer に寄せて通過済み。
- `cert_ex_transport_basis_contains_task0_rep` /
  `cert_ex_transport_basis_contains_task1_rep` は generated transport basis list に合わせて
  witness index を修正済み。
- current principal blocker は transport basis containment 修正後の再検証待ち。

## Stable Decisions

- `cert_candidates_ex_38_spec` は戻さない。
- `cert_prefix_sched_ex_choose_agrees_before` と `generated_prefix_slot_ex` は現時点で必要。
- Haskell offload は current proof blocker の解決策ではない。
- generated finite data を読む補題は、必要なら brittle な `vm_compute + repeat inversion`
  ではなく finite-table proof に寄せる。

## Current Blocker

対象補題:

```coq
Lemma cert_ex_prefix_backlog_matrix_true_of_release_order :
  forall i row j ji jj,
    nth_error cert_ex_prefix_backlog_matrix_data i = Some row ->
    nth_error cert_ex_prefix_basis_jobs_data i = Some ji ->
    nth_error cert_ex_prefix_basis_jobs_data j = Some jj ->
    job_release (jobs_ex jj) < job_release (jobs_ex ji) ->
    nth_error row j = Some true.
```

現状:

- `Hrow`, `Hji`, `Hjj` は `vm_compute` と inversion で正規化できる。
- `j` の有限列挙に入るところまでは進んでいる。
- しかし compile は line 1181 の branch tail で止まる。
- exact failure は `reflexivity || lia || exfalso; lia` でも閉じない branch が残ること。
- つまり blocker は release-order の arithmetic 自体ではなく、
  正規化後の goal を `nth_error row j = Some true` へ落とし切れていない proof shape にある。

次に試すべき既定方針:

- `cert_ex_prefix_backlog_matrix_true_of_release_order` は
  `cert_ex_prefix_backlog_matrix_release_lt` と同じ explicit finite-table proof に寄せて通過した。
- その後、transport layer に入って
  `cert_ex_transport_lookup_sound` の statement が `prefix_basis_jobs` を参照していたのを
  `transport_basis_jobs cert_ex_transport_generic` へ修正した。
- latest observed blocker は
  `cert_ex_transport_basis_contains_task0_rep` line 1233 の witness mismatch
  (`Some 2` vs `Some 1`) だった。
- task0/task1 の witness index は
  transport basis list `[0;1;2;3;4;5;6;7;8;9;10;12]` に合わせて
  task0: `0,2,4,6,8,10,11`
  task1: `1,3,5,7,9`
  へ修正済み。
- この修正後の full compile はまだ再検証中で、次の exact blocker は未確定。

## Next Task

1. transport basis containment 修正後の Docker compile を最後まで回し、next blocker を確定する。
2. もし transport 系の次補題で止まるなら、same finite-table style で局所修復する。
3. このメモを事実ベースで更新する。

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
- backlog matrix lookup lemmas を finite-table proof に寄せ、`release_lt` / `completed_true` /
  `row_exists` / `true_of_release_order` を通過させた。
- transport witness 定義の括弧不足を修正し、`cert_ex_transport_lookup_sound` の statement を
  transport layer に戻した。
- transport basis containment 補題の witness index を generated list に合わせて修正し、
  現在はその後の full compile の next blocker 確定待ちである。
