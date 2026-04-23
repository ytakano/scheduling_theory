# EDF infinite tutorial handoff note

## Goal

このファイルは、`Tutorials/EDFInfiniteSchedulability.v` の current proof state を
次セッションへ引き継ぐための要約である。

いまの主題は、generic periodic EDF certificate layer への移行自体ではなく、
その移行後に残った tutorial-local proof hotspot を順に潰して、
tutorial file の compile を先へ進めることである。

このメモを読めば、次に触る補題、固定済みの設計判断、再検証コマンドが
すぐ分かる粒度にしてある。

## Current Status

- generic periodic EDF certificate/checker/soundness layer は導入済み。
- tutorial は generated Rocq certificate file
  `Tutorials/Generated/EDFInfiniteSchedulabilityCert_ex.v`
  を import する構成へ移行済み。
- old local checker/schema は active proof core から除去済み。
- bulk slot equality (`generated_prefix_slots_ex_data_ok` / `nth_map_seq`) は削除済み。
- `cert_candidates_ex_38_spec` は削除済みで、candidate-source spec は
  common helper を直接使う形へ移行済み。
- `cert_prefix_sched_ex_choose_agrees_before` の hotspot は解消済み。
- `certified_service_prefix_ex_data_agrees_generated` は通過した。
- この補題では `service_job_step` と `cpu_count_1_some_eq/neq/none` を使う proof shape を採用した。
- `cert_slots_ex_data` はこの補題の前後だけ `Local Transparent` / `Local Opaque` で扱う形にした。
- 未使用だった
  `generated_edf_backlog_free_before_release_ex_from_completion_targets`
  は削除した。
- `generated_edf_backlog_free_before_release_ex_proved` も削除し、
  classical obligations 側は
  `generated_edf_backlog_free_before_release_ex_from_generic_prefix_and_transport`
  を直接参照する形に寄せた。
- current principal blocker は
  `cert_ex_prefix_completed_by_data_sound` である。
- current exact failure は
  `vm_compute` 後の `cert_ex_prefix_completed_by_data` witness が
  `S (job_abs_deadline (jobs_ex j))` と一致せず、
  `t` に `39` が残ることにある。

## Stable Decisions

- `cert_candidates_ex_38_spec` は戻さない。
  common-layer helper
  `generated_periodic_edf_enum_candidates_upto_spec`
  を tutorial で直接使う。
- `cert_prefix_sched_ex_choose_agrees_before` は現時点で必要。
  これは `generated_prefix_slot_ex` の唯一の `ChooseAgreesBefore` 供給元であり、
  `cert_ex_prefix_slots_sound` を通じて prefix semantics に繋がる。
- `generated_prefix_slot_ex` も現時点で必要。
  `certified_service_prefix_ex_data_agrees_generated` と
  `cert_ex_prefix_slots_sound` を支えている。
- Haskell offload は current blocker の解決策ではない。
  抽出済み Haskell は certificate checker の計算側であり、
  いま詰まっている Rocq proof obligation を置き換えない。
- 今やるべき作業は新しい設計追加ではなく、
  tutorial proof repair と stall の前進確認である。

## Current Blocker

対象補題:

```coq
Lemma cert_ex_prefix_completed_by_data_sound :
  forall i j t,
    nth_error cert_ex_prefix_basis_jobs_data i = Some j ->
    nth_error cert_ex_prefix_completed_by_data i = Some t ->
    t = S (job_abs_deadline (jobs_ex j)).
```

現状:

- `certified_service_prefix_ex_data_agrees_generated` は修復済みで、その下流まで compile が進む。
- 新しい failure は
  `Tutorials/EDFInfiniteSchedulability.v` line 1004 付近の
  `cert_ex_prefix_completed_by_data_sound`。
- `vm_compute in Hjob, Htime` 後に残る具体値は
  `cert_ex_prefix_basis_jobs_data = [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 14]`
  と
  `cert_ex_prefix_completed_by_data = [3; 4; 8; 11; 13; 18; 18; 25; 23; 32; 28; 39; 33; 38]`。
- failing branch では `Hjob` が `j = 11` を与え、`Htime` が `t = 39` を与える一方、
  goal は `39 = S (job_abs_deadline (jobs_ex 11))` を要求する。
- ここでは `S (job_abs_deadline (jobs_ex 11)) = 40` になっており、certificate data 側の値が 1 小さい。

次に試すべき既定方針:

- まず generated certificate data の意味を確認する。
- `cert_ex_prefix_completed_by_data` が absolute deadline そのものなのか、
  `S deadline` を意図した列なのかを generated file と checker semantics から再確認する。
- もし data が deadline そのものなら、tutorial lemma statement を
  `t = job_abs_deadline (jobs_ex j)` に合わせるべきかを検討する。
- もし `S deadline` が正しい interface なら、generated data またはその生成元が 1 off になっている。
- 修正点は、まず theorem statement / generated data / checker semantics のどれが責務上正しいかを確定してから選ぶ。

変えないもの:

- `cert_candidates_ex_38`
- `cert_prefix_sched_ex`
- `cert_prefix_sched_ex_choose_agrees_before`
- generated certificate interface

## Next Task

1. `cert_ex_prefix_completed_by_data_sound` の失敗枝を具体化し、
   `j = 11`, `t = 39` で `job_abs_deadline (jobs_ex j)` がいくつになるかを明示確認する。
2. `certified_completed_by_ex` / generated completed-by data の intended meaning を再確認し、
   statement か data のどちらがズレているかを決める。
3. その判断に基づいて局所修正を入れ、tutorial compile を再実行する。
4. 新しい failure point をこのファイルへ追記する。

再検証コマンド:

```sh
docker exec docker-scheduling_theory-1 zsh -lc \
  'cd /scheduling_theory && make Tutorials/EDFInfiniteSchedulability.vo'
```

```sh
timeout 180s docker exec docker-scheduling_theory-1 zsh -lc \
  'cd /scheduling_theory && rocq compile -time -q -w -deprecated-native-compiler-option -native-compiler no -Q Tutorials/Generated Tutorials.Generated -R theories RocqSched Tutorials/EDFInfiniteSchedulability.v'
```

受け入れ基準:

- `cert_ex_prefix_completed_by_data_sound` の責務が明確になる。
- 可能ならこの補題を通過する。
- その後の新しい failure point が分かる。
- 結果をこのファイルに短く追記する。

## History Summary

- generic periodic EDF certificate/checker/soundness layer を common layer に導入した。
- Haskell/外部生成物の受け口は JSON ではなく generated Rocq `.v` file に固定した。
- tutorial は generated certificate file を import する構成へ移行した。
- old local checker/schema と重い legacy support block は active proof core から外した。
- `generated_prefix_slots_ex_data_ok` に依存する bulk slot equality path は削除した。
- その後の stall は `cert_candidates_ex_38_spec` に移り、同 lemma は削除された。
- `certified_service_prefix_ex_data_agrees_generated` は
  `service_job_step` と `cpu_count_1_some_eq/neq/none` を使う形で修復され、compile はその先へ進んだ。
- 未使用の backlog-free completion-target lemma は削除し、
  `_proved` alias も落として direct reference に寄せた。
- 新しい blocker は `cert_ex_prefix_completed_by_data_sound` の completed-by witness mismatch である。
- 次の stall は `cert_prefix_sched_ex_choose_agrees_before` に移ったが、
  proof shape を bridge 側に揃えることで解消した。
- `certified_service_prefix_ex_data_agrees_generated` は旧帰納形へ戻した。
- `rewrite Nat.eqb_sym` failure は解消した。
- `change` / `replace` で `service_job` の RHS 1-step 形を固定する方針も試した。
- その後、`service_job_step` と `cpu_count_1_some_eq/neq/none` へ proof shape を切り替えた。
- 現在の principal blocker は同補題内の
  `Some j'` / `j = j'` 分岐での certificate-side term mismatch
  (`cert_ex_prefix_slots_data` と `cert_slots_ex_data` の surface mismatch) である。
