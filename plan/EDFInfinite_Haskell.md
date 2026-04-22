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
- current principal blocker は
  `certified_service_prefix_ex_data_agrees_generated` である。
- ただし blocker は proof 全体ではなく、
 いまはその補題内の `Some j'` / `j = j'` 分岐に局所化されている。
- `change` / `replace` で `service_job` の RHS 1-step 形を固定する方針は試したが、
  final goal には依然として concrete `sched_upto_ex` 展開
  (`match t with 0 | 1 | 5 | ...`) が残る。

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
Lemma certified_service_prefix_ex_data_agrees_generated :
  forall j t,
    t <= 38 ->
    certified_service_prefix_ex cert_ex_prefix_slots_data j t =
    service_job 1 (sched_upto_ex 38) j t.
```

現状:

- 旧安定形の帰納 proof へ戻すところまでは実施済み。
- compile はこの補題まで進み、
  `generated_prefix_slot_ex` を使う帰納 proof には戻っている。
- `Nat.eqb_sym` rewrite failure と単純な `lia` failure は解消した。
- いまの failure は
  `Tutorials/EDFInfiniteSchedulability.v`
  line 958 付近の
  `Some j'` / `j = j'` 分岐で、
  subproof では
  `replace (service_job 1 (sched_upto_ex 38) j' (S t)) with (S (...))`
  を閉じられるが、
  その後の main goal で右辺に concrete `sched_upto_ex` 展開が残り、
  `S (service_job ...)` と一致しないことにある。

次に試すべき既定方針:

- `generated_prefix_slot_ex` を使う帰納 proof は維持する。
- 次は `service_job` の RHS を branch ごとに固定するのではなく、
  main goal 側に残る concrete schedule match を明示的に再束縛する
  (`remember`, `set`, `change`, `pattern`, あるいは branch-local helper lemma) 方針を取る。
- 少なくとも現状の `rewrite generated_prefix_slot_ex` だけでは、
  final goal の concrete `sched_upto_ex` 展開を十分に吸収できない。
- theorem statement や周辺補題は変えない。

変えないもの:

- `cert_candidates_ex_38`
- `cert_prefix_sched_ex`
- `cert_prefix_sched_ex_choose_agrees_before`
- generated certificate interface

## Next Task

1. `certified_service_prefix_ex_data_agrees_generated` 内の
   `Some j'` / `j = j'` 分岐で、
   final goal に残る concrete `sched_upto_ex` 展開全体を再束縛し、
   `service_job` の 1-step 形と同じ surface syntax に合わせる。
2. 修復後に tutorial compile を再実行する。
3. 新しい failure point をこのファイルへ追記する。

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

- `certified_service_prefix_ex_data_agrees_generated` を通過する。
- その後の新しい failure point が分かる。
- 結果をこのファイルに短く追記する。

## History Summary

- generic periodic EDF certificate/checker/soundness layer を common layer に導入した。
- Haskell/外部生成物の受け口は JSON ではなく generated Rocq `.v` file に固定した。
- tutorial は generated certificate file を import する構成へ移行した。
- old local checker/schema と重い legacy support block は active proof core から外した。
- `generated_prefix_slots_ex_data_ok` に依存する bulk slot equality path は削除した。
- その後の stall は `cert_candidates_ex_38_spec` に移り、同 lemma は削除された。
- 次の stall は `cert_prefix_sched_ex_choose_agrees_before` に移ったが、
  proof shape を bridge 側に揃えることで解消した。
- `certified_service_prefix_ex_data_agrees_generated` は旧帰納形へ戻した。
- `rewrite Nat.eqb_sym` failure は解消した。
- `change` / `replace` で `service_job` の RHS 1-step 形を固定する方針も試した。
- それでも principal blocker は同補題内の
  `Some j'` / `j = j'` 分岐での concrete `sched_upto_ex` 展開残りにある。
