# Phase D-3 実行記録

## Status

Done

## Goal

`Multicore/Common` を、後続の Awkernel refinement が依存できる
placement / migration / top-`m` placement boundary まで引き上げる。

このタスクの焦点は共通 semantic layer の補強であり、
`Operational/Awkernel` や `Analysis/Multicore` の拡張ではない。

## Out of Scope

- `Operational/Awkernel/*` の拡張
- Awkernel state との対応づけ
- executable scheduler -> operational scheduler refinement
- delay / IPI / timer latency
- fairness / tardiness の新解析
- `Analysis/Multicore` への新しい依存追加

## Progress

- D-3a placement invariant 追加: Done
  - 追加: `theories/Multicore/Common/PlacementFacts.v`
  - `schedule_respects_admissibility` を導入した
  - `running_on_admissible_cpu` を追加した
  - `valid_schedule` と組み合わせて
    `running_implies_admissible_somewhere_under_respect` を追加した
  - `all_cpus_admissible` の自明 wrapper と
    `singleton_admissibility` の confinement 補題を追加した

- D-3b migration invariant 追加: Done
  - 追加: `theories/Multicore/Common/MigrationFacts.v`
  - `migrates_between` を abstract schedule 上で定義した
  - `migration_respects_admissibility` を追加した
  - singleton placement respect から
    cross-CPU migration が起きない補題を追加した

- D-3c machine-full / running-set facts 補強: Done
  - 追加: `theories/Multicore/Common/RunningSetFacts.v`
  - `total_cpu_service_at_eq_m_implies_machine_full_at` を追加した
  - `machine_full_at <-> total_cpu_service_at = m` を public wrapper にした
  - `some_cpu_idle <-> ~ machine_full_at` を追加した
  - `running_set_at_intro` / `running_set_at_elim` を追加した

- D-3d top-m placement-aware boundary 追加: Done
  - 追加: `theories/Multicore/Common/TopMPlacementFacts.v`
  - `TopMPlacementSpec` を導入した
  - `top_m_algorithm_respects_admissibility` を追加した
  - `all_cpus_top_m_placement_spec` を追加した
  - restricted affinity 側は interface のみで止めた

- D-3e entry point と例の更新: Done
  - 更新: `_CoqProject`
  - 更新: `theories/Multicore/Common/MulticoreSemanticsEntryPoints.v`
  - 更新: `theories/Examples/AffinityExamples.v`
  - 例として次を追加した
    - all-cpus placement は常に成立する
    - singleton placement は assigned CPU に閉じる
    - singleton placement 下では cross-CPU migration が起きない
    - top-`m` placement spec から schedule placement invariant が出る

## Main Result

`Multicore/Common` は、既存の admissibility-aware candidate source / top-`m`
selection boundary に加えて、

- schedule-level placement invariant
- abstract migration/admissibility compatibility
- machine-full と machine supply の往復 wrapper
- top-`m` position-aware placement boundary

を持つようになった。

これにより、Awkernel 側で後から満たすべき placement-aware obligation を、
OS 実装依存の前に共通層として固定できた。

## Files Added / Updated

- 追加: `theories/Multicore/Common/PlacementFacts.v`
- 追加: `theories/Multicore/Common/MigrationFacts.v`
- 追加: `theories/Multicore/Common/RunningSetFacts.v`
- 追加: `theories/Multicore/Common/TopMPlacementFacts.v`
- 更新: `_CoqProject`
- 更新: `theories/Multicore/Common/MulticoreSemanticsEntryPoints.v`
- 更新: `theories/Examples/AffinityExamples.v`
- 更新: `plan/roadmap.md`
- 更新: `plan/what_to_prove.md`

## Remaining Hand-off

Phase D 側の残作業は、EDF / LLF wrapper の policy-generic consolidation や
より豊富な affinity 例の追加といった整理作業である。

fairness / interference / operational refinement は次フェーズへ送る。
