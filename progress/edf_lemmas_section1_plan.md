# Proof Plan: EDFLemmas Section 1 — Service / Completion 補題

## Goal

`theories/UniPolicies/EDFLemmas.v` を新設し、Section 1 の定義・補題をすべて証明する。

## Proof Strategy

大半は `unfold` + `lia` / `tauto` で完結する簡単な補題。
`service_before_release_zero` のみ t に関する帰納法が必要。

## Proposed Lemmas

- [ ] `service_between` (definition)
- [ ] `completed_iff_service_ge_cost`
- [ ] `not_completed_iff_service_lt_cost`
- [ ] `missed_deadline_iff_not_completed_at_deadline`
- [ ] `missed_deadline_iff_service_lt_cost_at_deadline`
- [ ] `service_between_eq`
- [ ] `service_between_0_r`
- [ ] `service_between_refl`
- [ ] `service_between_split`
- [ ] `service_between_nonneg`
- [ ] `service_before_release_zero`
- [ ] `service_at_release_zero`

## Proof Order

1. `service_between` (definition)
2. `completed_iff_service_ge_cost`
3. `not_completed_iff_service_lt_cost`
4. `missed_deadline_iff_not_completed_at_deadline`
5. `missed_deadline_iff_service_lt_cost_at_deadline`
6. `service_between_eq`
7. `service_between_0_r`
8. `service_between_refl`
9. `service_between_split`
10. `service_between_nonneg`
11. `service_before_release_zero`
12. `service_at_release_zero`
