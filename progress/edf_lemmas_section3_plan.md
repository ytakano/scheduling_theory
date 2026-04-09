# Proof Plan: EDFLemmas Section 3 — Bridge / EDF の prefix 安定性

## Goal

`theories/UniPolicies/EDFLemmas.v` の Section 3 を実装する。
Section 2 の `agrees_before` 系補題を基盤に、`candidates_of`・`choose_edf`・`dispatch` の
prefix 安定性を証明する。

## Proof Strategy

- `agrees_before s1 s2 t` があれば `service_job` が等しく (Section 2)、
  `eligibleb` も等しくなる → `choose_edf` (= filter + min_dl_job) も等しくなる。
- `candidates_of` の prefix 安定性は `CandidateSourceSpec.candidates_prefix_extensional` で保証。
- `edf_dispatch_agrees_before` は両者を合成。

## Proposed Lemmas

- [x] `eligibleb_agrees_before` (helper)
- [x] `candidates_of_agrees_before` (3-1)
- [x] `choose_edf_agrees_before` (3-2)
- [x] `edf_dispatch_agrees_before` (3-3)

## Proof Order

1. `eligibleb_agrees_before`
2. `candidates_of_agrees_before`
3. `choose_edf_agrees_before`
4. `edf_dispatch_agrees_before`
