# Proof Plan: EDFLemmas Section 2 — Prefix agreement 補題

## Goal

`theories/UniPolicies/EDFLemmas.v` の Section 2 を実装する。
`agrees_before` を定義し、それを使って `service_job`・`completed`・`eligible`・`ready` の
prefix 安定性補題を証明する。

## Key Definitions

```coq
Definition agrees_before (s1 s2 : Schedule) (t : Time) : Prop :=
  forall t' c, t' < t -> s1 t' c = s2 t' c.
```

## Proof Strategy

- `agrees_before` は `CandidateSourceSpec.candidates_prefix_extensional` の前提と一致する。
- `service_job m sched j t` は `[0, t)` の `sched t' c` のみを参照する Fixpoint。
  → `agrees_before s1 s2 t` があれば `service_job m s1 j t = service_job m s2 j t`。
- `completed`, `eligible` は `service_job` 経由で schedule に依存 → 同様に prefix で決まる。
- `running m s j t` は `s t c` を直接参照 → `agrees_before s1 s2 t`（strictly before）では
  `running` の等価性は証明できない。`agrees_before_ready` は `agrees_before s1 s2 (S t)` を使う。

## Proposed Lemmas

- [ ] `agrees_before` (definition)
- [ ] `agrees_before_weaken`: `t1 <= t2 -> agrees_before s1 s2 t2 -> agrees_before s1 s2 t1`
- [ ] `agrees_before_refl`
- [ ] `agrees_before_sym`
- [ ] `agrees_before_trans`
- [ ] `cpu_count_agrees_at` (helper): `(forall c, s1 t c = s2 t c) -> cpu_count m s1 j t = cpu_count m s2 j t`
- [ ] `agrees_before_service_job`: `agrees_before s1 s2 t -> service_job m s1 j t = service_job m s2 j t`
- [ ] `agrees_before_completed`
- [ ] `agrees_before_eligible`
- [ ] `agrees_before_ready` (uses `agrees_before s1 s2 (S t)`)

## Proof Order

1. `agrees_before` (definition)
2. `agrees_before_weaken`
3. `agrees_before_refl`
4. `agrees_before_sym`
5. `agrees_before_trans`
6. `cpu_count_agrees_at`
7. `agrees_before_service_job`
8. `agrees_before_completed`
9. `agrees_before_eligible`
10. `agrees_before_ready`
