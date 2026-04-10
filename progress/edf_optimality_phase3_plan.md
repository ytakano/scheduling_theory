# Proof Plan: EDF Optimality Phase 3 — swap_at の定義と基本補題

## Goal

`plan/edf_optimality.md` § "Phase 3: repair schedule を定義する" の実装。
`theories/UniPolicies/EDFTransform.v` に以下を追加する。

## Proposed Lemmas

- [ ] `swap_at`: 2点入れ替え関数の定義
- [ ] `swap_at_same_outside`: `c≠0 OR (t≠t1 AND t≠t2)` のとき unchanged
- [ ] `swap_at_t1`: `swap_at sched t1 t2 t1 0 = sched t2 0`
- [ ] `swap_at_t2`: `swap_at sched t1 t2 t2 0 = sched t1 0`

## Proof Strategy

- `swap_at_same_outside`: `c` と `t` についての `Nat.eqb` 場合分け。`destruct (Nat.eqb c 0) eqn:Hc` → `destruct (Nat.eqb t t1) eqn:Ht1` → `destruct (Nat.eqb t t2) eqn:Ht2` の順で展開し、矛盾ケースを `Nat.eqb_eq` / `Nat.eqb_neq` で処理する。Constructive のみ。
- `swap_at_t1` / `swap_at_t2`: `unfold swap_at; rewrite Nat.eqb_refl`. `swap_at_t2` で `t2 = t1` の分岐が問題になる場合は `Nat.eqb_sym` を使う。

## Proof Order

1. `swap_at` (定義)
2. `swap_at_same_outside`
3. `swap_at_t1`
4. `swap_at_t2`
