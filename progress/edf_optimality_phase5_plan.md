# Proof Plan: EDF Optimality Phase 5 — swap_at preserves valid_schedule

## Goal
Prove that `swap_at sched t t'` is a valid schedule whenever the original `sched` is valid,
`j` runs at `t`, `j'` runs at `t'`, `j'` is eligible at `t`, `t ≤ t'`,
and `deadline(j') < deadline(j)`.

## Proof Strategy

We prove four lemmas in order:
1. A helper bounding service_job by job_cost in any valid schedule (m=1).
2. Lemma 11: the new front job `j'` is eligible at `t` in the swap schedule.
3. Lemma 12: the new back job `j` is eligible at `t'` in the swap schedule.
4. Lemma 13: the full valid_schedule property is preserved.

### Key insight for Lemma 13 (the tricky case j'' = j', t < t'' < t')
When j' runs at intermediate time t'' ∈ (t, t') in orig, Lemma 10b gives
  `service_swap(j', t'') = service_orig(j', t'') + 1`.
We need this < job_cost. Since j' runs at t'' AND at t' in orig (valid schedule),
and service is monotone, service_orig(j', t'') + 1 ≤ service_orig(j', t'+1?).
More precisely:
- j' runs at t'' → service_orig(j', t''+1) = service_orig(j', t'') + 1
- service_job_monotone: service_orig(j', t''+1) ≤ service_orig(j', t')
- valid_schedule + sched t' 0 = Some j' → ~completed(j',t') → service_orig(j',t') < job_cost
- Combining: service_orig(j', t'') + 1 ≤ service_orig(j', t') < job_cost ✓

All proofs are constructive; no Classical.

## Proposed Lemmas
- [ ] `valid_schedule_1_service_le_cost`: service_job 1 sched j T ≤ job_cost in valid schedule
- [ ] `swap_at_validity_new_front_job` (Lemma 11): eligible j' at t in swap
- [ ] `swap_at_validity_new_back_job` (Lemma 12): eligible j at t' in swap
- [ ] `swap_at_preserves_valid_schedule` (Lemma 13): valid_schedule preserved

## Proof Order
1. `valid_schedule_1_service_le_cost`
2. `swap_at_validity_new_front_job`
3. `swap_at_validity_new_back_job`
4. `swap_at_preserves_valid_schedule`
