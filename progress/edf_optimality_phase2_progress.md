# Proof Progress: EDF Optimality Phase 2 — repair 対象の 2 時刻を固定する

## Status Overview
- Overall: Complete
- Complete Lemmas: 1/1
- Unproven (`Admitted`): none
- Failed/Abandoned Items: none

## Completed Lemmas

### `first_violation_has_repair_witness` (Phase 2, Lemma 4)

Exposes the swap witness pair `(j', t')` from an EDF violation at `(t, j)`.
Fully constructive: no `Classical`, `NNPP`, or `classic` used.

```coq
Lemma first_violation_has_repair_witness :
  forall J (J_bool : JobId -> bool) (candidates_of : CandidateSource)
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched (H : nat) t j,
    (forall x, J_bool x = true <-> J x) ->
    valid_schedule jobs 1 sched ->
    feasible_schedule_on J jobs 1 sched ->
    t < H ->
    sched t 0 = Some j ->
    edf_violation_at_with J candidates_of jobs sched t ->
    exists j' t',
      J j' /\
      eligible jobs 1 sched j' t /\
      job_abs_deadline (jobs j') < job_abs_deadline (jobs j) /\
      t <= t' /\
      t' < job_abs_deadline (jobs j') /\
      sched t' 0 = Some j'.
Proof.
  intros J J_bool candidates_of cand_spec jobs sched H t j
         _HJbool Hvalid Hfeas _HtH Hsched Hviol.
  unfold edf_violation_at_with, edf_violation_at_in in Hviol.
  destruct Hviol as [j0 [j' [_HJj0 [HJj' [Hsched0 [_Hin [Helig Hlt]]]]]]].
  rewrite Hsched in Hsched0.
  injection Hsched0 as Heq. subst j0.
  destruct (eligible_feasible_implies_runs_later_before_deadline
              J jobs sched j' t HJj' Hvalid Hfeas Helig)
      as [t' [Hle [Hlt' Hrun]]].
  exists j', t'.
  split. exact HJj'.
  split. exact Helig.
  split. exact Hlt.
  split. exact Hle.
  split. exact Hlt'.
  exact Hrun.
Qed.
```

## Proof Notes

### Constructive strategy
- `edf_violation_at_with` = `edf_violation_at_in` includes `J j'` in the existential directly,
  so no `candidates_sound` projection needed.
- `eligible_feasible_implies_runs_later_before_deadline` (EDFLemmas, Section 6) is already
  constructive (uses `le_lt_dec`/`lt_dec`). No additional work required.
- `injection Hsched0 as Heq; subst j0` unifies the running job without classical reasoning.

### Dependencies used
- `edf_violation_at_with` / `edf_violation_at_in` — from `EDFLemmas.v`
- `eligible_feasible_implies_runs_later_before_deadline` — from `EDFLemmas.v`

## TODO

(all done)
