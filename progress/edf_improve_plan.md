# Proof Plan: EDF Improvement

## Goal

Promote `EDF.v` from a "single dispatch function" to a "reusable policy module" by adding:
- A1: `choose_edf_none_if_no_ready` (opposite direction of Theorem 3)
- A2: `choose_edf_unique_min` (uniqueness / determinism)
- B1: `choose_edf_complete` (explicit precondition, NoDup + ready-set coverage)
- B2: `choose_edf_optimal` (explicit precondition, NoDup + ready-set coverage)
- C: `UniSchedulerInterface.v` — abstract `UniSchedulerSpec` Record
- C': Instantiate `edf_scheduler_spec : UniSchedulerSpec` in `EDF.v`

## Proof Strategy

### A1 (`choose_edf_none_if_no_ready`)
Unfold `choose_edf`. Apply `min_dl_job_none_iff`. Show filter yields `[]` by induction on candidates: if head passes `readyb`, derive contradiction via `readyb_iff` and hypothesis; otherwise IH applies.

### A2 (`choose_edf_unique_min`)
Use `choose_edf_some_if_exists` to get a witness `j'`. Get `j'` is ready via `choose_edf_ready`, in candidates via `min_dl_job_in` + `filter_In`. Get `deadline(j') <= deadline(j)` via `choose_edf_min_deadline`. Case-split `j' = j` vs `j' ≠ j` via `Nat.eq_dec`. If `j' ≠ j`, strict hypothesis gives `deadline(j) < deadline(j')`, contradicting `<=`.

### B1 (`choose_edf_complete`)
Trivial: apply `choose_edf_some_if_exists` with witness from hypothesis, using `<->` to get `In j candidates`.

### B2 (`choose_edf_optimal`)
Trivial: apply `choose_edf_min_deadline` with `j'` in candidates from `<->` hypothesis.

### C (`UniSchedulerInterface.v`)
New file. `Record UniSchedulerSpec` with 4 fields: choose_ready, choose_min_deadline, choose_some_if_ready, choose_none_if_no_ready.

### C' (instantiation)
Definitional: `mkUniSchedulerSpec choose_edf choose_edf_ready choose_edf_min_deadline choose_edf_some_if_exists choose_edf_none_if_no_ready`.

## Proposed Lemmas

- [ ] A1: `choose_edf_none_if_no_ready`
- [ ] B1: `choose_edf_complete`
- [ ] B2: `choose_edf_optimal`
- [ ] A2: `choose_edf_unique_min`
- [ ] C: `UniSchedulerInterface.v` (new file)
- [ ] C': `edf_scheduler_spec` instantiation in `EDF.v` + Makefile update

## Proof Order

1. A1 `choose_edf_none_if_no_ready`
2. B1 `choose_edf_complete`
3. B2 `choose_edf_optimal`
4. A2 `choose_edf_unique_min`
5. C `UniSchedulerInterface.v`
6. C' instantiation + Makefile
