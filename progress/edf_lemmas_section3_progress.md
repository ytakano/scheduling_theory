# Proof Progress: EDFLemmas Section 3 — Bridge / EDF の prefix 安定性

## Status Overview
- Overall: Complete
- Complete Lemmas: 4/4
- Unproven (`Admitted`): none
- Failed/Abandoned Items: none

## Completed Lemmas

### `eligibleb_agrees_before` (helper)

```coq
Lemma eligibleb_agrees_before :
  forall jobs m s1 s2 j t,
    agrees_before s1 s2 t ->
    eligibleb jobs m s1 j t = eligibleb jobs m s2 j t.
Proof.
  intros jobs m s1 s2 j t Hagree.
  unfold eligibleb.
  rewrite (agrees_before_service_job m s1 s2 j t Hagree).
  reflexivity.
Qed.
```

### `candidates_of_agrees_before` (3-1)

```coq
Lemma candidates_of_agrees_before :
  forall J candidates_of
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs s1 s2 t,
    agrees_before s1 s2 t ->
    candidates_of jobs 1 s1 t = candidates_of jobs 1 s2 t.
Proof.
  intros J candidates_of cand_spec jobs s1 s2 t Hagree.
  destruct cand_spec as [_ _ Hpx].
  exact (Hpx jobs 1 s1 s2 t Hagree).
Qed.
```

### `choose_edf_agrees_before` (3-2)

```coq
Lemma choose_edf_agrees_before :
  forall jobs s1 s2 t candidates,
    agrees_before s1 s2 t ->
    choose_edf jobs 1 s1 t candidates =
    choose_edf jobs 1 s2 t candidates.
Proof.
  intros jobs s1 s2 t candidates Hagree.
  unfold choose_edf.
  f_equal.
  apply List.filter_ext.
  intro j.
  apply eligibleb_agrees_before. exact Hagree.
Qed.
```

### `edf_dispatch_agrees_before` (3-3)

```coq
Lemma edf_dispatch_agrees_before :
  forall J candidates_of
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs s1 s2 t,
    agrees_before s1 s2 t ->
    dispatch edf_generic_spec jobs 1 s1 t (candidates_of jobs 1 s1 t) =
    dispatch edf_generic_spec jobs 1 s2 t (candidates_of jobs 1 s2 t).
Proof.
  intros J candidates_of cand_spec jobs s1 s2 t Hagree.
  simpl.
  rewrite (candidates_of_agrees_before J candidates_of cand_spec jobs s1 s2 t Hagree).
  apply choose_edf_agrees_before. exact Hagree.
Qed.
```

## Proof Attempts & Diagnostics

### `candidates_of_agrees_before` — 初回エラー (fixed)

- Attempt 1: `apply (cand_spec.(candidates_prefix_extensional) jobs 1 s1 s2 t). exact Hagree.`
- Error: "Projection candidates_prefix_extensional expected 2 explicit parameters."
- Diagnosis: `CandidateSourceSpec` には 2 つの明示パラメータ (`J`, `candidates_of`) があるため、
  `.()` projection 構文が機能しない。`GenericDispatchSpec` (パラメータなし) では `.()` が使えるが、
  パラメータを持つ record では `destruct` が必要。
- Fix: `destruct cand_spec as [_ _ Hpx]; exact (Hpx jobs 1 s1 s2 t Hagree).`

## TODO

(all done)
