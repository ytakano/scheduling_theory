# Proof Progress: Policy Abstraction Layer

## Status Overview
- Overall: Complete
- Complete Lemmas: 13/13
- Unproven (`Admitted`): none
- Failed/Abandoned Items: none

## Completed Lemmas

### `SchedulerValidity.v` — all definitions and lemmas

```coq
Definition DispatchPolicy :=
  (JobId -> Job) -> nat -> Schedule -> Time -> list JobId -> option JobId -> Prop.

Record PolicySanity (policy : DispatchPolicy) : Prop := ...
Definition respects_policy_at ...
Definition respects_policy_at_with ...
Definition respects_policy_before ...
Definition single_cpu_policy_schedule ...
Definition single_cpu_policy_scheduler ...

Lemma respects_policy_at_with_in_candidates : ...  (* destruct Hsane, rewrite Hrun *)
Lemma respects_policy_at_with_implies_eligible : ...
Lemma respects_policy_at_with_in_subset : ...      (* destruct cand_spec *)
Lemma single_cpu_policy_schedulable_by_on_intro : ...
```

### `DispatcherRefinement.v` — all definitions and lemmas

```coq
Definition dispatcher_refines_policy ...

Lemma single_cpu_dispatch_schedule_respects_policy_at_with : ...
  (* rewrite Heq (from Hrel), apply Href *)
Lemma single_cpu_dispatch_schedule_respects_policy_before : ...
Lemma single_cpu_dispatch_schedule_implies_single_cpu_policy_schedule : ...
  (* split: exact (proj1 Hrel), apply respects_policy_at_with *)
```

### `UniPolicies/EDF.v` additions

```coq
Lemma choose_edf_none_implies_no_eligible : ...  (* auxiliary *)
Definition edf_policy : DispatchPolicy := ...
Lemma edf_policy_sane : PolicySanity edf_policy.
Lemma choose_edf_refines_edf_policy : dispatcher_refines_policy edf_generic_spec edf_policy.
  (* Some case: choose_edf_in_candidates / eligible / min_deadline
     None case: choose_edf_none_implies_no_eligible *)
```

### `UniPolicies/EDFLemmas.v` additions

```coq
Lemma matches_choose_edf_at_with_implies_respects_edf_policy_at_with : ...
  (* rewrite Hmatch; exact choose_edf_refines_edf_policy *)
Lemma respects_edf_policy_at_with_implies_respects_edf_priority_at_on : ...
  (* rewrite Hsched; unfold edf_policy; destruct [_ [_ Hmin]]; use Hmin + lia *)
```

### `UniPolicies/FIFO.v` additions

```coq
Lemma choose_fifo_none_implies_no_eligible : ...  (* auxiliary; induction on candidates *)
Definition fifo_policy : DispatchPolicy := ...
Lemma fifo_policy_sane : PolicySanity fifo_policy.
  (* in_candidates: in_or_app; eligible: proj from existential *)
Lemma choose_fifo_refines_fifo_policy : dispatcher_refines_policy fifo_generic_spec fifo_policy.
  (* Some: choose_fifo_first_eligible + choose_fifo_eligible
     None: choose_fifo_none_implies_no_eligible *)
```

## TODO
(none)
