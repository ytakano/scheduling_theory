From Stdlib Require Import List.
From SchedulingTheory Require Import Foundation.Base.
From SchedulingTheory Require Import Semantics.Schedule.
From SchedulingTheory Require Import Abstractions.SchedulingAlgorithm.Interface.
From SchedulingTheory Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
Import ListNotations.

Definition enum_candidates_of (enumJ : list JobId) : CandidateSource :=
  fun _ _ _ _ => enumJ.

Lemma enum_candidates_spec :
  forall J enumJ,
    (forall j, J j -> In j enumJ) ->
    (forall j, In j enumJ -> J j) ->
    CandidateSourceSpec J (enum_candidates_of enumJ).
Proof.
  intros J enumJ Hcomplete Hsound.
  refine (mkCandidateSourceSpec J (enum_candidates_of enumJ) _ _ _).
  - intros jobs m sched t j Hin.
    unfold enum_candidates_of in Hin.
    exact (Hsound j Hin).
  - intros jobs m sched t j Hj Helig.
    unfold enum_candidates_of.
    exact (Hcomplete j Hj).
  - intros jobs m s1 s2 t Hprefix.
    unfold enum_candidates_of.
    reflexivity.
Qed.
