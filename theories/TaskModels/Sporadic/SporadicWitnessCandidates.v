From Stdlib Require Import List.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.EnumCandidates.
From RocqSched Require Import TaskModels.Sporadic.SporadicFiniteHorizon.
From RocqSched Require Import TaskModels.Sporadic.SporadicEnumeration.
Import ListNotations.

Definition sporadic_witness_candidates_of
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (jobs : JobId -> Job)
    (H : Time)
    (w : SporadicFiniteHorizonWitness T tasks jobs H)
    : CandidateSource :=
  enum_candidates_of (sporadic_enumJ T tasks jobs H w).

Lemma sporadic_witness_candidates_spec :
  forall T tasks jobs H
         (w : SporadicFiniteHorizonWitness T tasks jobs H),
    CandidateSourceSpec
      (sporadic_jobset_upto T tasks jobs H)
      (sporadic_witness_candidates_of T tasks jobs H w).
Proof.
  intros T tasks jobs H w.
  unfold sporadic_witness_candidates_of.
  apply enum_candidates_spec.
  - exact (sporadic_enum_complete T tasks jobs H w).
  - exact (sporadic_enum_sound T tasks jobs H w).
Qed.
