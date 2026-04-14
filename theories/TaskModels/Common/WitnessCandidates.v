From Stdlib Require Import List.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.EnumCandidates.
From RocqSched Require Import TaskModels.Common.FiniteHorizonWitness.
Import ListNotations.

Definition witness_candidates_of
    (J : JobId -> Prop)
    (w : FiniteHorizonWitness J)
    : CandidateSource :=
  enum_candidates_of (witness_enumJ J w).

Lemma witness_candidates_spec :
  forall J (w : FiniteHorizonWitness J),
    CandidateSourceSpec J (witness_candidates_of J w).
Proof.
  intros J w.
  unfold witness_candidates_of.
  apply enum_candidates_spec.
  - exact (witness_enum_complete J w).
  - exact (witness_enum_sound J w).
Qed.
