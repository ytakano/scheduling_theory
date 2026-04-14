From Stdlib Require Import List.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import TaskModels.Common.FiniteHorizonWitness.
From RocqSched Require Import TaskModels.Sporadic.SporadicFiniteHorizon.
Import ListNotations.

Definition SporadicFiniteHorizonWitness
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (jobs : JobId -> Job)
    (H : Time) : Type :=
  FiniteHorizonWitness (sporadic_jobset_upto T tasks jobs H).
