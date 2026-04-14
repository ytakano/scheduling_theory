From Stdlib Require Import List.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import TaskModels.Common.FiniteHorizonWitness.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicFiniteHorizon.
Import ListNotations.

Definition JitteredPeriodicFiniteHorizonWitness
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jitter : TaskId -> Time)
    (jobs : JobId -> Job)
    (H : Time) : Type :=
  FiniteHorizonWitness
    (jittered_periodic_jobset_upto T tasks offset jitter jobs H).
