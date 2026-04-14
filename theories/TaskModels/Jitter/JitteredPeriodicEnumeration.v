From Stdlib Require Import List.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicFiniteHorizon.
Import ListNotations.

Record JitteredPeriodicFiniteHorizonWitness
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jitter : TaskId -> Time)
    (jobs : JobId -> Job)
    (H : Time) : Type := mkJitteredPeriodicFiniteHorizonWitness {

  jittered_enumJ : list JobId;

  jittered_enum_complete :
    forall j,
      jittered_periodic_jobset_upto T tasks offset jitter jobs H j ->
      In j jittered_enumJ;

  jittered_enum_sound :
    forall j,
      In j jittered_enumJ ->
      jittered_periodic_jobset_upto T tasks offset jitter jobs H j
}.

