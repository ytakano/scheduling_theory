From Stdlib Require Import List.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import TaskModels.Sporadic.SporadicFiniteHorizon.
Import ListNotations.

(* A thin wrapper around manual finite-horizon job enumeration for sporadic
   task systems. Unlike the periodic codec, this does not attempt to derive
   jobs from (task, index); it only packages a user-supplied finite witness. *)
Record SporadicFiniteHorizonWitness
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (jobs : JobId -> Job)
    (H : Time) : Type := mkSporadicFiniteHorizonWitness {

  sporadic_enumJ : list JobId;

  sporadic_enum_complete :
    forall j,
      sporadic_jobset_upto T tasks jobs H j ->
      In j sporadic_enumJ;

  sporadic_enum_sound :
    forall j,
      In j sporadic_enumJ ->
      sporadic_jobset_upto T tasks jobs H j
}.
