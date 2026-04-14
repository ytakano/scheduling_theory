From Stdlib Require Import List.
From RocqSched Require Import Foundation.Base.
Import ListNotations.

Record FiniteHorizonWitness
    (J : JobId -> Prop) : Type := mkFiniteHorizonWitness {
  witness_enumJ : list JobId;

  witness_enum_complete :
    forall j,
      J j ->
      In j witness_enumJ;

  witness_enum_sound :
    forall j,
      In j witness_enumJ ->
      J j
}.
