From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Operational.Common.State.
From RocqSched Require Import Operational.Common.Invariants.
From RocqSched Require Import Multicore.Common.MultiCoreBase.

Definition op_idle_outside_range (m : nat) (st : OpState) : Prop :=
  forall c, m <= c -> op_current st c = None.

Definition op_respects_admissibility
    (adm : admissible_cpu) (m : nat) (st : OpState) : Prop :=
  forall c j,
    c < m ->
    op_current st c = Some j ->
    adm j c.

Record op_multicore_projection_inv
    (adm : admissible_cpu) (m : nat) (st : OpState) : Prop := {
  ompi_struct :
    op_struct_inv m st;
  ompi_idle_outside :
    op_idle_outside_range m st;
  ompi_placement :
    op_respects_admissibility adm m st;
}.
