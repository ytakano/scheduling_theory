From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Operational.Common.State.
Import ListNotations.

Record op_struct_inv (m : nat) (st : OpState) : Prop := mkOpStructInv {
  osi_no_dup :
    op_no_duplication m st;
  osi_runnable_nodup :
    op_runnable_set_like st;
  osi_current_not_in_runnable :
    forall c j,
      c < m ->
      op_current st c = Some j ->
      ~ In j (op_runnable st);
}.
