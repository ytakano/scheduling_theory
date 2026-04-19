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
      op_current st c = Some j ->
      ~ In j (op_runnable st);
  osi_dispatch_no_dup :
    forall j c1 c2,
      c1 < m ->
      c2 < m ->
      op_dispatch_target st c1 = Some j ->
      op_dispatch_target st c2 = Some j ->
      c1 = c2;
  osi_dispatch_from_runnable :
    forall c j,
      c < m ->
      op_dispatch_target st c = Some j ->
      In j (op_runnable st);
}.
