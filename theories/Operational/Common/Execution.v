From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Operational.Common.Trace.
From RocqSched Require Import Operational.Common.Step.
From RocqSched Require Import Operational.Common.Invariants.

Definition trace_stepwise (tr : OpTrace) : Prop :=
  forall t, exists ev, op_step (tr t) ev (tr (S t)).

Record execution (m : nat) : Type := mkExecution {
  ex_trace : OpTrace;
  ex_init : Prop;
  ex_stepwise : trace_stepwise ex_trace;
  ex_struct_inv : forall t, op_struct_inv m (ex_trace t);
}.

Arguments ex_trace {m} _ _.
Arguments ex_init {m} _.
Arguments ex_stepwise {m} _ _.
Arguments ex_struct_inv {m} _ _.

Lemma execution_trace_step :
  forall m (ex : execution m) t,
    exists ev, op_step (ex_trace ex t) ev (ex_trace ex (S t)).
Proof.
  intros m ex t.
  exact (ex_stepwise ex t).
Qed.
