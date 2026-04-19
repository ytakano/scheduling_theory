From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Operational.Common.Trace.
From RocqSched Require Import Operational.Common.Step.
From RocqSched Require Import Operational.Common.Invariants.
From RocqSched Require Import Operational.Common.Execution.

Record labeled_execution (m : nat) : Type := mkLabeledExecution {
  lex_trace : OpTrace;
  lex_event : Time -> OpEvent;
  lex_init : Prop;
  lex_stepwise :
    forall t, op_step (lex_trace t) (lex_event t) (lex_trace (S t));
  lex_struct_inv :
    forall t, op_struct_inv m (lex_trace t);
}.

Arguments lex_trace {m} _ _.
Arguments lex_event {m} _ _.
Arguments lex_init {m} _.
Arguments lex_stepwise {m} _ _.
Arguments lex_struct_inv {m} _ _.

Definition labeled_to_execution
    {m : nat}
    (ex : labeled_execution m) : execution m :=
  mkExecution
    m
    (lex_trace ex)
    (lex_init ex)
    (fun t => ex_intro _ (lex_event ex t) (lex_stepwise ex t))
    (lex_struct_inv ex).

Lemma labeled_to_execution_trace_eq :
  forall m (ex : labeled_execution m) t,
    ex_trace (labeled_to_execution ex) t = lex_trace ex t.
Proof.
  reflexivity.
Qed.

Lemma labeled_execution_trace_step :
  forall m (ex : labeled_execution m) t,
    op_step (lex_trace ex t) (lex_event ex t) (lex_trace ex (S t)).
Proof.
  intros m ex t.
  exact (lex_stepwise ex t).
Qed.
