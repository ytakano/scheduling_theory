From Stdlib Require Import List String.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Operational.Common.Projection.
From RocqSched Require Import Operational.Common.ConcreteExecution.
From RocqSched Require Import Operational.Common.LabeledExecution.
From RocqSched Require Import Operational.Common.OSLocalAdapterContract.
From RocqSched Require Import Operational.Awkernel.Minimal.MinimalProjection.
From RocqSched Require Import Operational.Awkernel.BaselineTrace.
Import ListNotations.
Open Scope string_scope.

(** * Captured Awkernel baseline witness

    This module records the canonical serial trace artifact for the faithful
    two-CPU Awkernel baseline. The canonical runtime trace is emitted by the
    baseline VM test mode and checked against the fixture under
    [awkernel/fixtures/baseline_trace/faithful_2cpu.txt].

    The proof-facing witness remains the existing 2-CPU cross-core baseline:
    CPU 0 provides the wakeup-side witness and CPU 1 provides the choose,
    dispatch, and completion witness. No new common-layer event is introduced.
 *)

Definition awk_captured_baseline_lines : list string :=
  [ "BASELINE_TRACE: cpu=0 event=EvWakeup current=None runnable=[1] need_resched=false dispatch_target=None"
  ; "BASELINE_TRACE: cpu=1 event=EvChoose current=None runnable=[1] need_resched=false dispatch_target=Some(1)"
  ; "BASELINE_TRACE: cpu=1 event=EvDispatch current=Some(1) runnable=[] need_resched=false dispatch_target=None"
  ; "BASELINE_TRACE: cpu=1 event=EvComplete current=None runnable=[] need_resched=true dispatch_target=None"
  ; "BASELINE_TRACE_DONE"
  ].

Definition awk_captured_baseline_projection := awk_baseline_projection.
Definition awk_captured_baseline_execution := awk_baseline_execution.
Definition awk_captured_baseline_contract := awk_baseline_contract.

Example awk_captured_baseline_has_four_events :
  List.length awk_captured_baseline_lines = 5.
Proof.
  reflexivity.
Qed.

Example awk_captured_baseline_valid_schedule :
  valid_schedule
    awk_baseline_jobs
    2
    (project_schedule
       (lex_trace
          (concrete_to_labeled_execution
             (olac_execution awk_captured_baseline_contract)))).
Proof.
  exact awk_baseline_contract_valid_schedule.
Qed.
