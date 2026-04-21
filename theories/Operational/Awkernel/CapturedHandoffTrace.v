From Stdlib Require Import List String.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Operational.Common.Projection.
From RocqSched Require Import Operational.Common.ConcreteExecution.
From RocqSched Require Import Operational.Common.LabeledExecution.
From RocqSched Require Import Operational.Common.OSLocalAdapterContract.
From RocqSched Require Import Refinement.OSRefinementTheorem.
From RocqSched Require Import Operational.Awkernel.BaselineTrace.
From RocqSched Require Import Operational.Awkernel.HandoffTrace.
Import ListNotations.
Open Scope string_scope.

(** * Captured Awkernel handoff witness

    This module records the canonical serial trace artifact for the first
    handoff-aware two-CPU Awkernel adapter milestone. The canonical runtime
    trace is emitted by the handoff VM test mode and checked against the
    fixture under [awkernel/fixtures/handoff_trace/faithful_2cpu.txt].

    The proof-facing witness remains an adapter-level cross-core trace:
    CPU 0 provides the wakeup-side witness, CPU 1 receives the proof-facing
    reschedule request and handling steps, and CPU 1 performs dispatch and
    completion. No new common-layer event is introduced.
 *)

Definition awk_captured_handoff_lines : list string :=
  [ "BASELINE_TRACE: cpu=0 event=EvWakeup current=None runnable=[1] need_resched=false dispatch_target=None"
  ; "BASELINE_TRACE: cpu=1 event=EvRequestResched current=None runnable=[1] need_resched=true dispatch_target=None"
  ; "BASELINE_TRACE: cpu=1 event=EvHandleResched current=None runnable=[1] need_resched=true dispatch_target=None"
  ; "BASELINE_TRACE: cpu=1 event=EvChoose current=None runnable=[1] need_resched=false dispatch_target=Some(1)"
  ; "BASELINE_TRACE: cpu=1 event=EvDispatch current=Some(1) runnable=[] need_resched=false dispatch_target=None"
  ; "BASELINE_TRACE: cpu=1 event=EvComplete current=None runnable=[] need_resched=true dispatch_target=None"
  ; "BASELINE_TRACE_DONE"
  ].

Definition awk_captured_handoff_projection := awk_handoff_projection.
Definition awk_captured_handoff_execution := awk_handoff_execution.
Definition awk_captured_handoff_contract := awk_handoff_local_adapter_contract.

Example awk_captured_handoff_has_six_events :
  List.length awk_captured_handoff_lines = 7.
Proof.
  reflexivity.
Qed.

Example awk_captured_handoff_valid_schedule :
  valid_schedule
    awk_baseline_jobs
    2
    (project_schedule
       (lex_trace
          (concrete_to_labeled_execution
             (olac_execution awk_captured_handoff_contract)))).
Proof.
  exact awk_handoff_contract_valid_schedule.
Qed.
