From Stdlib Require Import List String Bool Arith Arith.PeanoNat Lia Logic.FunctionalExtensionality.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Operational.Common.State.
From RocqSched Require Import Operational.Common.Step.
From RocqSched Require Import Operational.Common.Projection.
From RocqSched Require Import Operational.Common.ConcreteExecution.
From RocqSched Require Import Operational.Common.LabeledExecution.
From RocqSched Require Import Operational.Common.OSLocalAdapterContract.
From RocqSched Require Import Refinement.OSRefinementTheorem.
From RocqSched Require Import Operational.Awkernel.BaselineTrace.
From RocqSched Require Import Operational.Awkernel.CapturedTraceSyntax.
From RocqSched Require Import Operational.Awkernel.GeneratedHandoffTraceArtifact.
From RocqSched Require Import Operational.Awkernel.HandoffTrace.
From RocqSched Require Import Operational.Awkernel.HandoffTraceFamily.
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

Definition awk_captured_handoff_rows : list AwkernelCapturedRow :=
  awk_generated_handoff_rows.

Definition awk_captured_handoff_post_states : list AwkernelHandoffState :=
  [ awk_handoff_state1
  ; awk_handoff_state2
  ; awk_handoff_state3
  ; awk_handoff_state4
  ; awk_handoff_state5
  ; awk_handoff_state6
  ].

Definition awk_captured_handoff_trace (t : Time) : AwkernelHandoffState :=
  match t with
  | 0 => awk_handoff_state0
  | S t' => nth t' awk_captured_handoff_post_states awk_handoff_state6
  end.

Lemma awk_captured_handoff_rows_are_generated :
  awk_handoff_row_generation
    awk_captured_handoff_rows
    awk_captured_handoff_post_states.
Proof.
  unfold awk_captured_handoff_rows, awk_captured_handoff_post_states.
  exact awk_handoff_generated_rows_are_generated.
Qed.

Lemma awk_captured_handoff_trace_eq :
  forall t, awk_captured_handoff_trace t = awk_handoff_trace t.
Proof.
  intros [|[|[|[|[|[|[|t']]]]]]].
  - unfold awk_captured_handoff_trace, awk_handoff_trace,
      awk_captured_handoff_post_states.
    reflexivity.
  - unfold awk_captured_handoff_trace, awk_handoff_trace,
      awk_captured_handoff_post_states.
    reflexivity.
  - unfold awk_captured_handoff_trace, awk_handoff_trace,
      awk_captured_handoff_post_states.
    reflexivity.
  - unfold awk_captured_handoff_trace, awk_handoff_trace,
      awk_captured_handoff_post_states.
    reflexivity.
  - unfold awk_captured_handoff_trace, awk_handoff_trace,
      awk_captured_handoff_post_states.
    reflexivity.
  - unfold awk_captured_handoff_trace, awk_handoff_trace,
      awk_captured_handoff_post_states.
    reflexivity.
  - unfold awk_captured_handoff_trace, awk_handoff_trace,
      awk_captured_handoff_post_states.
    reflexivity.
  - unfold awk_captured_handoff_trace, awk_handoff_trace,
      awk_captured_handoff_post_states.
    replace
      (nth (S (S (S (S (S (S t'))))))
         [awk_handoff_state1; awk_handoff_state2; awk_handoff_state3;
          awk_handoff_state4; awk_handoff_state5; awk_handoff_state6]
         awk_handoff_state6)
      with awk_handoff_state6 by
        (symmetry; apply nth_overflow; simpl; lia).
    reflexivity.
Qed.

Definition awk_captured_handoff_projection := awk_handoff_projection.

Definition awk_captured_handoff_execution : labeled_concrete_execution awk_captured_handoff_projection 2 :=
  awk_handoff_execution.

Lemma awk_captured_handoff_local_sound :
  @local_labeled_concrete_multicore_projection_sound AwkernelHandoffState
    awk_captured_handoff_projection
    awk_baseline_jobs
    awk_baseline_admissibility
    2
    awk_captured_handoff_execution.
Proof.
  exact awk_handoff_local_sound.
Qed.

Definition awk_captured_handoff_contract :
  @os_local_multicore_adapter_contract AwkernelHandoffState
    awk_captured_handoff_projection
    awk_baseline_jobs
    awk_baseline_admissibility
    2 :=
  {|
    olac_execution := awk_captured_handoff_execution;
    olac_sound := awk_captured_handoff_local_sound;
  |}.

Example awk_captured_handoff_has_six_events :
  List.length awk_captured_handoff_rows = 6.
Proof.
  reflexivity.
Qed.

Example awk_captured_handoff_seed_is_well_formed :
  awk_handoff_row_generation
    awk_captured_handoff_rows
    awk_captured_handoff_post_states.
Proof.
  exact awk_captured_handoff_rows_are_generated.
Qed.

Example awk_captured_handoff_rows_replay_trace :
  forall t, awk_captured_handoff_trace t = awk_handoff_trace t.
Proof.
  exact awk_captured_handoff_trace_eq.
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
  apply os_local_multicore_adapter_contract_implies_valid_schedule.
Qed.
