From Stdlib Require Import List String Bool Arith Arith.PeanoNat Lia Logic.FunctionalExtensionality.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Operational.Common.State.
From RocqSched Require Import Operational.Common.Step.
From RocqSched Require Import Operational.Common.Projection.
From RocqSched Require Import Operational.Common.OSProjectionInterface.
From RocqSched Require Import Operational.Common.Invariants.
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
  match awk_handoff_generate_post_states awk_captured_handoff_rows with
  | Some states => states
  | None => []
  end.

Lemma awk_captured_handoff_post_states_eq :
  awk_captured_handoff_post_states =
  [ awk_handoff_state1
  ; awk_handoff_state2
  ; awk_handoff_state3
  ; awk_handoff_state4
  ; awk_handoff_state5
  ; awk_handoff_state6
  ].
Proof.
  unfold awk_captured_handoff_post_states, awk_captured_handoff_rows.
  rewrite awk_handoff_generated_rows_compute_post_states.
  reflexivity.
Qed.

Definition awk_captured_handoff_trace (t : Time) : AwkernelHandoffState :=
  awk_handoff_generated_trace awk_captured_handoff_post_states t.

Lemma awk_captured_handoff_rows_are_generated :
  awk_handoff_row_generation
    awk_captured_handoff_rows
    awk_captured_handoff_post_states.
Proof.
  unfold awk_captured_handoff_rows.
  rewrite awk_captured_handoff_post_states_eq.
  exact awk_handoff_generated_rows_are_generated.
Qed.

Lemma awk_captured_handoff_rows_are_accepted :
  awk_handoff_accepts_rows awk_captured_handoff_rows = true.
Proof.
  unfold awk_captured_handoff_rows.
  exact awk_handoff_generated_rows_are_accepted.
Qed.

Lemma awk_captured_handoff_rows_accept_sound :
  exists states,
    awk_handoff_check_rows awk_captured_handoff_rows = Some states /\
    awk_handoff_row_generation awk_captured_handoff_rows states.
Proof.
  exists awk_captured_handoff_post_states.
  split.
  - unfold awk_handoff_check_rows, awk_captured_handoff_rows, awk_captured_handoff_post_states.
    rewrite awk_handoff_generated_rows_compute_post_states.
    reflexivity.
  - exact awk_captured_handoff_rows_are_generated.
Qed.

Lemma awk_captured_handoff_trace_eq :
  forall t, awk_captured_handoff_trace t = awk_handoff_trace t.
Proof.
  intros [|[|[|[|[|[|[|t']]]]]]].
  - unfold awk_captured_handoff_trace, awk_handoff_trace.
    rewrite awk_captured_handoff_post_states_eq.
    reflexivity.
  - unfold awk_captured_handoff_trace, awk_handoff_trace.
    rewrite awk_captured_handoff_post_states_eq.
    reflexivity.
  - unfold awk_captured_handoff_trace, awk_handoff_trace.
    rewrite awk_captured_handoff_post_states_eq.
    reflexivity.
  - unfold awk_captured_handoff_trace, awk_handoff_trace.
    rewrite awk_captured_handoff_post_states_eq.
    reflexivity.
  - unfold awk_captured_handoff_trace, awk_handoff_trace.
    rewrite awk_captured_handoff_post_states_eq.
    reflexivity.
  - unfold awk_captured_handoff_trace, awk_handoff_trace.
    rewrite awk_captured_handoff_post_states_eq.
    reflexivity.
  - unfold awk_captured_handoff_trace, awk_handoff_trace.
    rewrite awk_captured_handoff_post_states_eq.
    reflexivity.
  - unfold awk_captured_handoff_trace, awk_handoff_trace,
      awk_handoff_generated_trace,
      awk_handoff_generated_trace_from,
      awk_handoff_generated_final_state_from.
    rewrite awk_captured_handoff_post_states_eq.
    replace
      (nth (S (S (S (S (S (S t'))))))
         [awk_handoff_state1; awk_handoff_state2; awk_handoff_state3;
          awk_handoff_state4; awk_handoff_state5; awk_handoff_state6]
         (last
            [awk_handoff_state1; awk_handoff_state2; awk_handoff_state3;
             awk_handoff_state4; awk_handoff_state5; awk_handoff_state6]
            awk_handoff_state0))
      with awk_handoff_state6 by
        (symmetry; apply nth_overflow; simpl; lia).
    reflexivity.
Qed.

Definition awk_captured_handoff_projection := awk_handoff_projection.

Lemma awk_captured_handoff_lce_stepwise :
  forall t,
    op_step
      (os_to_op_state (osl_to_os_projection awk_captured_handoff_projection)
         (awk_captured_handoff_trace t))
      (os_step_label awk_captured_handoff_projection
         (awk_captured_handoff_trace t)
         (awk_captured_handoff_trace (S t)))
      (os_to_op_state (osl_to_os_projection awk_captured_handoff_projection)
         (awk_captured_handoff_trace (S t))).
Proof.
  intros t.
  rewrite !awk_captured_handoff_trace_eq.
  exact (awk_handoff_lce_stepwise t).
Qed.

Lemma awk_captured_handoff_lce_struct_inv :
  forall t,
    op_struct_inv 2
      (os_to_op_state (osl_to_os_projection awk_captured_handoff_projection)
         (awk_captured_handoff_trace t)).
Proof.
  intros t.
  rewrite awk_captured_handoff_trace_eq.
  exact (awk_handoff_lce_struct_inv t).
Qed.

Definition awk_captured_handoff_execution : labeled_concrete_execution awk_captured_handoff_projection 2 :=
  {|
    lce_trace := awk_captured_handoff_trace;
    lce_init := True;
    lce_stepwise := awk_captured_handoff_lce_stepwise;
    lce_struct_inv := awk_captured_handoff_lce_struct_inv;
  |}.

Definition awk_captured_handoff_contract_execution : labeled_concrete_execution awk_captured_handoff_projection 2 :=
  awk_captured_handoff_execution.

Lemma awk_captured_handoff_op_trace_eq :
  osl_to_op_trace awk_captured_handoff_projection
    (lce_trace awk_captured_handoff_contract_execution) =
  osl_to_op_trace awk_handoff_projection
    (lce_trace awk_handoff_execution).
Proof.
  apply functional_extensionality. intro t.
  unfold osl_to_op_trace, os_to_op_trace,
         awk_captured_handoff_contract_execution,
         awk_captured_handoff_execution.
  simpl. rewrite awk_captured_handoff_trace_eq. reflexivity.
Qed.

Lemma awk_captured_handoff_schedule_eq :
  project_schedule
    (osl_to_op_trace awk_captured_handoff_projection
       (lce_trace awk_captured_handoff_contract_execution)) =
  project_schedule
    (osl_to_op_trace awk_handoff_projection
       (lce_trace awk_handoff_execution)).
Proof.
  unfold project_schedule.
  now rewrite awk_captured_handoff_op_trace_eq.
Qed.

Lemma awk_captured_handoff_local_sound :
  @local_labeled_concrete_multicore_projection_sound AwkernelHandoffState
    awk_captured_handoff_projection
    awk_baseline_jobs
    awk_baseline_admissibility
    2
    awk_captured_handoff_contract_execution.
Proof.
  pose proof (llcmps_projection_sound awk_handoff_local_sound) as Hproj.
  refine {|
    llcmps_projection_sound := _;
    llcmps_idle_outside := _;
    llcmps_placement := _;
  |}.
  - refine {|
      llcps_init_release := _;
      llcps_init_completion := _;
      llcps_init_runnable_release := _;
      llcps_init_runnable_completion := _;
      llcps_current_origin := _;
      llcps_dispatch_release := _;
      llcps_wakeup_release := _;
      llcps_wakeup_completion := _;
      llcps_persistent_completion := _;
      llcps_request_sets_need_resched := _;
      llcps_handle_sets_need_resched := _;
      llcps_choose_sets_dispatch_target := _;
      llcps_choose_from_runnable := _;
      llcps_dispatch_completion := _;
      llcps_block_clears_current := _;
      llcps_block_clears_runnable := _;
      llcps_block_clears_dispatch_target := _;
      llcps_complete_sets_completed := _;
      llcps_preempt_release := _;
        llcps_preempt_completion := _;
        llcps_preempt_old_completion := _;
      |}.
    + intros c j Hlt Hcur.
      rewrite awk_captured_handoff_trace_eq in Hcur.
      exact (llcps_init_release Hproj c j Hlt Hcur).
    + intros c j Hlt Hcur.
      rewrite awk_captured_handoff_trace_eq in Hcur.
      exact (llcps_init_completion Hproj c j Hlt Hcur).
    + intros j Hin.
      rewrite awk_captured_handoff_trace_eq in Hin.
      exact (llcps_init_runnable_release Hproj j Hin).
    + intros j Hin.
      rewrite awk_captured_handoff_trace_eq in Hin.
      exact (llcps_init_runnable_completion Hproj j Hin).
    + intros t c j Hlt Hcur.
      rewrite awk_captured_handoff_trace_eq in Hcur.
      destruct (llcps_current_origin Hproj t c j Hlt Hcur)
        as [Hprev | [Hdispatch | Hpreempt]].
      * left. rewrite awk_captured_handoff_trace_eq. exact Hprev.
      * right. left. rewrite !awk_captured_handoff_trace_eq. exact Hdispatch.
      * right. right.
        destruct Hpreempt as [old Hpreempt].
        exists old.
        rewrite !awk_captured_handoff_trace_eq.
        exact Hpreempt.
    + intros t c j Hlt Hlbl.
      rewrite !awk_captured_handoff_trace_eq in Hlbl.
      exact (llcps_dispatch_release Hproj t c j Hlt Hlbl).
    + intros t j Hlbl.
      rewrite !awk_captured_handoff_trace_eq in Hlbl.
      exact (llcps_wakeup_release Hproj t j Hlbl).
    + intros t j Hlbl.
      rewrite !awk_captured_handoff_trace_eq in Hlbl.
      rewrite awk_captured_handoff_schedule_eq.
      exact (llcps_wakeup_completion Hproj t j Hlbl).
    + intros t c j Hlt Hcur Hnext.
      rewrite awk_captured_handoff_trace_eq in Hcur.
      rewrite awk_captured_handoff_trace_eq in Hnext.
      rewrite awk_captured_handoff_schedule_eq.
      exact (llcps_persistent_completion Hproj t c j Hlt Hcur Hnext).
    + intros t c Hlt Hlbl.
      rewrite !awk_captured_handoff_trace_eq in Hlbl.
      rewrite awk_captured_handoff_trace_eq.
      exact (llcps_request_sets_need_resched Hproj t c Hlt Hlbl).
    + intros t c Hlt Hlbl.
      rewrite !awk_captured_handoff_trace_eq in Hlbl.
      rewrite awk_captured_handoff_trace_eq.
      exact (llcps_handle_sets_need_resched Hproj t c Hlt Hlbl).
    + intros t c j Hlt Hlbl.
      rewrite !awk_captured_handoff_trace_eq in Hlbl.
      rewrite awk_captured_handoff_trace_eq.
      exact (llcps_choose_sets_dispatch_target Hproj t c j Hlt Hlbl).
    + intros t c j Hlt Hlbl.
      rewrite !awk_captured_handoff_trace_eq in Hlbl.
      rewrite awk_captured_handoff_trace_eq.
      exact (llcps_choose_from_runnable Hproj t c j Hlt Hlbl).
    + intros t c j Hlt Hlbl.
      rewrite !awk_captured_handoff_trace_eq in Hlbl.
      rewrite awk_captured_handoff_schedule_eq.
      exact (llcps_dispatch_completion Hproj t c j Hlt Hlbl).
    + intros t c j Hlbl.
      rewrite !awk_captured_handoff_trace_eq in Hlbl.
      rewrite awk_captured_handoff_trace_eq.
      exact (llcps_block_clears_current Hproj t c j Hlbl).
    + intros t j Hlbl.
      rewrite !awk_captured_handoff_trace_eq in Hlbl.
      rewrite awk_captured_handoff_trace_eq.
      exact (llcps_block_clears_runnable Hproj t j Hlbl).
    + intros t c j Hlt Hlbl.
      rewrite !awk_captured_handoff_trace_eq in Hlbl.
      rewrite awk_captured_handoff_trace_eq.
      exact (llcps_block_clears_dispatch_target Hproj t c j Hlt Hlbl).
    + intros t j Hlbl.
      rewrite !awk_captured_handoff_trace_eq in Hlbl.
      rewrite awk_captured_handoff_schedule_eq.
      exact (llcps_complete_sets_completed Hproj t j Hlbl).
    + intros t c old new Hlt Hlbl.
      rewrite !awk_captured_handoff_trace_eq in Hlbl.
      exact (llcps_preempt_release Hproj t c old new Hlt Hlbl).
    + intros t c old new Hlt Hlbl.
      rewrite !awk_captured_handoff_trace_eq in Hlbl.
      rewrite awk_captured_handoff_schedule_eq.
      exact (llcps_preempt_completion Hproj t c old new Hlt Hlbl).
    + intros t c old new Hlt Hlbl.
      rewrite !awk_captured_handoff_trace_eq in Hlbl.
      rewrite awk_captured_handoff_schedule_eq.
      exact (llcps_preempt_old_completion Hproj t c old new Hlt Hlbl).
  - intros t.
    rewrite awk_captured_handoff_trace_eq.
    exact (llcmps_idle_outside awk_handoff_local_sound t).
  - intros t.
    rewrite awk_captured_handoff_trace_eq.
    exact (llcmps_placement awk_handoff_local_sound t).
Qed.

Definition awk_captured_handoff_contract :
  @os_local_multicore_adapter_contract AwkernelHandoffState
    awk_captured_handoff_projection
    awk_baseline_jobs
    awk_baseline_admissibility
    2 :=
  {|
    olac_execution := awk_captured_handoff_contract_execution;
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
