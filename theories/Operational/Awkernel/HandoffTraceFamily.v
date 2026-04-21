From Stdlib Require Import List String Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Operational.Common.Step.
From RocqSched Require Import Operational.Awkernel.CapturedTraceSyntax.
From RocqSched Require Import Operational.Awkernel.GeneratedHandoffTraceArtifact.
From RocqSched Require Import Operational.Awkernel.HandoffTrace.
Import ListNotations.

Section AwkernelHandoffTraceFamily.

  Definition awk_handoff_row_wakeup : AwkernelCapturedRow :=
    mkAwkernelCapturedRow 0 (EvWakeup 1) None [1] false None.

  Definition awk_handoff_row_request_resched : AwkernelCapturedRow :=
    mkAwkernelCapturedRow 1 (EvRequestResched 1) None [1] true None.

  Definition awk_handoff_row_handle_resched : AwkernelCapturedRow :=
    mkAwkernelCapturedRow 1 (EvHandleResched 1) None [1] true None.

  Definition awk_handoff_row_choose : AwkernelCapturedRow :=
    mkAwkernelCapturedRow 1 (EvChoose 1 1) None [1] true (Some 1).

  Definition awk_handoff_row_dispatch : AwkernelCapturedRow :=
    mkAwkernelCapturedRow 1 (EvDispatch 1 1) (Some 1) [] false None.

  Definition awk_handoff_row_complete : AwkernelCapturedRow :=
    mkAwkernelCapturedRow 1 (EvComplete 1) None [] true None.

  Definition awk_handoff_seed_rows : list AwkernelCapturedRow :=
    [ awk_handoff_row_wakeup
    ; awk_handoff_row_request_resched
    ; awk_handoff_row_handle_resched
    ; awk_handoff_row_choose
    ; awk_handoff_row_dispatch
    ; awk_handoff_row_complete
    ].

  Lemma awk_handoff_seed_rows_eq_generated :
    awk_handoff_seed_rows = awk_generated_handoff_rows.
  Proof.
    reflexivity.
  Qed.

  Inductive awk_handoff_row_step
    : AwkernelHandoffState -> AwkernelCapturedRow -> AwkernelHandoffState -> Prop :=
  | awk_handoff_row_step_wakeup :
      awk_handoff_row_step
        awk_handoff_state0
        awk_handoff_row_wakeup
        awk_handoff_state1
  | awk_handoff_row_step_request_resched :
      awk_handoff_row_step
        awk_handoff_state1
        awk_handoff_row_request_resched
        awk_handoff_state2
  | awk_handoff_row_step_handle_resched :
      awk_handoff_row_step
        awk_handoff_state2
        awk_handoff_row_handle_resched
        awk_handoff_state3
  | awk_handoff_row_step_choose :
      awk_handoff_row_step
        awk_handoff_state3
        awk_handoff_row_choose
        awk_handoff_state4
  | awk_handoff_row_step_dispatch :
      awk_handoff_row_step
        awk_handoff_state4
        awk_handoff_row_dispatch
        awk_handoff_state5
  | awk_handoff_row_step_complete :
      awk_handoff_row_step
        awk_handoff_state5
        awk_handoff_row_complete
        awk_handoff_state6
  | awk_handoff_row_step_stutter :
      forall st row,
        acr_event row = EvStutter ->
        awk_row_to_state row = awk_handoff_visible st ->
        awk_handoff_row_step
          st
          row
          (mkAwkernelHandoffState (awk_handoff_visible st) (awk_handoff_phase st)).

  Inductive awk_handoff_row_generation_from
    : AwkernelHandoffState ->
      list AwkernelCapturedRow ->
      list AwkernelHandoffState -> Prop :=
  | awk_handoff_row_generation_nil :
      forall st,
        awk_handoff_row_generation_from st [] []
  | awk_handoff_row_generation_cons :
      forall st row st' rows states,
        awk_handoff_row_step st row st' ->
        awk_handoff_row_generation_from st' rows states ->
        awk_handoff_row_generation_from st (row :: rows) (st' :: states).

  Definition awk_handoff_row_generation
      (rows : list AwkernelCapturedRow)
      (states : list AwkernelHandoffState) : Prop :=
    awk_handoff_row_generation_from awk_handoff_state0 rows states.

  Lemma awk_handoff_row_step_label :
    forall st row st',
      awk_handoff_row_step st row st' ->
      awk_handoff_labeler st st' = acr_event row.
  Proof.
    intros st row st' Hstep.
    inversion Hstep; subst; try reflexivity.
    unfold awk_handoff_labeler.
    destruct st as [vis ph].
    simpl in *.
    destruct ph as [|[|[|[|[|[|ph']]]]]]; rewrite H; reflexivity.
  Qed.

  Lemma awk_handoff_seed_rows_are_generated :
    awk_handoff_row_generation
      awk_handoff_seed_rows
      [ awk_handoff_state1
      ; awk_handoff_state2
      ; awk_handoff_state3
      ; awk_handoff_state4
      ; awk_handoff_state5
      ; awk_handoff_state6
      ].
  Proof.
    unfold awk_handoff_row_generation, awk_handoff_seed_rows.
    econstructor.
    - exact awk_handoff_row_step_wakeup.
    - econstructor.
      + exact awk_handoff_row_step_request_resched.
      + econstructor.
        * exact awk_handoff_row_step_handle_resched.
        * econstructor.
          -- exact awk_handoff_row_step_choose.
          -- econstructor.
             ++ exact awk_handoff_row_step_dispatch.
             ++ econstructor.
                ** exact awk_handoff_row_step_complete.
                ** constructor.
  Qed.

  Lemma awk_handoff_generated_rows_are_generated :
    awk_handoff_row_generation
      awk_generated_handoff_rows
      [ awk_handoff_state1
      ; awk_handoff_state2
      ; awk_handoff_state3
      ; awk_handoff_state4
      ; awk_handoff_state5
      ; awk_handoff_state6
      ].
  Proof.
    rewrite <- awk_handoff_seed_rows_eq_generated.
    exact awk_handoff_seed_rows_are_generated.
  Qed.

End AwkernelHandoffTraceFamily.
