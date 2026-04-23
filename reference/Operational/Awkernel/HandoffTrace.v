From Stdlib Require Import List String Bool Arith Arith.PeanoNat Lia Logic.FunctionalExtensionality.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Multicore.Common.MultiCoreBase.
From RocqSched Require Import Operational.Common.State.
From RocqSched Require Import Operational.Common.Step.
From RocqSched Require Import Operational.Common.Invariants.
From RocqSched Require Import Operational.Common.Projection.
From RocqSched Require Import Operational.Common.ConcreteExecution.
From RocqSched Require Import Operational.Common.LabeledExecution.
From RocqSched Require Import Operational.Common.OSLocalAdapterContract.
From RocqSched Require Import Operational.Common.OSProjectionInterface.
From RocqSched Require Import Refinement.OSRefinementTheorem.
From RocqSched Require Import Operational.Awkernel.Minimal.MinimalProjection.
From RocqSched Require Import Operational.Awkernel.BaselineTrace.
Import ListNotations.

Section AwkernelHandoffTrace.

  Record AwkernelHandoffState : Type := mkAwkernelHandoffState {
    awk_handoff_visible : AwkernelState;
    awk_handoff_phase : nat;
  }.

  Definition awk_handoff_to_op_state (st : AwkernelHandoffState) : OpState :=
    awk_to_op_state (awk_handoff_visible st).

  Definition awk_handoff_state0 : AwkernelHandoffState :=
    mkAwkernelHandoffState awk_baseline_state0 0.

  Definition awk_handoff_state1 : AwkernelHandoffState :=
    mkAwkernelHandoffState awk_baseline_state1 1.

  Definition awk_handoff_request_visible : AwkernelState :=
    mkAwkernelState
      (fun _ => None)
      [1]
      (fun c => if Nat.eqb c 1 then true else false)
      (fun _ => None).

  Definition awk_handoff_state2 : AwkernelHandoffState :=
    mkAwkernelHandoffState awk_handoff_request_visible 2.

  Definition awk_handoff_state3 : AwkernelHandoffState :=
    mkAwkernelHandoffState awk_handoff_request_visible 3.

  Definition awk_handoff_choose_visible : AwkernelState :=
    mkAwkernelState
      (fun _ => None)
      [1]
      (fun c => if Nat.eqb c 1 then true else false)
      (fun c => if Nat.eqb c 1 then Some 1 else None).

  Definition awk_handoff_state4 : AwkernelHandoffState :=
    mkAwkernelHandoffState awk_handoff_choose_visible 4.

  Definition awk_handoff_state5 : AwkernelHandoffState :=
    mkAwkernelHandoffState awk_baseline_state3 5.

  Definition awk_handoff_state6 : AwkernelHandoffState :=
    mkAwkernelHandoffState awk_baseline_state4 6.

  Definition awk_handoff_trace (t : Time) : AwkernelHandoffState :=
    match t with
    | 0 => awk_handoff_state0
    | 1 => awk_handoff_state1
    | 2 => awk_handoff_state2
    | 3 => awk_handoff_state3
    | 4 => awk_handoff_state4
    | 5 => awk_handoff_state5
    | _ => awk_handoff_state6
    end.

  Definition awk_handoff_labeler
      (st st' : AwkernelHandoffState) : OpEvent :=
    match awk_handoff_phase st, awk_handoff_phase st' with
    | 0, 1 => EvWakeup 1
    | 1, 2 => EvRequestResched 1
    | 2, 3 => EvHandleResched 1
    | 3, 4 => EvChoose 1 1
    | 4, 5 => EvDispatch 1 1
    | 5, 6 => EvComplete 1
    | _, _ => EvStutter
    end.

  Definition awk_handoff_projection : OSLabeledProjection AwkernelHandoffState :=
    mkOSLabeledProjection
      AwkernelHandoffState
      (mkOSProjection AwkernelHandoffState awk_handoff_to_op_state)
      awk_handoff_labeler.

  Lemma awk_handoff_state5_is_dispatch :
    awk_handoff_to_op_state awk_handoff_state5 =
    dispatch_on_cpu 1 1 (awk_handoff_to_op_state awk_handoff_state4).
  Proof.
    unfold awk_handoff_to_op_state, awk_handoff_state5, awk_handoff_state4,
           awk_handoff_choose_visible, awk_to_op_state, awk_baseline_state3.
    unfold dispatch_on_cpu, clear_need_resched, clear_dispatch_target,
           set_need_resched, set_dispatch_target.
    simpl.
    repeat f_equal; try reflexivity.
    all: extensionality c; destruct (Nat.eqb_spec c 1); reflexivity.
  Qed.

  Lemma awk_handoff_state6_is_complete :
    awk_handoff_to_op_state awk_handoff_state6 =
    clear_current_and_request 1 (awk_handoff_to_op_state awk_handoff_state5).
  Proof.
    unfold awk_handoff_to_op_state, awk_handoff_state6, awk_handoff_state5,
           awk_to_op_state, awk_baseline_state4, awk_baseline_state3,
           clear_current_and_request.
    simpl.
    repeat f_equal; try reflexivity.
    all: extensionality c; destruct (Nat.eqb_spec c 1); reflexivity.
  Qed.

  Lemma awk_handoff_state3_is_handle :
    awk_handoff_to_op_state awk_handoff_state3 =
    set_need_resched 1 true (awk_handoff_to_op_state awk_handoff_state2).
  Proof.
    unfold awk_handoff_to_op_state, awk_handoff_state2, awk_handoff_state3,
           awk_handoff_request_visible, awk_to_op_state, set_need_resched.
    simpl.
    repeat f_equal; try reflexivity.
    extensionality c.
    destruct (Nat.eqb_spec c 1); reflexivity.
  Qed.

  Lemma awk_handoff_request_struct_inv :
    op_struct_inv 2 (awk_handoff_to_op_state awk_handoff_state2).
  Proof.
    refine (mkOpStructInv 2 (awk_handoff_to_op_state awk_handoff_state2) _ _ _ _ _).
    - intros j c1 c2 Hlt1 Hlt2 Hrun1 Hrun2. discriminate.
    - constructor.
      + simpl. tauto.
      + constructor.
    - intros c j Hcur. discriminate Hcur.
    - intros j c1 c2 Hlt1 Hlt2 Ht1 Ht2. discriminate.
    - intros c j Hlt Ht. discriminate.
  Qed.

  Lemma awk_handoff_choose_struct_inv :
    op_struct_inv 2 (awk_handoff_to_op_state awk_handoff_state4).
  Proof.
    refine (mkOpStructInv 2 (awk_handoff_to_op_state awk_handoff_state4) _ _ _ _ _).
    - intros j c1 c2 Hlt1 Hlt2 Hrun1 Hrun2. discriminate.
    - constructor.
      + simpl. tauto.
      + constructor.
    - intros c j Hcur. discriminate Hcur.
    - intros j c1 c2 Hlt1 Hlt2 Ht1 Ht2.
      assert (c1 = 1) as ->.
      { destruct c1 as [|[|c1']]; simpl in *; try lia; try discriminate; reflexivity. }
      assert (c2 = 1) as ->.
      { destruct c2 as [|[|c2']]; simpl in *; try lia; try discriminate; reflexivity. }
      reflexivity.
    - intros c j Hlt Ht.
      assert (c = 1) as ->.
      { destruct c as [|[|c']]; simpl in *; try lia; try discriminate; reflexivity. }
      simpl in Ht. inversion Ht; subst. simpl. auto.
  Qed.

  Lemma awk_handoff_struct_inv :
    forall t, op_struct_inv 2 (awk_handoff_to_op_state (awk_handoff_trace t)).
  Proof.
    intros [|[|[|[|[|[|t']]]]]].
    - change (op_struct_inv 2 (awk_to_op_state awk_baseline_state0)).
      exact (awk_baseline_struct_inv 0).
    - change (op_struct_inv 2 (awk_to_op_state awk_baseline_state1)).
      exact (awk_baseline_struct_inv 1).
    - exact awk_handoff_request_struct_inv.
    - exact awk_handoff_request_struct_inv.
    - exact awk_handoff_choose_struct_inv.
    - change (op_struct_inv 2 (awk_to_op_state awk_baseline_state3)).
      exact (awk_baseline_struct_inv 3).
    - change (op_struct_inv 2 (awk_to_op_state awk_baseline_state4)).
      exact (awk_baseline_struct_inv 4).
  Qed.

  Lemma awk_handoff_stepwise :
    forall t,
      op_step
        (awk_handoff_to_op_state (awk_handoff_trace t))
        (awk_handoff_labeler (awk_handoff_trace t) (awk_handoff_trace (S t)))
        (awk_handoff_to_op_state (awk_handoff_trace (S t))).
  Proof.
    intros [|[|[|[|[|[|t']]]]]].
    - simpl. apply step_wakeup.
    - unfold awk_handoff_labeler, awk_handoff_to_op_state,
             awk_handoff_state1, awk_handoff_state2,
             awk_handoff_request_visible, awk_to_op_state.
      simpl. apply step_request_resched.
    - simpl.
      rewrite awk_handoff_state3_is_handle.
      apply step_handle_resched.
    - unfold awk_handoff_labeler, awk_handoff_to_op_state,
             awk_handoff_state3, awk_handoff_state4,
             awk_handoff_request_visible, awk_handoff_choose_visible,
             awk_to_op_state.
      simpl. apply step_choose.
      + simpl. auto.
      + reflexivity.
      + intros [c Hpending]. destruct c as [|[|c']]; simpl in Hpending; discriminate.
    - simpl. rewrite awk_handoff_state5_is_dispatch.
      apply step_dispatch; [reflexivity | reflexivity].
    - simpl. rewrite awk_handoff_state6_is_complete.
      eapply step_complete.
      exists 1. reflexivity.
    - simpl. apply step_stutter.
  Qed.

  Lemma awk_handoff_lce_stepwise :
    forall t,
      op_step
        (os_to_op_state (osl_to_os_projection awk_handoff_projection)
           (awk_handoff_trace t))
        (os_step_label awk_handoff_projection
           (awk_handoff_trace t)
           (awk_handoff_trace (S t)))
        (os_to_op_state (osl_to_os_projection awk_handoff_projection)
           (awk_handoff_trace (S t))).
  Proof.
    exact awk_handoff_stepwise.
  Qed.

  Lemma awk_handoff_lce_struct_inv :
    forall t,
      op_struct_inv 2
        (os_to_op_state (osl_to_os_projection awk_handoff_projection)
           (awk_handoff_trace t)).
  Proof.
    exact awk_handoff_struct_inv.
  Qed.

  Definition awk_handoff_execution : labeled_concrete_execution awk_handoff_projection 2 :=
    {|
      lce_trace := awk_handoff_trace;
      lce_init := True;
      lce_stepwise := awk_handoff_lce_stepwise;
      lce_struct_inv := awk_handoff_lce_struct_inv;
    |}.

  Lemma awk_handoff_local_sound :
    @local_labeled_concrete_multicore_projection_sound AwkernelHandoffState
      awk_handoff_projection
      awk_baseline_jobs
      awk_baseline_admissibility
      2
      awk_handoff_execution.
  Proof.
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
      + intros c j Hlt Hcur. simpl in Hcur. discriminate.
      + intros c j Hlt Hcur. simpl in Hcur. discriminate.
      + intros j Hin. simpl in Hin. contradiction.
      + intros j Hin. simpl in Hin. contradiction.
      + intros [|[|[|[|[|[|t']]]]]] c j Hlt Hcur.
        * simpl in Hcur. discriminate.
        * simpl in Hcur. discriminate.
        * simpl in Hcur. discriminate.
        * simpl in Hcur. discriminate.
        * destruct c as [|[|c']]; simpl in *; try lia; try discriminate.
          inversion Hcur; subst. right. left. reflexivity.
        * simpl in Hcur. discriminate.
        * simpl in Hcur. discriminate.
      + intros t c j Hlt Hlbl.
        destruct t as [|[|[|[|[|[|t']]]]]]; try solve [inversion Hlbl].
        inversion Hlbl; subst.
        unfold released, awk_baseline_jobs, awk_baseline_job. simpl. lia.
      + intros t j Hlbl.
        destruct t as [|[|[|[|[|[|t']]]]]]; try solve [inversion Hlbl].
        inversion Hlbl; subst.
        unfold released, awk_baseline_jobs, awk_baseline_job. simpl. lia.
      + intros t j Hlbl.
        destruct t as [|[|[|[|[|[|t']]]]]]; try solve [inversion Hlbl].
        inversion Hlbl; subst.
        unfold completed, service_job, cpu_count, runs_on,
               project_schedule, osl_to_op_trace, os_to_op_trace,
               awk_handoff_trace, awk_handoff_to_op_state,
               awk_baseline_jobs, awk_baseline_job.
        simpl. lia.
      + intros [|[|[|[|[|[|t']]]]]] c j Hlt Hcur Hnext.
        * simpl in Hcur. discriminate.
        * simpl in Hcur. discriminate.
        * simpl in Hcur. discriminate.
        * simpl in Hcur. discriminate.
        * simpl in Hnext. discriminate.
        * simpl in Hcur. discriminate.
        * simpl in Hcur. discriminate.
      + intros t c Hlt Hlbl.
        destruct t as [|[|[|[|[|[|t']]]]]]; try solve [inversion Hlbl].
        inversion Hlbl; subst. simpl. reflexivity.
      + intros t c Hlt Hlbl.
        destruct t as [|[|[|[|[|[|t']]]]]]; try solve [inversion Hlbl].
        inversion Hlbl; subst. simpl. reflexivity.
      + intros t c j Hlt Hlbl.
        destruct t as [|[|[|[|[|[|t']]]]]]; try solve [inversion Hlbl].
        inversion Hlbl; subst. simpl. reflexivity.
      + intros t c j Hlt Hlbl.
        destruct t as [|[|[|[|[|[|t']]]]]]; try solve [inversion Hlbl].
        inversion Hlbl; subst. simpl. auto.
      + intros t c j Hlt Hlbl.
        destruct t as [|[|[|[|[|[|t']]]]]]; try solve [inversion Hlbl].
        unfold completed, service_job, cpu_count, runs_on,
               project_schedule, osl_to_op_trace, os_to_op_trace,
               awk_handoff_trace, awk_handoff_to_op_state,
               awk_baseline_jobs, awk_baseline_job.
        simpl. lia.
      + intros t c j Hlbl.
        destruct t as [|[|[|[|[|[|t']]]]]]; inversion Hlbl.
      + intros t j Hlbl.
        destruct t as [|[|[|[|[|[|t']]]]]]; inversion Hlbl.
      + intros t c j Hlt Hlbl.
        destruct t as [|[|[|[|[|[|t']]]]]]; inversion Hlbl.
      + intros t j Hlbl.
        destruct t as [|[|[|[|[|[|t']]]]]]; try solve [inversion Hlbl].
        inversion Hlbl; subst.
        vm_compute. lia.
      + intros t c old new Hlt Hlbl.
        destruct t as [|[|[|[|[|[|t']]]]]]; inversion Hlbl.
      + intros t c old new Hlt Hlbl.
        destruct t as [|[|[|[|[|[|t']]]]]]; inversion Hlbl.
      + intros t c old new Hlt Hlbl.
        destruct t as [|[|[|[|[|[|t']]]]]]; inversion Hlbl.
    - intros t c Hge.
      destruct t as [|[|[|[|[|[|t']]]]]];
      destruct c as [|[|c']]; simpl; auto; lia.
    - intros t c j Hlt Hcur.
      assert (c = 1) as ->.
      {
        destruct t as [|[|[|[|[|[|t']]]]]];
        destruct c as [|[|c']]; simpl in *; try lia; try discriminate; reflexivity.
      }
      unfold awk_baseline_admissibility. reflexivity.
  Qed.

  Definition awk_handoff_local_adapter_contract :
    @os_local_multicore_adapter_contract AwkernelHandoffState
      awk_handoff_projection
      awk_baseline_jobs
      awk_baseline_admissibility
      2 :=
    {|
      olac_execution := awk_handoff_execution;
      olac_sound := awk_handoff_local_sound;
    |}.

  Example awk_handoff_contract_valid_schedule :
    valid_schedule
      awk_baseline_jobs
      2
      (project_schedule
         (lex_trace
            (concrete_to_labeled_execution
               (olac_execution awk_handoff_local_adapter_contract)))).
  Proof.
    apply os_local_multicore_adapter_contract_implies_valid_schedule.
  Qed.

  Example awk_handoff_request_sets_need_resched :
    op_need_resched
      (os_to_op_state
         (osl_to_os_projection awk_handoff_projection)
         (lce_trace (olac_execution awk_handoff_local_adapter_contract) 2))
      1 = true.
  Proof.
    eapply local_labeled_concrete_projection_sound_request_sets_need_resched.
    - exact (llcmps_projection_sound (olac_sound awk_handoff_local_adapter_contract)).
    - lia.
    - reflexivity.
  Qed.

  Example awk_handoff_handle_sets_need_resched :
    op_need_resched
      (os_to_op_state
         (osl_to_os_projection awk_handoff_projection)
         (lce_trace (olac_execution awk_handoff_local_adapter_contract) 3))
      1 = true.
  Proof.
    eapply os_local_multicore_adapter_contract_handle_sets_need_resched.
    - lia.
    - reflexivity.
  Qed.

End AwkernelHandoffTrace.
