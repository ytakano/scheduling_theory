From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia Logic.FunctionalExtensionality.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Multicore.Common.MultiCoreBase.
From RocqSched Require Import Operational.Common.State.
From RocqSched Require Import Operational.Common.Step.
From RocqSched Require Import Operational.Common.Invariants.
From RocqSched Require Import Operational.Common.StepLemmas.
From RocqSched Require Import Operational.Common.Projection.
From RocqSched Require Import Operational.Common.ConcreteExecution.
From RocqSched Require Import Operational.Common.LabeledExecution.
From RocqSched Require Import Operational.Common.OSLocalAdapterContract.
From RocqSched Require Import Operational.Common.OSProjectionInterface.
From RocqSched Require Import Operational.Awkernel.MinimalProjection.
Import ListNotations.

Section AwkernelBaselineTrace.

  Definition awk_baseline_job : Job := mkJob 0 0 1 1 10.

  Definition awk_baseline_jobs (_ : JobId) : Job := awk_baseline_job.

  Definition awk_baseline_admissibility : admissible_cpu :=
    fun _ c => c = 0.

  Definition awk_baseline_state0 : AwkernelState :=
    mkAwkernelState (fun _ => None) [] (fun _ => false) (fun _ => None).

  Definition awk_baseline_state1 : AwkernelState :=
    mkAwkernelState (fun _ => None) [0] (fun _ => false) (fun _ => None).

  Definition awk_baseline_state2 : AwkernelState :=
    mkAwkernelState
      (fun _ => None)
      [0]
      (fun _ => false)
      (fun c => if Nat.eqb c 0 then Some 0 else None).

  Definition awk_baseline_state3 : AwkernelState :=
    mkAwkernelState
      (fun c => if Nat.eqb c 0 then Some 0 else None)
      []
      (fun _ => false)
      (fun _ => None).

  Definition awk_baseline_state4 : AwkernelState :=
    mkAwkernelState
      (fun _ => None)
      []
      (fun c => if Nat.eqb c 0 then true else false)
      (fun _ => None).

  Definition awk_baseline_trace (t : Time) : AwkernelState :=
    match t with
    | 0 => awk_baseline_state0
    | 1 => awk_baseline_state1
    | 2 => awk_baseline_state2
    | 3 => awk_baseline_state3
    | _ => awk_baseline_state4
    end.

  Definition awk_baseline_phase (st : AwkernelState) : nat :=
    match awk_current st 0,
          awk_runnable st,
          awk_need_resched st 0,
          awk_dispatch_target st 0 with
    | None, [], false, None => 0
    | None, [0], false, None => 1
    | None, [0], false, Some 0 => 2
    | Some 0, [], false, None => 3
    | None, [], true, None => 4
    | _, _, _, _ => 5
    end.

  Definition awk_baseline_labeler (st st' : AwkernelState) : OpEvent :=
    match awk_baseline_phase st, awk_baseline_phase st' with
    | 0, 1 => EvWakeup 0
    | 1, 2 => EvChoose 0 0
    | 2, 3 => EvDispatch 0 0
    | 3, 4 => EvComplete 0
    | _, _ => EvStutter
    end.

  Definition awk_baseline_projection : OSLabeledProjection AwkernelState :=
    awk_labeled_projection awk_baseline_labeler.

  Lemma awk_baseline_state3_is_dispatch :
    awk_to_op_state awk_baseline_state3 =
    dispatch_on_cpu 0 0 (awk_to_op_state awk_baseline_state2).
  Proof.
    unfold awk_to_op_state, awk_baseline_state3, awk_baseline_state2.
    unfold dispatch_on_cpu, clear_need_resched, clear_dispatch_target,
           set_need_resched, set_dispatch_target.
    simpl.
    repeat f_equal; try reflexivity.
    all: extensionality c; destruct (Nat.eqb_spec c 0); reflexivity.
  Qed.

  Lemma awk_baseline_state4_is_complete :
    awk_to_op_state awk_baseline_state4 =
    clear_current_and_request 0 (awk_to_op_state awk_baseline_state3).
  Proof.
    unfold awk_to_op_state, awk_baseline_state4, awk_baseline_state3,
           clear_current_and_request.
    simpl.
    repeat f_equal; try reflexivity.
    all: extensionality c; destruct (Nat.eqb_spec c 0); reflexivity.
  Qed.

  Lemma awk_baseline_struct_inv :
    forall t, op_struct_inv 1 (awk_to_op_state (awk_baseline_trace t)).
  Proof.
    intros [|[|[|[|t']]]]; constructor; simpl.
    - intros j c1 c2 Hlt1 Hlt2 Hrun1 Hrun2. discriminate.
    - constructor.
    - intros c j Hcur. discriminate Hcur.
    - intros j c1 c2 Hlt1 Hlt2 Ht1 Ht2. discriminate.
    - intros c j Hlt Ht. discriminate.
    - intros j c1 c2 Hlt1 Hlt2 Hrun1 Hrun2. discriminate.
    - constructor.
      + simpl. tauto.
      + constructor.
    - intros c j Hcur. discriminate Hcur.
    - intros j c1 c2 Hlt1 Hlt2 Ht1 Ht2. discriminate.
    - intros c j Hlt Ht. discriminate.
    - intros j c1 c2 Hlt1 Hlt2 Hrun1 Hrun2. discriminate.
    - constructor.
      + simpl. tauto.
      + constructor.
    - intros c j Hcur Hin. discriminate Hcur.
    - intros j c1 c2 Hlt1 Hlt2 Ht1 Ht2.
      destruct c1, c2; simpl in *; try lia; inversion Ht1; inversion Ht2; reflexivity.
    - intros c j Hlt Ht.
      destruct c; simpl in *; try lia; inversion Ht; subst; simpl; auto.
    - intros j c1 c2 Hlt1 Hlt2 Hrun1 Hrun2.
      destruct c1; simpl in Hrun1.
      + destruct c2; simpl in Hrun2; try discriminate.
        inversion Hrun1; inversion Hrun2; reflexivity.
      + lia.
    - constructor.
    - intros c j Hcur. simpl. tauto.
    - intros j c1 c2 Hlt1 Hlt2 Ht1 Ht2. discriminate.
    - intros c j Hlt Ht. discriminate.
    - intros j c1 c2 Hlt1 Hlt2 Hrun1 Hrun2. discriminate.
    - constructor.
    - intros c j Hcur. discriminate.
    - intros j c1 c2 Hlt1 Hlt2 Ht1 Ht2. discriminate.
    - intros c j Hlt Ht. discriminate.
  Qed.

  Lemma awk_baseline_stepwise :
    forall t,
      op_step
        (awk_to_op_state (awk_baseline_trace t))
        (awk_baseline_labeler (awk_baseline_trace t) (awk_baseline_trace (S t)))
        (awk_to_op_state (awk_baseline_trace (S t))).
  Proof.
    intros [|[|[|[|t']]]].
    - simpl. apply step_wakeup.
    - simpl. apply step_choose.
      + simpl. auto.
      + reflexivity.
      + intros [c Hpending]. destruct c; simpl in Hpending; discriminate.
    - simpl. rewrite awk_baseline_state3_is_dispatch.
      apply step_dispatch; [reflexivity | reflexivity].
    - simpl. rewrite awk_baseline_state4_is_complete.
      eapply step_complete.
      exists 0. reflexivity.
    - simpl. apply step_stutter.
  Qed.

  Lemma awk_baseline_lce_stepwise :
    forall t,
      op_step
        (os_to_op_state (osl_to_os_projection awk_baseline_projection)
           (awk_baseline_trace t))
        (os_step_label awk_baseline_projection
           (awk_baseline_trace t)
           (awk_baseline_trace (S t)))
        (os_to_op_state (osl_to_os_projection awk_baseline_projection)
           (awk_baseline_trace (S t))).
  Proof.
    exact awk_baseline_stepwise.
  Qed.

  Lemma awk_baseline_lce_struct_inv :
    forall t,
      op_struct_inv 1
        (os_to_op_state (osl_to_os_projection awk_baseline_projection)
           (awk_baseline_trace t)).
  Proof.
    exact awk_baseline_struct_inv.
  Qed.

  Definition awk_baseline_execution : labeled_concrete_execution awk_baseline_projection 1 :=
    {|
      lce_trace := awk_baseline_trace;
      lce_init := True;
      lce_stepwise := awk_baseline_lce_stepwise;
      lce_struct_inv := awk_baseline_lce_struct_inv;
    |}.

  Lemma awk_baseline_local_sound :
    awk_local_labeled_concrete_multicore_projection_sound
      awk_baseline_projection
      awk_baseline_jobs
      awk_baseline_admissibility
      1
      awk_baseline_execution.
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
      + intros [|[|[|[|t']]]] c j Hlt Hcur.
        * simpl in Hcur. discriminate.
        * simpl in Hcur. discriminate.
        * destruct c; simpl in *.
          -- inversion Hcur; subst. right. left. reflexivity.
          -- lia.
        * simpl in Hcur. discriminate.
        * simpl in Hcur. discriminate.
      + intros t c j Hlt Hlbl.
        destruct t as [|[|[|[|t']]]]; inversion Hlbl; subst.
        unfold released, awk_baseline_jobs, awk_baseline_job. simpl. lia.
      + intros t j Hlbl.
        destruct t as [|[|[|[|t']]]]; inversion Hlbl; subst.
        unfold released, awk_baseline_jobs, awk_baseline_job. simpl. lia.
      + intros t j Hlbl.
        destruct t as [|[|[|[|t']]]]; inversion Hlbl; subst.
        unfold completed, service_job, cpu_count, runs_on,
               project_schedule, osl_to_op_trace, os_to_op_trace,
               awk_to_op_trace, awk_baseline_trace, awk_to_op_state,
               awk_baseline_jobs, awk_baseline_job.
        simpl. lia.
      + intros [|[|[|[|t']]]] c j Hlt Hcur Hnext.
        * simpl in Hcur. discriminate.
        * simpl in Hcur. discriminate.
        * simpl in Hcur. discriminate.
        * simpl in Hnext. discriminate.
        * simpl in Hcur. discriminate.
      + intros t c Hlt Hlbl. destruct t as [|[|[|[|t']]]]; inversion Hlbl.
      + intros t c Hlt Hlbl. destruct t as [|[|[|[|t']]]]; inversion Hlbl.
      + intros t c j Hlt Hlbl.
        destruct t as [|[|[|[|t']]]]; try solve [inversion Hlbl].
        inversion Hlbl; subst. simpl. reflexivity.
      + intros t c j Hlt Hlbl.
        destruct t as [|[|[|[|t']]]]; try solve [inversion Hlbl].
        inversion Hlbl; subst. simpl. auto.
      + intros t c j Hlt Hlbl.
        destruct t as [|[|[|[|t']]]]; try solve [inversion Hlbl].
        unfold completed, service_job, cpu_count, runs_on,
               project_schedule, osl_to_op_trace, os_to_op_trace,
               awk_to_op_trace, awk_baseline_trace, awk_to_op_state,
               awk_baseline_jobs, awk_baseline_job.
        simpl. lia.
      + intros t c j Hlbl. destruct t as [|[|[|[|t']]]]; inversion Hlbl.
      + intros t j Hlbl. destruct t as [|[|[|[|t']]]]; inversion Hlbl.
      + intros t c j Hlt Hlbl. destruct t as [|[|[|[|t']]]]; inversion Hlbl.
      + intros t j Hlbl.
        destruct t as [|[|[|[|t']]]]; try solve [inversion Hlbl].
        inversion Hlbl; subst.
        vm_compute. lia.
      + intros t c old new Hlt Hlbl. destruct t as [|[|[|[|t']]]]; inversion Hlbl.
      + intros t c old new Hlt Hlbl. destruct t as [|[|[|[|t']]]]; inversion Hlbl.
      + intros t c old new Hlt Hlbl. destruct t as [|[|[|[|t']]]]; inversion Hlbl.
    - intros t c Hge.
      destruct t as [|[|[|[|t']]]]; destruct c; simpl; auto; lia.
    - intros t c j Hlt Hcur.
      destruct c; simpl in Hcur.
      + inversion Hcur; subst.
        unfold awk_baseline_admissibility. reflexivity.
      + lia.
  Qed.

  Definition awk_baseline_contract : awk_local_adapter_contract
    awk_baseline_projection awk_baseline_jobs awk_baseline_admissibility 1 :=
    {|
      olac_execution := awk_baseline_execution;
      olac_sound := awk_baseline_local_sound;
    |}.

  Example awk_baseline_contract_valid_schedule :
    valid_schedule
      awk_baseline_jobs
      1
      (project_schedule
         (lex_trace (concrete_to_labeled_execution (olac_execution awk_baseline_contract)))).
  Proof.
    apply awk_local_adapter_contract_implies_valid_schedule.
  Qed.

End AwkernelBaselineTrace.
