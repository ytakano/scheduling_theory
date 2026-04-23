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

  Definition awk_baseline_job : Job := mkJob 1 0 1 1 10.

  Definition awk_baseline_jobs (_ : JobId) : Job := awk_baseline_job.

  Definition awk_baseline_admissibility : admissible_cpu :=
    fun _ c => c = 1.

  Definition awk_baseline_state0 : AwkernelState :=
    mkAwkernelState (fun _ => None) [] (fun _ => false) (fun _ => None).

  Definition awk_baseline_state1 : AwkernelState :=
    mkAwkernelState (fun _ => None) [1] (fun _ => false) (fun _ => None).

  Definition awk_baseline_state2 : AwkernelState :=
    mkAwkernelState
      (fun _ => None)
      [1]
      (fun _ => false)
      (fun c => if Nat.eqb c 1 then Some 1 else None).

  Definition awk_baseline_state3 : AwkernelState :=
    mkAwkernelState
      (fun c => if Nat.eqb c 1 then Some 1 else None)
      []
      (fun _ => false)
      (fun _ => None).

  Definition awk_baseline_state4 : AwkernelState :=
    mkAwkernelState
      (fun _ => None)
      []
      (fun c => if Nat.eqb c 1 then true else false)
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
    match awk_current st 1,
          awk_runnable st,
          awk_need_resched st 1,
          awk_dispatch_target st 1 with
    | None, [], false, None => 0
    | None, [1], false, None => 1
    | None, [1], false, Some 1 => 2
    | Some 1, [], false, None => 3
    | None, [], true, None => 4
    | _, _, _, _ => 5
    end.

  Definition awk_baseline_labeler (st st' : AwkernelState) : OpEvent :=
    match awk_baseline_phase st, awk_baseline_phase st' with
    | 0, 1 => EvWakeup 1
    | 1, 2 => EvChoose 1 1
    | 2, 3 => EvDispatch 1 1
    | 3, 4 => EvComplete 1
    | _, _ => EvStutter
    end.

  Definition awk_baseline_projection : OSLabeledProjection AwkernelState :=
    awk_labeled_projection awk_baseline_labeler.

  Lemma awk_baseline_state3_is_dispatch :
    awk_to_op_state awk_baseline_state3 =
    dispatch_on_cpu 1 1 (awk_to_op_state awk_baseline_state2).
  Proof.
    unfold awk_to_op_state, awk_baseline_state3, awk_baseline_state2.
    unfold dispatch_on_cpu, clear_need_resched, clear_dispatch_target,
           set_need_resched, set_dispatch_target.
    simpl.
    repeat f_equal; try reflexivity.
    all: extensionality c; destruct (Nat.eqb_spec c 1); reflexivity.
  Qed.

  Lemma awk_baseline_state4_is_complete :
    awk_to_op_state awk_baseline_state4 =
    clear_current_and_request 1 (awk_to_op_state awk_baseline_state3).
  Proof.
    unfold awk_to_op_state, awk_baseline_state4, awk_baseline_state3,
           clear_current_and_request.
    simpl.
    repeat f_equal; try reflexivity.
    all: extensionality c; destruct (Nat.eqb_spec c 1); reflexivity.
  Qed.

  Lemma awk_baseline_struct_inv :
    forall t, op_struct_inv 2 (awk_to_op_state (awk_baseline_trace t)).
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
      assert (c1 = 1) as ->.
      { destruct c1 as [|[|c1']]; simpl in *; try lia; try discriminate; reflexivity. }
      assert (c2 = 1) as ->.
      { destruct c2 as [|[|c2']]; simpl in *; try lia; try discriminate; reflexivity. }
      reflexivity.
    - intros c j Hlt Ht.
      assert (c = 1) as ->.
      { destruct c as [|[|c']]; simpl in *; try lia; try discriminate; reflexivity. }
      simpl in Ht. inversion Ht; subst. simpl. auto.
    - intros j c1 c2 Hlt1 Hlt2 Hrun1 Hrun2.
      assert (c1 = 1) as ->.
      { destruct c1 as [|[|c1']]; simpl in *; try lia; try discriminate; reflexivity. }
      assert (c2 = 1) as ->.
      { destruct c2 as [|[|c2']]; simpl in *; try lia; try discriminate; reflexivity. }
      reflexivity.
    - constructor.
    - intros c j Hcur. destruct c as [|[|c']]; simpl in Hcur; try discriminate; try lia.
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
      + intros [c Hpending]. destruct c as [|[|c']]; simpl in Hpending; discriminate.
    - simpl. rewrite awk_baseline_state3_is_dispatch.
      apply step_dispatch; [reflexivity | reflexivity].
    - simpl. rewrite awk_baseline_state4_is_complete.
      eapply step_complete.
      exists 1. reflexivity.
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
      op_struct_inv 2
        (os_to_op_state (osl_to_os_projection awk_baseline_projection)
           (awk_baseline_trace t)).
  Proof.
    exact awk_baseline_struct_inv.
  Qed.

  Definition awk_baseline_execution : labeled_concrete_execution awk_baseline_projection 2 :=
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
      2
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
        * destruct c as [|[|c']]; simpl in *; try lia; try discriminate.
          inversion Hcur; subst. right. left. reflexivity.
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
      destruct t as [|[|[|[|t']]]]; destruct c as [|[|c']]; simpl; auto; lia.
    - intros t c j Hlt Hcur.
      assert (c = 1) as ->.
      {
        destruct t as [|[|[|[|t']]]];
        destruct c as [|[|c']]; simpl in *; try lia; try discriminate; reflexivity.
      }
      unfold awk_baseline_admissibility. reflexivity.
  Qed.

  Definition awk_baseline_contract : awk_local_adapter_contract
    awk_baseline_projection awk_baseline_jobs awk_baseline_admissibility 2 :=
    {|
      olac_execution := awk_baseline_execution;
      olac_sound := awk_baseline_local_sound;
    |}.

  Example awk_baseline_contract_valid_schedule :
    valid_schedule
      awk_baseline_jobs
      2
      (project_schedule
         (lex_trace (concrete_to_labeled_execution (olac_execution awk_baseline_contract)))).
  Proof.
    apply awk_local_adapter_contract_implies_valid_schedule.
  Qed.

End AwkernelBaselineTrace.
