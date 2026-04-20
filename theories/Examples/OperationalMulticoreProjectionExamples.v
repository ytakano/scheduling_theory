From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia Logic.FunctionalExtensionality.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Semantics.ScheduleLemmas.ScheduleFacts.
From RocqSched Require Import Multicore.Common.MultiCoreBase.
From RocqSched Require Import Multicore.Common.Admissibility.
From RocqSched Require Import Multicore.Common.PlacementFacts.
From RocqSched Require Import Multicore.Common.ValidityFacts.
From RocqSched Require Import Operational.Common.State.
From RocqSched Require Import Operational.Common.Invariants.
From RocqSched Require Import Operational.Common.Projection.
From RocqSched Require Import Operational.Common.Step.
From RocqSched Require Import Operational.Common.StepLemmas.
From RocqSched Require Import Operational.Common.Execution.
From RocqSched Require Import Operational.Common.ConcreteExecution.
From RocqSched Require Import Operational.Common.LabeledExecution.
From RocqSched Require Import Operational.Common.OSProjectionInterface.
From RocqSched Require Import Operational.Common.OSLocalAdapterContract.
From RocqSched Require Import Operational.Common.ProjectionLemmas.
From RocqSched Require Import Operational.Common.ProjectionInvariants.
From RocqSched Require Import Operational.Common.ProjectionMulticoreValidity.
From RocqSched Require Import Operational.Awkernel.MinimalProjection.
Import ListNotations.

Section OperationalMulticoreProjectionExamples.

  Definition mc_job0 : Job := mkJob 0 0 0 3 5.
  Definition mc_job1 : Job := mkJob 1 0 0 2 4.

  Definition mc_jobs (j : JobId) : Job :=
    match j with
    | 0 => mc_job0
    | _ => mc_job1
    end.

  Definition even_odd_admissibility : admissible_cpu :=
    fun j c => j = c.

  Definition mc_running_state : OpState :=
    mkOpState
      (fun c =>
         if Nat.eqb c 0 then Some 0
         else if Nat.eqb c 1 then Some 1
              else None)
      []
      (fun _ => false)
      (fun _ => None).

  Definition mc_idle_state : OpState :=
    mkOpState (fun _ => None) [] (fun _ => false) (fun _ => None).

  Definition mc_trace (t : Time) : OpState :=
    match t with
    | 0 => mc_running_state
    | _ => mc_idle_state
    end.

  Lemma mc_running_state_cpu_job :
    forall c j,
      c < 2 ->
      op_current mc_running_state c = Some j ->
      c = j.
  Proof.
    intros c j Hlt Hrun.
    assert (Hc : c = 0 \/ c = 1) by lia.
    destruct Hc as [-> | ->]; simpl in Hrun; inversion Hrun; subst; reflexivity.
  Qed.

  Lemma mc_trace_projectable :
    projectable_trace mc_jobs 2 mc_trace.
  Proof.
    constructor.
    - intros [|t'] j c1 c2 Hlt1 Hlt2 Hrun1 Hrun2.
      + pose proof (mc_running_state_cpu_job c1 j Hlt1 Hrun1) as ->.
        pose proof (mc_running_state_cpu_job c2 j Hlt2 Hrun2) as ->.
        reflexivity.
      + unfold mc_trace, mc_idle_state in Hrun1.
        simpl in Hrun1.
        discriminate.
    - intros [|t'] c j Hlt Hrun.
      + assert (Hcpu : c = 0 \/ c = 1) by lia.
        destruct Hcpu as [-> | ->]; simpl in Hrun; inversion Hrun; subst;
          unfold released, mc_jobs, mc_job0, mc_job1; simpl; lia.
      + unfold mc_trace, mc_idle_state in Hrun.
        simpl in Hrun.
        discriminate.
    - intros [|t'] c j Hlt Hrun.
      + assert (Hcpu : c = 0 \/ c = 1) by lia.
        destruct Hcpu as [-> | ->]; simpl in Hrun; inversion Hrun; subst;
          unfold completed, service_job, cpu_count, runs_on, project_schedule,
                 mc_trace, mc_running_state, mc_jobs, mc_job0, mc_job1; simpl; lia.
      + unfold mc_trace, mc_idle_state in Hrun.
        simpl in Hrun.
        discriminate.
  Qed.

  Lemma mc_trace_idle_outside_range :
    forall t, op_idle_outside_range 2 (mc_trace t).
  Proof.
    intros [|t'] c Hge.
    - unfold mc_trace, mc_running_state.
      simpl.
      destruct (Nat.eqb c 0) eqn:Ec0.
      + apply Nat.eqb_eq in Ec0. lia.
      + destruct (Nat.eqb c 1) eqn:Ec1.
        * apply Nat.eqb_eq in Ec1. lia.
        * reflexivity.
    - reflexivity.
  Qed.

  Lemma mc_trace_respects_admissibility :
    forall t, op_respects_admissibility even_odd_admissibility 2 (mc_trace t).
  Proof.
    intros [|t'] c j Hlt Hrun.
    - assert (Hcpu : c = 0 \/ c = 1) by lia.
      destruct Hcpu as [-> | ->]; simpl in Hrun; inversion Hrun; subst;
        unfold even_odd_admissibility; reflexivity.
    - unfold mc_trace, mc_idle_state in Hrun.
      simpl in Hrun.
      discriminate.
  Qed.

  Example projected_schedule_respects_admissibility :
    schedule_respects_admissibility even_odd_admissibility 2 (project_schedule mc_trace).
  Proof.
    apply op_respects_admissibility_projected.
    exact mc_trace_respects_admissibility.
  Qed.

  Example projected_schedule_has_multicore_semantic_validity :
    multicore_semantic_validity mc_jobs 2 (project_schedule mc_trace).
  Proof.
    apply projectable_trace_with_range_implies_multicore_semantic_validity.
    - exact mc_trace_projectable.
    - exact mc_trace_idle_outside_range.
  Qed.

  Definition awk_state : AwkernelState :=
    mkAwkernelState (fun _ => None) [] (fun _ => false) (fun _ => None).

  Definition awk_trace (_ : Time) : AwkernelState := awk_state.

  Lemma awk_struct_inv :
    forall t, op_struct_inv 2 (awk_to_op_state (awk_trace t)).
  Proof.
    intros t.
    constructor.
      - intros j c1 c2 Hlt1 Hlt2 Hrun1 Hrun2.
        simpl in Hrun1.
        discriminate.
      - constructor.
    - intros c j Hrun Hin.
      simpl in Hin.
      contradiction.
      - intros j c1 c2 Hlt1 Hlt2 Ht1 Ht2.
        simpl in Ht1.
        discriminate.
      - intros c j Hlt Ht.
        simpl in Ht.
        discriminate.
  Qed.

  Definition awk_execution_ex : awk_execution 2 :=
    mkAwkExecution 2 awk_trace True (fun _ => ex_intro _ EvStutter (step_stutter _)) awk_struct_inv.

  Lemma awk_execution_projection_sound :
    awk_multicore_projection_sound mc_jobs even_odd_admissibility 2 awk_execution_ex.
  Proof.
    constructor.
    - constructor.
      + intros t c j Hlt Hrun.
        unfold awk_trace, awk_state in Hrun.
        simpl in Hrun.
        discriminate.
      + intros t c j Hlt Hrun.
        unfold awk_trace, awk_state in Hrun.
        simpl in Hrun.
        discriminate.
    - intros t.
      unfold awk_trace, awk_state, awk_idle_outside_range, op_idle_outside_range.
      intros c Hge.
      reflexivity.
    - intros t c j Hlt Hrun.
      unfold awk_trace, awk_state, awk_respects_admissibility,
             op_respects_admissibility, even_odd_admissibility in *.
      simpl in Hrun.
      discriminate.
  Qed.

  Example awk_projection_has_multicore_semantic_validity :
    multicore_semantic_validity mc_jobs 2 (awk_project_schedule (awk_ex_trace awk_execution_ex)).
  Proof.
    eapply awk_multicore_projection_sound_implies_semantic_validity.
    exact awk_execution_projection_sound.
  Qed.

  Definition awk_handoff_job : Job := mkJob 0 0 0 2 10.

  Definition awk_handoff_jobs (_ : JobId) : Job := awk_handoff_job.

  Definition awk_single_cpu_admissibility : admissible_cpu :=
    fun _ c => c = 0.

  Definition awk_handoff_state0 : AwkernelState :=
    mkAwkernelState
      (fun _ => None)
      [0]
      (fun _ => false)
      (fun _ => None).

  Definition awk_handoff_state1 : AwkernelState :=
    mkAwkernelState
      (fun _ => None)
      [0]
      (fun c => if Nat.eqb c 0 then true else false)
      (fun _ => None).

  Definition awk_handoff_state2 : AwkernelState :=
    mkAwkernelState
      (fun _ => None)
      [0]
      (fun c => if Nat.eqb c 0 then true else false)
      (fun c => if Nat.eqb c 0 then Some 0 else None).

  Definition awk_handoff_state3 : AwkernelState :=
    mkAwkernelState
      (fun c => if Nat.eqb c 0 then Some 0 else awk_current awk_handoff_state2 c)
      (remove_job 0 (awk_runnable awk_handoff_state2))
      (fun c => if Nat.eqb c 0 then false else awk_need_resched awk_handoff_state2 c)
      (fun c => if Nat.eqb c 0 then None else awk_dispatch_target awk_handoff_state2 c).

  Definition awk_handoff_state4 : AwkernelState :=
    mkAwkernelState
      (fun c =>
         match awk_current awk_handoff_state3 c with
         | Some j' => if Nat.eqb j' 0 then None else Some j'
         | None => None
         end)
      (remove_job 0 (awk_runnable awk_handoff_state3))
      (fun c =>
         match awk_current awk_handoff_state3 c with
         | Some j' => if Nat.eqb j' 0 then true else awk_need_resched awk_handoff_state3 c
         | None => awk_need_resched awk_handoff_state3 c
         end)
      (awk_dispatch_target awk_handoff_state3).

  Definition awk_handoff_trace (t : Time) : AwkernelState :=
    match t with
    | 0 => awk_handoff_state0
    | 1 => awk_handoff_state1
    | 2 => awk_handoff_state2
    | 3 => awk_handoff_state3
    | _ => awk_handoff_state4
    end.

  Definition awk_handoff_phase_code (st : AwkernelState) : nat :=
    match awk_current st 0,
          awk_runnable st,
          awk_need_resched st 0,
          awk_dispatch_target st 0 with
    | None, [0], false, None => 0
    | None, [0], true, None => 1
    | None, [0], true, Some 0 => 2
    | Some 0, [], false, None => 3
    | None, [], true, None => 4
    | _, _, _, _ => 5
    end.

  Definition awk_handoff_labeler (st st' : AwkernelState) : OpEvent :=
    match awk_handoff_phase_code st, awk_handoff_phase_code st' with
    | 0, 1 => EvHandleResched 0
    | 1, 2 => EvChoose 0 0
    | 2, 3 => EvDispatch 0 0
    | 3, 4 => EvBlock 0
    | _, _ => EvStutter
    end.

  Definition awk_handoff_projection : OSLabeledProjection AwkernelState :=
    awk_labeled_projection awk_handoff_labeler.

  Lemma awk_handoff_state3_is_dispatch :
    awk_to_op_state awk_handoff_state3 =
    dispatch_on_cpu 0 0 (awk_to_op_state awk_handoff_state2).
  Proof.
    unfold awk_to_op_state, awk_handoff_state3, awk_handoff_state2.
    unfold dispatch_on_cpu, clear_need_resched, clear_dispatch_target,
           set_need_resched, set_dispatch_target.
    reflexivity.
  Qed.

  Lemma awk_handoff_state4_is_block :
    awk_to_op_state awk_handoff_state4 =
    clear_current_and_request 0 (awk_to_op_state awk_handoff_state3).
  Proof.
    unfold awk_to_op_state, awk_handoff_state4, awk_handoff_state3,
           clear_current_and_request.
    reflexivity.
  Qed.

  Lemma awk_handoff_struct_inv :
    forall t, op_struct_inv 1 (awk_to_op_state (awk_handoff_trace t)).
  Proof.
    intros [|[|[|[|t']]]].
    - constructor.
      + intros j c1 c2 Hlt1 Hlt2 Hrun1 Hrun2.
        simpl in Hrun1. discriminate.
      + constructor.
        * simpl. tauto.
        * constructor.
      + intros c j Hcur Hin.
        simpl in Hcur. discriminate.
      + intros j c1 c2 Hlt1 Hlt2 Ht1 Ht2.
        simpl in Ht1. discriminate.
      + intros c j Hlt Ht.
        simpl in Ht. discriminate.
    - constructor.
      + intros j c1 c2 Hlt1 Hlt2 Hrun1 Hrun2.
        simpl in Hrun1. discriminate.
      + constructor.
        * simpl. tauto.
        * constructor.
      + intros c j Hcur Hin.
        simpl in Hcur. discriminate.
      + intros j c1 c2 Hlt1 Hlt2 Ht1 Ht2.
        simpl in Ht1. discriminate.
      + intros c j Hlt Ht.
        simpl in Ht. discriminate.
    - constructor.
      + intros j c1 c2 Hlt1 Hlt2 Hrun1 Hrun2.
        simpl in Hrun1. discriminate.
      + constructor.
        * simpl. tauto.
        * constructor.
      + intros c j Hcur Hin.
        simpl in Hcur. discriminate.
      + intros j c1 c2 Hlt1 Hlt2 Ht1 Ht2.
        assert (c1 = 0) by lia.
        assert (c2 = 0) by lia.
        subst c1 c2. reflexivity.
      + intros c j Hlt Ht.
        assert (c = 0) by lia.
        subst c.
        inversion Ht; subst.
        simpl.
        left.
        reflexivity.
    - constructor.
      + intros j c1 c2 Hlt1 Hlt2 Hrun1 Hrun2.
        assert (c1 = 0) by lia.
        assert (c2 = 0) by lia.
        subst c1 c2. reflexivity.
      + constructor.
      + intros c j Hcur Hin.
        simpl in Hin.
        contradiction.
      + intros j c1 c2 Hlt1 Hlt2 Ht1 Ht2.
        simpl in Ht1.
        destruct (Nat.eqb c1 0); discriminate.
      + intros c j Hlt Ht.
        simpl in Ht.
        destruct (Nat.eqb c 0); discriminate.
    - constructor.
      + intros j c1 c2 Hlt1 Hlt2 Hrun1 Hrun2.
        simpl in Hrun1.
        destruct (Nat.eqb c1 0); discriminate.
      + constructor.
      + intros c j Hcur Hin.
        simpl in Hcur.
        destruct (Nat.eqb c 0); discriminate.
      + intros j c1 c2 Hlt1 Hlt2 Ht1 Ht2.
        simpl in Ht1.
        destruct (Nat.eqb c1 0); discriminate.
      + intros c j Hlt Ht.
        simpl in Ht.
        destruct (Nat.eqb c 0); discriminate.
  Qed.

  Lemma awk_handoff_stepwise :
    forall t,
      op_step
        (os_to_op_state (osl_to_os_projection awk_handoff_projection) (awk_handoff_trace t))
        (os_step_label awk_handoff_projection (awk_handoff_trace t) (awk_handoff_trace (S t)))
        (os_to_op_state (osl_to_os_projection awk_handoff_projection) (awk_handoff_trace (S t))).
  Proof.
    intros [|[|[|[|t']]]].
    - unfold awk_handoff_projection, awk_labeled_projection,
             awk_handoff_labeler, awk_handoff_phase_code.
      simpl.
      repeat rewrite Nat.eqb_refl.
      apply step_handle_resched.
    - unfold awk_handoff_projection, awk_labeled_projection,
             awk_handoff_labeler, awk_handoff_phase_code.
      simpl.
      repeat rewrite Nat.eqb_refl.
      apply step_choose.
      + simpl. left. reflexivity.
      + reflexivity.
      + intros [c Hpending].
        simpl in Hpending.
        destruct (Nat.eqb c 0); discriminate.
    - unfold awk_handoff_projection, awk_labeled_projection,
             awk_handoff_labeler, awk_handoff_phase_code.
      simpl.
      repeat rewrite Nat.eqb_refl.
      rewrite awk_handoff_state3_is_dispatch.
      apply step_dispatch; reflexivity.
    - unfold awk_handoff_projection, awk_labeled_projection,
             awk_handoff_labeler, awk_handoff_phase_code.
      simpl.
      repeat rewrite Nat.eqb_refl.
      rewrite awk_handoff_state4_is_block.
      apply step_block. exists 0. reflexivity.
    - unfold awk_handoff_projection, awk_labeled_projection,
             awk_handoff_labeler, awk_handoff_phase_code.
      simpl.
      repeat rewrite Nat.eqb_refl.
      apply step_stutter.
  Qed.

  Definition awk_handoff_execution :
      labeled_concrete_execution awk_handoff_projection 1 :=
    @mkLabeledConcreteExecution
      AwkernelState
      awk_handoff_projection
      1
      awk_handoff_trace
      True
      awk_handoff_stepwise
      awk_handoff_struct_inv.

  Lemma awk_handoff_local_sound :
    @local_labeled_concrete_multicore_projection_sound
      AwkernelState
      awk_handoff_projection
      awk_handoff_jobs
      awk_single_cpu_admissibility
      1
      awk_handoff_execution.
  Proof.
    constructor.
    - constructor.
      + intros c j Hlt Hrun.
        simpl in Hrun.
        discriminate.
      + intros c j Hlt Hrun.
        simpl in Hrun.
        discriminate.
      + intros j Hin.
        simpl in Hin.
        destruct Hin as [Hj | []].
        subst j.
        unfold released, awk_handoff_jobs, awk_handoff_job.
        simpl.
        lia.
      + intros j Hin.
        simpl in Hin.
        destruct Hin as [Hj | []].
        subst j.
        apply not_completed_iff_service_lt_cost.
        unfold service_job, cpu_count, runs_on, project_schedule,
               osl_to_op_trace, os_to_op_state, osl_to_os_projection,
               awk_projection, os_to_op_trace, awk_to_op_state,
               awk_handoff_jobs, awk_handoff_job, awk_handoff_trace.
        simpl.
        lia.
      + intros [|[|[|[|t']]]] c j Hlt Hrun; simpl in *.
        * discriminate.
        * discriminate.
        * assert (c = 0) by lia.
          subst c.
          inversion Hrun; subst.
          right. left. reflexivity.
        * destruct (Nat.eqb c 0); discriminate.
        * destruct (Nat.eqb c 0); discriminate.
      + intros [|[|[|[|t']]]] c j Hlt Hdispatch; simpl in *.
        * discriminate.
        * discriminate.
        * inversion Hdispatch; subst.
          unfold released, awk_handoff_jobs, awk_handoff_job.
          simpl.
          lia.
        * discriminate.
        * discriminate.
      + intros t j Hwakeup.
        destruct t as [|[|[|[|t']]]]; simpl in Hwakeup; discriminate.
      + intros t j Hwakeup.
        destruct t as [|[|[|[|t']]]]; simpl in Hwakeup; discriminate.
      + intros [|[|[|[|t']]]] c j Hlt Hprev Hnext; simpl in *.
        * discriminate.
        * discriminate.
        * discriminate.
        * destruct (Nat.eqb c 0); discriminate.
        * destruct (Nat.eqb c 0); discriminate.
      + intros t c Hlt Hreq.
        destruct t as [|[|[|[|t']]]]; simpl in Hreq; discriminate.
      + intros [|[|[|[|t']]]] c Hlt Hhandle; simpl in *.
        * inversion Hhandle; subst. reflexivity.
        * discriminate.
        * discriminate.
        * discriminate.
        * discriminate.
      + intros [|[|[|[|t']]]] c j Hlt Hchoose; simpl in *.
        * discriminate.
        * inversion Hchoose; subst. reflexivity.
        * discriminate.
        * discriminate.
        * discriminate.
      + intros [|[|[|[|t']]]] c j Hlt Hchoose; simpl in *.
        * discriminate.
        * inversion Hchoose; subst. left. reflexivity.
        * discriminate.
        * discriminate.
        * discriminate.
      + intros [|[|[|[|t']]]] c j Hlt Hdispatch; simpl in *.
        * discriminate.
        * discriminate.
        * inversion Hdispatch; subst.
          apply not_completed_iff_service_lt_cost.
          unfold service_job, cpu_count, runs_on, project_schedule,
                 osl_to_op_trace, os_to_op_state, osl_to_os_projection,
                 awk_projection, os_to_op_trace, awk_to_op_state,
                 awk_handoff_jobs, awk_handoff_job, awk_handoff_trace.
          simpl.
          lia.
        * discriminate.
        * discriminate.
      + intros [|[|[|[|t']]]] c j Hblock Hcur; simpl in *.
        * discriminate.
        * discriminate.
        * discriminate.
        * inversion Hblock; subst.
          destruct (Nat.eqb c 0); discriminate.
        * discriminate.
      + intros [|[|[|[|t']]]] j Hblock; simpl in *.
        * discriminate.
        * discriminate.
        * discriminate.
        * inversion Hblock; subst.
          simpl.
          exact (remove_job_not_in 0 []).
        * discriminate.
      + intros [|[|[|[|t']]]] c j Hlt Hblock Htarget; simpl in *.
        * discriminate.
        * discriminate.
        * discriminate.
        * inversion Hblock; subst.
          destruct (Nat.eqb c 0); discriminate.
        * discriminate.
      + intros t j Hcomplete.
        destruct t as [|[|[|[|t']]]]; simpl in Hcomplete; discriminate.
      + intros t c old new Hlt Hpreempt.
        destruct t as [|[|[|[|t']]]]; simpl in Hpreempt; discriminate.
      + intros t c old new Hlt Hpreempt.
        destruct t as [|[|[|[|t']]]]; simpl in Hpreempt; discriminate.
      + intros t c old new Hlt Hpreempt.
        destruct t as [|[|[|[|t']]]]; simpl in Hpreempt; discriminate.
    - intros [|[|[|[|t']]]] c Hge; simpl.
      + destruct (Nat.eqb c 0) eqn:Ec.
        * apply Nat.eqb_eq in Ec. lia.
        * reflexivity.
      + destruct (Nat.eqb c 0) eqn:Ec.
        * apply Nat.eqb_eq in Ec. lia.
        * reflexivity.
      + destruct (Nat.eqb c 0) eqn:Ec.
        * apply Nat.eqb_eq in Ec. lia.
        * reflexivity.
      + destruct (Nat.eqb c 0) eqn:Ec.
        * apply Nat.eqb_eq in Ec. lia.
        * reflexivity.
      + destruct (Nat.eqb c 0) eqn:Ec.
        * apply Nat.eqb_eq in Ec. lia.
        * reflexivity.
    - intros [|[|[|[|t']]]] c j Hlt Hrun; simpl in *.
      + discriminate.
      + discriminate.
      + discriminate.
      + assert (c = 0) by lia.
        subst c.
        inversion Hrun; subst.
        unfold awk_single_cpu_admissibility.
        reflexivity.
      + destruct (Nat.eqb c 0); discriminate.
  Qed.

  Definition awk_handoff_local_contract :
    @os_local_multicore_adapter_contract
      AwkernelState
      awk_handoff_projection
      awk_handoff_jobs
      awk_single_cpu_admissibility
      1 :=
    @mkOSLocalMulticoreAdapterContract
      AwkernelState
      awk_handoff_projection
      awk_handoff_jobs
      awk_single_cpu_admissibility
      1
      awk_handoff_execution
      awk_handoff_local_sound.

  Example awk_handoff_local_contract_valid_schedule :
    valid_schedule
      awk_handoff_jobs
      1
      (project_schedule
         (lex_trace
            (concrete_to_labeled_execution
               (olac_execution awk_handoff_local_contract)))).
  Proof.
    apply awk_local_adapter_contract_implies_valid_schedule.
  Qed.

  Example awk_handoff_handle_sets_need_resched :
    op_need_resched
      (os_to_op_state
         (osl_to_os_projection awk_handoff_projection)
         (lce_trace (olac_execution awk_handoff_local_contract) 1))
      0 = true.
  Proof.
    eapply awk_local_adapter_contract_handle_sets_need_resched.
    - lia.
    - reflexivity.
  Qed.

  Example awk_handoff_choose_sets_dispatch_target :
    op_dispatch_target
      (os_to_op_state
         (osl_to_os_projection awk_handoff_projection)
         (lce_trace (olac_execution awk_handoff_local_contract) 2))
      0 = Some 0.
  Proof.
    eapply awk_local_adapter_contract_choose_sets_dispatch_target.
    - lia.
    - reflexivity.
  Qed.

  Example awk_handoff_dispatch_clears_need_resched :
    op_need_resched
      (os_to_op_state
         (osl_to_os_projection awk_handoff_projection)
         (lce_trace (olac_execution awk_handoff_local_contract) 3))
      0 = false.
  Proof.
    eapply awk_local_adapter_contract_dispatch_clears_need_resched.
    - lia.
    - reflexivity.
  Qed.

  Example awk_handoff_block_clears_dispatch_target :
    op_dispatch_target
      (os_to_op_state
         (osl_to_os_projection awk_handoff_projection)
         (lce_trace (olac_execution awk_handoff_local_contract) 4))
      0 = None.
  Proof.
    reflexivity.
  Qed.

End OperationalMulticoreProjectionExamples.
