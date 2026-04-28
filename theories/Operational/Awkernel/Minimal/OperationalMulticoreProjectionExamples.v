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
From RocqSched Require Import Operational.Awkernel.Minimal.MinimalProjection.
Import ListNotations.

(** Worked 2-CPU projection examples built on top of the reusable Awkernel
    minimal projection boundary. *)
Section OperationalMulticoreProjectionExamples.

  Definition mc_job0 : Job := mkJob 0 0 0 3 5 (fun _ => false).
  Definition mc_job1 : Job := mkJob 1 0 0 2 4 (fun _ => false).

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
    - intros [|t'] c j Hlt Hrun.
      + assert (Hcpu : c = 0 \/ c = 1) by lia.
        destruct Hcpu as [-> | ->]; simpl in Hrun; inversion Hrun; subst;
          unfold blocked, mc_jobs, mc_job0, mc_job1; simpl; discriminate.
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
      + intros t c j Hlt Hrun.
        unfold awk_trace, awk_state, blocked in Hrun |- *.
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

End OperationalMulticoreProjectionExamples.
