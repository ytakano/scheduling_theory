From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Multicore.Common.Admissibility.
From RocqSched Require Import Multicore.Common.ValidityFacts.
From RocqSched Require Import Operational.Common.State.
From RocqSched Require Import Operational.Common.Trace.
From RocqSched Require Import Operational.Common.Step.
From RocqSched Require Import Operational.Common.Invariants.
From RocqSched Require Import Operational.Common.Execution.
From RocqSched Require Import Operational.Common.Projection.
From RocqSched Require Import Operational.Common.ProjectionLemmas.
From RocqSched Require Import Operational.Common.LabeledExecution.
From RocqSched Require Import Operational.Common.DelayModel.
From RocqSched Require Import Operational.Common.DelayBudget.
From RocqSched Require Import Operational.Common.ProjectionMulticoreValidity.
From RocqSched Require Import Refinement.BoundedDelayRefinement.
Import ListNotations.

Section OperationalDelayExamples.

  Definition delay_example_job : Job := mkJob 0 0 0 1 3.
  Definition delay_example_jobs (_ : JobId) : Job := delay_example_job.

  Definition idle_state : OpState :=
    mkOpState (fun _ => None) [] (fun _ => false) (fun _ => None).

  Definition idle_trace (_ : Time) : OpState := idle_state.

  Lemma idle_state_struct_inv :
    forall t, op_struct_inv 1 (idle_trace t).
  Proof.
    intros t.
    constructor.
    - intros j c1 c2 Hlt1 Hlt2 Hrun1 _.
      simpl in Hrun1.
      discriminate.
    - constructor.
    - intros c j Hcur Hin.
      simpl in Hcur.
      discriminate.
    - intros j c1 c2 Hlt1 Hlt2 Ht1 _.
      simpl in Ht1.
      discriminate.
    - intros c j Hlt Ht.
      simpl in Ht.
      discriminate.
  Qed.

  Definition idle_labeled_execution : labeled_execution 1 :=
    mkLabeledExecution
      1
      idle_trace
      (fun _ => EvTick)
      True
      (fun _ => step_tick _)
      idle_state_struct_inv.

  Definition idle_actual_schedule : Schedule :=
    labeled_actual_schedule idle_labeled_execution.

  Definition idle_delay_sources : DelayTrace :=
    fun t => default_event_delay_sources (lex_event idle_labeled_execution t).

  Lemma idle_labeled_execution_sound :
    execution_projection_sound
      delay_example_jobs
      1
      (labeled_to_execution idle_labeled_execution).
  Proof.
    constructor.
    - intros t c j Hlt Hrun.
      unfold idle_trace, idle_state in Hrun.
      simpl in Hrun.
      discriminate.
    - intros t c j Hlt Hrun.
      unfold idle_trace, idle_state in Hrun.
      simpl in Hrun.
      discriminate.
  Qed.

  Example labeled_execution_yields_valid_schedule :
    valid_schedule
      delay_example_jobs
      1
      idle_actual_schedule.
  Proof.
    unfold idle_actual_schedule.
    change
      (valid_schedule
         delay_example_jobs
         1
         (project_schedule (ex_trace (labeled_to_execution idle_labeled_execution)))).
    eapply execution_projection_sound_implies_valid_schedule.
    exact idle_labeled_execution_sound.
  Qed.

  Example labeled_execution_default_delay_source :
    default_event_delay_sources (lex_event idle_labeled_execution 0) =
    [DelayTimer].
  Proof.
    reflexivity.
  Qed.

  Definition timer_heavy_bounds : op_delay_bounds :=
    mkOpDelayBounds 0 0 2 0 0 0.

  Example cumulative_timer_budget_example :
    cumulative_delay_budget timer_heavy_bounds (fun _ => [DelayTimer]) 3 = 6.
  Proof.
    reflexivity.
  Qed.

  Example cumulative_timer_delay_example :
    cumulative_delay timer_heavy_bounds (fun _ => [DelayTimer]) 1 4 = 6.
  Proof.
    reflexivity.
  Qed.

  Example service_lag_same_schedule :
    service_lag_le
      1
      (project_schedule idle_trace)
      (project_schedule idle_trace)
      0.
  Proof.
    apply service_lag_le_refl.
  Qed.

  Definition zero_delay_bounds : op_delay_bounds :=
    mkOpDelayBounds 0 0 0 0 0 0.

  Lemma cumulative_zero_delay_budget :
    forall t,
      cumulative_delay_budget
        zero_delay_bounds
        idle_delay_sources
        t <= 0.
  Proof.
    induction t as [|t IH].
    - simpl. lia.
    - unfold idle_delay_sources.
      simpl.
      replace (step_delay_budget zero_delay_bounds [DelayTimer]) with 0 by reflexivity.
      rewrite Nat.add_0_r.
      exact IH.
  Qed.

  Lemma idle_zero_budget_within_delta :
    forall t,
      delay_budget_le zero_delay_bounds idle_delay_sources 0 t 0.
  Proof.
    intros t.
    unfold delay_budget_le, cumulative_delay, delay_budget_between.
    simpl.
    rewrite Nat.sub_0_r.
    pose proof (cumulative_zero_delay_budget t) as Hbudget.
    exact Hbudget.
  Qed.

  Lemma idle_default_delay_sources_covered :
    forall t src,
      In src (default_event_delay_sources (lex_event idle_labeled_execution t)) ->
      In src (idle_delay_sources t).
  Proof.
    intros t src Hin.
    exact Hin.
  Qed.

  Lemma idle_service_lag_zero :
    service_lag_le
      1
      (project_schedule idle_trace)
      idle_actual_schedule
      0.
  Proof.
    unfold idle_actual_schedule.
    apply service_lag_le_refl.
  Qed.

  Lemma idle_multicore_projection_sound :
    execution_multicore_projection_sound
      delay_example_jobs
      all_cpus_admissible
      1
      (labeled_to_execution idle_labeled_execution).
  Proof.
    constructor.
    - exact idle_labeled_execution_sound.
    - intros t c Hge.
      unfold idle_trace, idle_state.
      simpl.
      reflexivity.
    - intros t c j Hlt Hrun.
      unfold idle_trace, idle_state in Hrun.
      simpl in Hrun.
      discriminate.
  Qed.

  Lemma idle_actual_semantic_validity :
    multicore_semantic_validity
      delay_example_jobs
      1
      idle_actual_schedule.
  Proof.
    unfold idle_actual_schedule.
    change
      (multicore_semantic_validity
         delay_example_jobs
         1
         (project_schedule (ex_trace (labeled_to_execution idle_labeled_execution)))).
    apply execution_multicore_projection_sound_implies_semantic_validity
      with (adm := all_cpus_admissible).
    exact idle_multicore_projection_sound.
  Qed.

  Definition idle_delay_refinement : bounded_delay_refinement 1 :=
    mkBoundedDelayRefinement
      1
      idle_labeled_execution
      (project_schedule idle_trace)
      zero_delay_bounds
      idle_delay_sources
      0
      idle_default_delay_sources_covered
      idle_zero_budget_within_delta
      idle_service_lag_zero.

  Example idle_delay_refinement_has_zero_lag :
    service_lag_le
      1
      (bdr_ideal_schedule idle_delay_refinement)
      (labeled_actual_schedule (bdr_execution idle_delay_refinement))
      (bdr_delta idle_delay_refinement).
  Proof.
    apply bounded_delay_refinement_service_lag.
  Qed.

  Definition idle_projection_refinement :
    bounded_delay_projection_refinement
      delay_example_jobs
      all_cpus_admissible
      1
      idle_labeled_execution
      idle_actual_schedule
      zero_delay_bounds
      idle_delay_sources
      0.
  Proof.
    refine
      (mkBoundedDelayProjectionRefinement
         delay_example_jobs
         all_cpus_admissible
         1
         idle_labeled_execution
         idle_actual_schedule
         zero_delay_bounds
         idle_delay_sources
         0
         idle_multicore_projection_sound
         idle_actual_semantic_validity
         idle_default_delay_sources_covered
         idle_zero_budget_within_delta
         idle_service_lag_zero).
  Defined.

  Example idle_projection_refinement_actual_valid :
    multicore_semantic_validity
      delay_example_jobs
      1
      idle_actual_schedule.
  Proof.
    eapply bounded_delay_projection_refinement_actual_semantic_validity.
    exact idle_projection_refinement.
  Qed.

  Example service_lag_monotone_idle_example :
    service_lag_le
      1
      (project_schedule idle_trace)
      idle_actual_schedule
      2.
  Proof.
    eapply service_lag_monotone_delta.
    - exact idle_service_lag_zero.
    - lia.
  Qed.

  Example cumulative_delay_split_idle_example :
    cumulative_delay zero_delay_bounds idle_delay_sources 0 3 =
    cumulative_delay zero_delay_bounds idle_delay_sources 0 1 +
    cumulative_delay zero_delay_bounds idle_delay_sources 1 3.
  Proof.
    apply cumulative_delay_split; lia.
  Qed.

End OperationalDelayExamples.
