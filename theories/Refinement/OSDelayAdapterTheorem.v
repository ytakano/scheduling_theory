From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.Scheduler.Validity.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.TopMInterface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.TopMSchedulerBridge.
From RocqSched Require Import Multicore.Common.Admissibility.
From RocqSched Require Import Multicore.Common.ValidityFacts.
From RocqSched Require Import Operational.Common.OSProjectionInterface.
From RocqSched Require Import Operational.Common.ConcreteExecution.
From RocqSched Require Import Operational.Common.Projection.
From RocqSched Require Import Operational.Common.OSAdapterContract.
From RocqSched Require Import Operational.Common.OSDelayAdapterContract.
From RocqSched Require Import Refinement.BoundedDelayRefinement.
From RocqSched Require Import Refinement.OSAlgorithmAdapterTheorem.
From RocqSched Require Import Refinement.OSRefinementTheorem.

Lemma os_delay_adapter_contract_implies_bounded_delay_refinement :
  forall CState (P : OSLabeledProjection CState) jobs adm m
         (C : os_delay_adapter_contract P jobs adm m),
    let ex := @oac_execution CState P jobs adm m (odac_base C) in
    bounded_delay_projection_refinement
      jobs
      adm
      m
      (concrete_to_labeled_execution ex)
      (odac_ideal_schedule C)
      (odac_delay_bounds C)
      (odac_delay_sources C)
      (odac_delta C).
Proof.
  intros CState P jobs adm m C.
  destruct C as [base ideal bounds sources delta Hvalid Hcovered Hbudget Hlag].
  destruct base as [ex Hsound].
  apply mk_bounded_delay_projection_refinement.
  - apply labeled_concrete_multicore_projection_sound_to_labeled_execution.
    exact Hsound.
  - exact Hvalid.
  - exact Hcovered.
  - exact Hbudget.
  - exact Hlag.
Qed.

Lemma os_delay_adapter_contract_implies_actual_semantic_validity :
  forall CState (P : OSLabeledProjection CState) jobs adm m
         (C : os_delay_adapter_contract P jobs adm m),
    multicore_semantic_validity
      jobs
      m
      (labeled_actual_schedule
         (concrete_to_labeled_execution (oac_execution (odac_base C)))).
Proof.
  intros CState P jobs adm m C.
  eapply bounded_delay_projection_refinement_actual_semantic_validity.
  apply os_delay_adapter_contract_implies_bounded_delay_refinement.
Qed.

Lemma os_delay_adapter_contract_implies_actual_valid_schedule :
  forall CState (P : OSLabeledProjection CState) jobs adm m
         (C : os_delay_adapter_contract P jobs adm m),
    valid_schedule
      jobs
      m
      (labeled_actual_schedule
         (concrete_to_labeled_execution (oac_execution (odac_base C)))).
Proof.
  intros CState P jobs adm m C.
  apply os_multicore_adapter_contract_implies_valid_schedule.
Qed.

Lemma os_delay_top_m_adapter_contract_implies_actual_valid_schedule :
  forall CState (P : OSLabeledProjection CState)
         J spec candidates_of jobs adm m
         (C : os_delay_top_m_adapter_contract P J spec candidates_of jobs adm m),
    valid_schedule
      jobs
      m
      (labeled_actual_schedule
         (concrete_to_labeled_execution
            (projected_top_m_algorithm_execution (odtac_base C)))).
Proof.
  intros CState P J spec candidates_of jobs adm m C.
  apply os_top_m_algorithm_adapter_contract_implies_valid_schedule
    with (C := odtac_base C).
Qed.

Lemma os_delay_adapter_contract_implies_ideal_semantic_validity :
  forall CState (P : OSLabeledProjection CState) jobs adm m
         (C : os_delay_adapter_contract P jobs adm m),
    multicore_semantic_validity
      jobs
      m
      (odac_ideal_schedule C).
Proof.
  intros CState P jobs adm m C.
  eapply bounded_delay_projection_refinement_ideal_semantic_validity.
  apply os_delay_adapter_contract_implies_bounded_delay_refinement.
Qed.

Lemma os_delay_adapter_contract_implies_service_lag :
  forall CState (P : OSLabeledProjection CState) jobs adm m
         (C : os_delay_adapter_contract P jobs adm m),
    service_lag_le
      m
      (odac_ideal_schedule C)
      (labeled_actual_schedule
         (concrete_to_labeled_execution (oac_execution (odac_base C))))
      (odac_delta C).
Proof.
  intros CState P jobs adm m C.
  eapply bounded_delay_projection_refinement_service_lag.
  apply os_delay_adapter_contract_implies_bounded_delay_refinement.
Qed.

Lemma os_delay_top_m_adapter_contract_implies_bounded_delay_top_m_refinement :
  forall CState (P : OSLabeledProjection CState)
         J spec candidates_of jobs adm m
         (C : os_delay_top_m_adapter_contract P J spec candidates_of jobs adm m),
    let ex :=
      @projected_top_m_algorithm_execution
        CState P J spec candidates_of jobs adm m
        (odtac_base C) in
    bounded_delay_top_m_projection_refinement
      spec
      candidates_of
      jobs
      adm
      m
      (concrete_to_labeled_execution ex)
      (odtac_ideal_schedule C)
      (odtac_delay_bounds C)
      (odtac_delay_sources C)
      (odtac_delta C).
Proof.
  intros CState P J spec candidates_of jobs adm m C.
  destruct C as [base ideal bounds sources delta Htopm Hcovered Hbudget Hlag].
  destruct base as [schedrel Hcand].
  destruct schedrel as [cand_adapter Hrel].
  destruct cand_adapter as [base_sound Hcand_contract].
  destruct base_sound as [ex Hsound].
  apply mk_bounded_delay_top_m_projection_refinement.
  - apply labeled_concrete_multicore_projection_sound_to_labeled_execution.
    apply local_labeled_concrete_multicore_projection_sound_to_global.
    exact Hsound.
  - exact Htopm.
  - exact Hcovered.
  - exact Hbudget.
  - exact Hlag.
Qed.

Lemma os_delay_top_m_adapter_contract_implies_actual_semantic_validity :
  forall CState (P : OSLabeledProjection CState)
         J spec candidates_of jobs adm m
         (C : os_delay_top_m_adapter_contract P J spec candidates_of jobs adm m),
    multicore_semantic_validity
      jobs
      m
      (labeled_actual_schedule
         (concrete_to_labeled_execution
            (projected_top_m_algorithm_execution (odtac_base C)))).
Proof.
  intros CState P J spec candidates_of jobs adm m C.
  eapply bounded_delay_top_m_actual_semantic_validity.
  apply os_delay_top_m_adapter_contract_implies_bounded_delay_top_m_refinement.
Qed.

Lemma os_delay_top_m_adapter_contract_implies_ideal_top_m_scheduler_rel :
  forall CState (P : OSLabeledProjection CState)
         J spec candidates_of jobs adm m
         (C : os_delay_top_m_adapter_contract P J spec candidates_of jobs adm m),
    scheduler_rel
      (top_m_algorithm_schedule spec candidates_of)
      jobs
      m
      (odtac_ideal_schedule C).
Proof.
  intros CState P J spec candidates_of jobs adm m C.
  exact (odtac_ideal_top_m C).
Qed.
