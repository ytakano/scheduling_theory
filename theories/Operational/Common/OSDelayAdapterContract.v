From Stdlib Require Import List.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.TopMInterface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.TopMSchedulerBridge.
From RocqSched Require Import Multicore.Common.MultiCoreBase.
From RocqSched Require Import Multicore.Common.Admissibility.
From RocqSched Require Import Multicore.Common.ValidityFacts.
From RocqSched Require Import Operational.Common.DelayModel.
From RocqSched Require Import Operational.Common.DelayBudget.
From RocqSched Require Import Operational.Common.OSProjectionInterface.
From RocqSched Require Import Operational.Common.LabeledExecution.
From RocqSched Require Import Operational.Common.ConcreteExecution.
From RocqSched Require Import Operational.Common.OSLocalAdapterContract.
From RocqSched Require Import Operational.Common.OSAdapterContract.
From RocqSched Require Import Operational.Common.OSCandidateSourceContract.
From RocqSched Require Import Operational.Common.OSSchedulerRelationContract.
From RocqSched Require Import Operational.Common.OSAlgorithmAdapterContract.
From RocqSched Require Import Refinement.BoundedDelayRefinement.
Import ListNotations.

Record os_delay_adapter_contract
    {CState : Type}
    (P : OSLabeledProjection CState)
    (jobs : JobId -> Job)
    (adm : admissible_cpu)
    (m : nat) : Type :=
  mkOSDelayAdapterContract {
    odac_base : os_multicore_adapter_contract P jobs adm m;
    odac_ideal_schedule : Schedule;
    odac_delay_bounds : op_delay_bounds;
    odac_delay_sources : DelayTrace;
    odac_delta : nat;
    odac_ideal_valid :
      multicore_semantic_validity jobs m odac_ideal_schedule;
    odac_default_sources_covered :
      forall t src,
        In src
           (default_event_delay_sources
              (lex_event
                 (concrete_to_labeled_execution (oac_execution odac_base)) t)) ->
        In src (odac_delay_sources t);
    odac_budget_within_delta :
      forall t,
        delay_budget_le
          odac_delay_bounds
          odac_delay_sources
          0
          t
          odac_delta;
    odac_service_lag :
      service_lag_le
        m
        odac_ideal_schedule
        (labeled_actual_schedule
           (concrete_to_labeled_execution (oac_execution odac_base)))
        odac_delta;
  }.

Definition projected_top_m_algorithm_execution
    {CState : Type}
    {P : OSLabeledProjection CState}
    {J : JobId -> Prop}
    {spec : GenericTopMSchedulingAlgorithm}
    {candidates_of : CandidateSource}
    {jobs : JobId -> Job}
    {adm : admissible_cpu}
    {m : nat}
    (C : os_top_m_algorithm_adapter_contract
           P J spec candidates_of jobs adm m)
  : labeled_concrete_execution P m :=
  olac_execution
    (olcsac_base
       (oltsrac_base
          (otmaac_scheduler_relation C))).

Record os_delay_top_m_adapter_contract
    {CState : Type}
    (P : OSLabeledProjection CState)
    (J : JobId -> Prop)
    (spec : GenericTopMSchedulingAlgorithm)
    (candidates_of : CandidateSource)
    (jobs : JobId -> Job)
    (adm : admissible_cpu)
    (m : nat) : Type :=
  mkOSDelayTopMAdapterContract {
    odtac_base :
      os_top_m_algorithm_adapter_contract
        P
        J
        spec
        candidates_of
        jobs
        adm
        m;
    odtac_ideal_schedule : Schedule;
    odtac_delay_bounds : op_delay_bounds;
    odtac_delay_sources : DelayTrace;
    odtac_delta : nat;
    odtac_ideal_top_m :
      scheduler_rel
        (top_m_algorithm_schedule spec candidates_of)
        jobs m odtac_ideal_schedule;
    odtac_default_sources_covered :
      forall t src,
        In src
           (default_event_delay_sources
              (lex_event
                 (concrete_to_labeled_execution
                    (projected_top_m_algorithm_execution odtac_base))
                 t)) ->
        In src (odtac_delay_sources t);
    odtac_budget_within_delta :
      forall t,
        delay_budget_le
          odtac_delay_bounds
          odtac_delay_sources
          0
          t
          odtac_delta;
    odtac_service_lag :
      service_lag_le
        m
        odtac_ideal_schedule
        (labeled_actual_schedule
           (concrete_to_labeled_execution
              (projected_top_m_algorithm_execution odtac_base)))
        odtac_delta;
  }.

Arguments odac_base {CState P jobs adm m} _.
Arguments odac_ideal_schedule {CState P jobs adm m} _.
Arguments odac_delay_bounds {CState P jobs adm m} _.
Arguments odac_delay_sources {CState P jobs adm m} _ _.
Arguments odac_delta {CState P jobs adm m} _.
Arguments odac_ideal_valid {CState P jobs adm m} _.
Arguments odtac_base {CState P J spec candidates_of jobs adm m} _.
Arguments odtac_ideal_schedule {CState P J spec candidates_of jobs adm m} _.
Arguments odtac_delay_bounds {CState P J spec candidates_of jobs adm m} _.
Arguments odtac_delay_sources {CState P J spec candidates_of jobs adm m} _ _.
Arguments odtac_delta {CState P J spec candidates_of jobs adm m} _.
Arguments odtac_ideal_top_m {CState P J spec candidates_of jobs adm m} _.
