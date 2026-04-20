From Stdlib Require Import List.
Import ListNotations.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Multicore.Common.MultiCoreBase.
From RocqSched Require Import Multicore.Common.Admissibility.
From RocqSched Require Import Operational.Common.OSProjectionInterface.
From RocqSched Require Import Operational.Common.ConcreteExecution.
From RocqSched Require Import Operational.Common.Projection.
From RocqSched Require Import Operational.Common.OSCandidateSourceContract.
From RocqSched Require Import Operational.Common.OSLocalAdapterContract.

Record labeled_concrete_admissible_candidate_source_contract
    {CState : Type}
    {P : OSLabeledProjection CState}
    (J : JobId -> Prop)
    (jobs : JobId -> Job)
    (adm : admissible_cpu)
    (m : nat)
    (candidates_of : CandidateSource)
    (ex : labeled_concrete_execution P m) : Prop :=
  mkLabeledConcreteAdmissibleCandidateSourceContract {
    lcacsc_base :
      labeled_concrete_candidate_source_contract
        jobs
        m
        candidates_of
        ex;
    lcacsc_candidates_sound :
      forall t j,
        In j (projected_candidate_list jobs m ex candidates_of t) ->
        J j;
    lcacsc_candidates_complete :
      forall t j,
        J j ->
        eligible
          jobs
          m
          (project_schedule (osl_to_op_trace P (lce_trace ex)))
          j
          t ->
        admissible_somewhere
          adm
          jobs
          m
          (project_schedule (osl_to_op_trace P (lce_trace ex)))
          j
          t ->
        In j (projected_candidate_list jobs m ex candidates_of t);
  }.

Arguments lcacsc_base
  {CState P J jobs adm m candidates_of ex} _.
Arguments lcacsc_candidates_sound
  {CState P J jobs adm m candidates_of ex} _ _ _ _.
Arguments lcacsc_candidates_complete
  {CState P J jobs adm m candidates_of ex} _ _ _ _ _ _.

Record labeled_concrete_strong_admissible_candidate_source_contract
    {CState : Type}
    {P : OSLabeledProjection CState}
    (J : JobId -> Prop)
    (jobs : JobId -> Job)
    (adm : admissible_cpu)
    (m : nat)
    (candidates_of : CandidateSource)
    (ex : labeled_concrete_execution P m) : Prop :=
  mkLabeledConcreteStrongAdmissibleCandidateSourceContract {
    lcsacsc_base :
      labeled_concrete_admissible_candidate_source_contract
        J
        jobs
        adm
        m
        candidates_of
        ex;
    lcsacsc_candidates_somewhere :
      forall t j,
        In j (projected_candidate_list jobs m ex candidates_of t) ->
        admissible_somewhere
          adm
          jobs
          m
          (project_schedule (osl_to_op_trace P (lce_trace ex)))
          j
          t;
  }.

Arguments lcsacsc_base
  {CState P J jobs adm m candidates_of ex} _.
Arguments lcsacsc_candidates_somewhere
  {CState P J jobs adm m candidates_of ex} _ _ _ _.

Record os_local_admissible_candidate_source_adapter_contract
    {CState : Type}
    (P : OSLabeledProjection CState)
    (J : JobId -> Prop)
    (candidates_of : CandidateSource)
    (jobs : JobId -> Job)
    (adm : admissible_cpu)
    (m : nat) : Type :=
  mkOSLocalAdmissibleCandidateSourceAdapterContract {
    olacsc_base :
      os_local_candidate_source_adapter_contract
        P
        candidates_of
        jobs
        adm
        m;
    olacsc_admissible :
      labeled_concrete_admissible_candidate_source_contract
        J
        jobs
        adm
        m
        candidates_of
        (olac_execution (olcsac_base olacsc_base));
  }.

Arguments olacsc_base
  {CState P J candidates_of jobs adm m} _.
Arguments olacsc_admissible
  {CState P J candidates_of jobs adm m} _.

Record os_local_strong_admissible_candidate_source_adapter_contract
    {CState : Type}
    (P : OSLabeledProjection CState)
    (J : JobId -> Prop)
    (candidates_of : CandidateSource)
    (jobs : JobId -> Job)
    (adm : admissible_cpu)
    (m : nat) : Type :=
  mkOSLocalStrongAdmissibleCandidateSourceAdapterContract {
    olsacsc_base :
      os_local_admissible_candidate_source_adapter_contract
        P
        J
        candidates_of
        jobs
        adm
        m;
    olsacsc_strong :
      labeled_concrete_strong_admissible_candidate_source_contract
        J
        jobs
        adm
        m
        candidates_of
        (olac_execution (olcsac_base (olacsc_base olsacsc_base)));
  }.

Arguments olsacsc_base
  {CState P J candidates_of jobs adm m} _.
Arguments olsacsc_strong
  {CState P J candidates_of jobs adm m} _.
