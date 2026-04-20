From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.TopMInterface.
From RocqSched Require Import Multicore.Common.MultiCoreBase.
From RocqSched Require Import Multicore.Common.Admissibility.
From RocqSched Require Import Multicore.Common.AdmissibleCandidateSource.
From RocqSched Require Import Operational.Common.OSProjectionInterface.
From RocqSched Require Import Operational.Common.OSSchedulerRelationContract.

Record os_single_cpu_algorithm_adapter_contract
    {CState : Type}
    (P : OSLabeledProjection CState)
    (J : JobId -> Prop)
    (spec : GenericSchedulingAlgorithm)
    (candidates_of : CandidateSource)
    (jobs : JobId -> Job)
    (adm : admissible_cpu) : Type :=
  mkOSSingleCPUAlgorithmAdapterContract {
    osaac_scheduler_relation :
      os_local_single_cpu_scheduler_relation_adapter_contract
        P
        spec
        candidates_of
        jobs
        adm;
    osaac_candidate_source_spec :
      CandidateSourceSpec J candidates_of;
  }.

Arguments osaac_scheduler_relation
  {CState P J spec candidates_of jobs adm} _.
Arguments osaac_candidate_source_spec
  {CState P J spec candidates_of jobs adm} _.

Record os_top_m_algorithm_adapter_contract
    {CState : Type}
    (P : OSLabeledProjection CState)
    (J : JobId -> Prop)
    (spec : GenericTopMSchedulingAlgorithm)
    (candidates_of : CandidateSource)
    (jobs : JobId -> Job)
    (adm : admissible_cpu)
    (m : nat) : Type :=
  mkOSTopMAlgorithmAdapterContract {
    otmaac_scheduler_relation :
      os_local_top_m_scheduler_relation_adapter_contract
        P
        spec
        candidates_of
        jobs
        adm
        m;
    otmaac_candidate_source_spec :
      AdmissibleCandidateSourceSpec adm J candidates_of;
  }.

Arguments otmaac_scheduler_relation
  {CState P J spec candidates_of jobs adm m} _.
Arguments otmaac_candidate_source_spec
  {CState P J spec candidates_of jobs adm m} _.

Record os_strong_top_m_algorithm_adapter_contract
    {CState : Type}
    (P : OSLabeledProjection CState)
    (J : JobId -> Prop)
    (spec : GenericTopMSchedulingAlgorithm)
    (candidates_of : CandidateSource)
    (jobs : JobId -> Job)
    (adm : admissible_cpu)
    (m : nat) : Type :=
  mkOSStrongTopMAlgorithmAdapterContract {
    ostmaac_base :
      os_top_m_algorithm_adapter_contract
        P
        J
        spec
        candidates_of
        jobs
        adm
        m;
    ostmaac_candidate_source_spec :
      StrongAdmissibleCandidateSourceSpec adm J candidates_of;
  }.

Arguments ostmaac_base
  {CState P J spec candidates_of jobs adm m} _.
Arguments ostmaac_candidate_source_spec
  {CState P J spec candidates_of jobs adm m} _.
