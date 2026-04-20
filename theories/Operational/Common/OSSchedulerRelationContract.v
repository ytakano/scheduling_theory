From Stdlib Require Import List Bool Arith.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.TopMInterface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.TopMSchedulerBridge.
From RocqSched Require Import Multicore.Common.MultiCoreBase.
From RocqSched Require Import Multicore.Common.Admissibility.
From RocqSched Require Import Operational.Common.OSProjectionInterface.
From RocqSched Require Import Operational.Common.ConcreteExecution.
From RocqSched Require Import Operational.Common.Projection.
From RocqSched Require Import Operational.Common.OSLocalAdapterContract.
From RocqSched Require Import Operational.Common.OSCandidateSourceContract.

Definition projected_scheduler_relation_schedule
    {CState : Type}
    {P : OSLabeledProjection CState}
    {m : nat}
    (ex : labeled_concrete_execution P m) : Schedule :=
  project_schedule (osl_to_op_trace P (lce_trace ex)).

Record labeled_concrete_single_cpu_scheduler_relation_contract
    {CState : Type}
    {P : OSLabeledProjection CState}
    (jobs : JobId -> Job)
    (spec : GenericSchedulingAlgorithm)
    (candidates_of : CandidateSource)
    (ex : labeled_concrete_execution P 1) : Prop :=
  mkLabeledConcreteSingleCPUSchedulerRelationContract {
    lcssrc_cpu0_follows_choose :
      forall t,
        projected_scheduler_relation_schedule ex t 0 =
        spec.(choose)
          jobs
          1
          (projected_scheduler_relation_schedule ex)
          t
          (projected_candidate_list jobs 1 ex candidates_of t);
    lcssrc_other_cpus_idle :
      forall t c, 0 < c ->
        projected_scheduler_relation_schedule ex t c = None;
  }.

Arguments lcssrc_cpu0_follows_choose
  {CState P jobs spec candidates_of ex} _ _.
Arguments lcssrc_other_cpus_idle
  {CState P jobs spec candidates_of ex} _ _ _ _.

Record labeled_concrete_top_m_scheduler_relation_contract
    {CState : Type}
    {P : OSLabeledProjection CState}
    (jobs : JobId -> Job)
    (m : nat)
    (spec : GenericTopMSchedulingAlgorithm)
    (candidates_of : CandidateSource)
    (ex : labeled_concrete_execution P m) : Prop :=
  mkLabeledConcreteTopMSchedulerRelationContract {
    lctmsrc_cpu_follows_choose_top_m :
      forall t c,
        projected_scheduler_relation_schedule ex t c =
        if c <? m then
          nth_error
            (choose_top_m
               spec
               jobs
               m
               (projected_scheduler_relation_schedule ex)
               t
               (projected_candidate_list jobs m ex candidates_of t))
            c
        else
          None;
  }.

Arguments lctmsrc_cpu_follows_choose_top_m
  {CState P jobs m spec candidates_of ex} _ _ _.

Record os_local_single_cpu_scheduler_relation_adapter_contract
    {CState : Type}
    (P : OSLabeledProjection CState)
    (spec : GenericSchedulingAlgorithm)
    (candidates_of : CandidateSource)
    (jobs : JobId -> Job)
    (adm : admissible_cpu) : Type :=
  mkOSLocalSingleCPUSchedulerRelationAdapterContract {
    olssrac_base :
      os_local_candidate_source_adapter_contract
        P
        candidates_of
        jobs
        adm
        1;
    olssrac_relation :
      labeled_concrete_single_cpu_scheduler_relation_contract
        jobs
        spec
        candidates_of
        (olac_execution (olcsac_base olssrac_base));
  }.

Arguments olssrac_base
  {CState P spec candidates_of jobs adm} _.
Arguments olssrac_relation
  {CState P spec candidates_of jobs adm} _.

Record os_local_top_m_scheduler_relation_adapter_contract
    {CState : Type}
    (P : OSLabeledProjection CState)
    (spec : GenericTopMSchedulingAlgorithm)
    (candidates_of : CandidateSource)
    (jobs : JobId -> Job)
    (adm : admissible_cpu)
    (m : nat) : Type :=
  mkOSLocalTopMSchedulerRelationAdapterContract {
    oltsrac_base :
      os_local_candidate_source_adapter_contract
        P
        candidates_of
        jobs
        adm
        m;
    oltsrac_relation :
      labeled_concrete_top_m_scheduler_relation_contract
        jobs
        m
        spec
        candidates_of
        (olac_execution (olcsac_base oltsrac_base));
  }.

Arguments oltsrac_base
  {CState P spec candidates_of jobs adm m} _.
Arguments oltsrac_relation
  {CState P spec candidates_of jobs adm m} _.
