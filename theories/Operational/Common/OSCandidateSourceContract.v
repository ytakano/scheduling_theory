From Stdlib Require Import List.
Import ListNotations.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Multicore.Common.MultiCoreBase.
From RocqSched Require Import Multicore.Common.Admissibility.
From RocqSched Require Import Operational.Common.State.
From RocqSched Require Import Operational.Common.OSProjectionInterface.
From RocqSched Require Import Operational.Common.ConcreteExecution.
From RocqSched Require Import Operational.Common.Projection.
From RocqSched Require Import Operational.Common.OSLocalAdapterContract.
From RocqSched Require Import Operational.Common.OSSchedulerViewContract.

Definition projected_candidate_list
    {CState : Type}
    {P : OSLabeledProjection CState}
    (jobs : JobId -> Job)
    (m : nat)
    (ex : labeled_concrete_execution P m)
    (candidates_of : CandidateSource)
    (t : Time) : list JobId :=
  candidates_of
    jobs
    m
    (project_schedule (osl_to_op_trace P (lce_trace ex)))
    t.

Record labeled_concrete_candidate_source_contract
    {CState : Type}
    {P : OSLabeledProjection CState}
    (jobs : JobId -> Job)
    (m : nat)
    (candidates_of : CandidateSource)
    (ex : labeled_concrete_execution P m) : Prop :=
  mkLabeledConcreteCandidateSourceContract {
    lccsc_candidates_visible :
      forall t j,
        In j (projected_candidate_list jobs m ex candidates_of t) ->
        op_job_visible
          m
          (os_to_op_state (osl_to_os_projection P) (lce_trace ex t))
          j;
    lccsc_current_in_candidates :
      forall t c j,
        c < m ->
        op_current
          (os_to_op_state (osl_to_os_projection P) (lce_trace ex t))
          c = Some j ->
        In j (projected_candidate_list jobs m ex candidates_of t);
    lccsc_runnable_in_candidates :
      forall t j,
        In j
           (op_runnable
              (os_to_op_state (osl_to_os_projection P) (lce_trace ex t))) ->
        In j (projected_candidate_list jobs m ex candidates_of t);
    lccsc_dispatch_target_in_candidates :
      forall t c j,
        c < m ->
        op_dispatch_target
          (os_to_op_state (osl_to_os_projection P) (lce_trace ex t))
          c = Some j ->
        In j (projected_candidate_list jobs m ex candidates_of t);
    lccsc_prefix_extensional :
      forall s1 s2 t,
        (forall t' c, t' < t -> s1 t' c = s2 t' c) ->
        candidates_of jobs m s1 t = candidates_of jobs m s2 t;
  }.

Arguments lccsc_candidates_visible
  {CState P jobs m candidates_of ex} _ _ _ _.
Arguments lccsc_current_in_candidates
  {CState P jobs m candidates_of ex} _ _ _ _ _.
Arguments lccsc_runnable_in_candidates
  {CState P jobs m candidates_of ex} _ _ _ _.
Arguments lccsc_dispatch_target_in_candidates
  {CState P jobs m candidates_of ex} _ _ _ _ _.
Arguments lccsc_prefix_extensional
  {CState P jobs m candidates_of ex} _ _ _ _ _.

Record os_local_candidate_source_adapter_contract
    {CState : Type}
    (P : OSLabeledProjection CState)
    (candidates_of : CandidateSource)
    (jobs : JobId -> Job)
    (adm : admissible_cpu)
    (m : nat) : Type :=
  mkOSLocalCandidateSourceAdapterContract {
    olcsac_base : os_local_multicore_adapter_contract P jobs adm m;
    olcsac_candidates :
      labeled_concrete_candidate_source_contract
        jobs
        m
        candidates_of
        (olac_execution olcsac_base);
  }.

Arguments olcsac_base {CState P candidates_of jobs adm m} _.
Arguments olcsac_candidates {CState P candidates_of jobs adm m} _.
