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
From RocqSched Require Import Operational.Common.OSAdmissibleCandidateSourceContract.
From RocqSched Require Import Operational.Common.OSLocalAdapterContract.

Lemma os_local_admissible_candidate_source_adapter_contract_candidate_in_subset :
  forall CState (P : OSLabeledProjection CState)
         J candidates_of jobs adm m
         (C : os_local_admissible_candidate_source_adapter_contract
                P J candidates_of jobs adm m) t j,
    In j
       (projected_candidate_list
          jobs
          m
          (olac_execution (olcsac_base (olacsc_base C)))
          candidates_of
          t) ->
    J j.
Proof.
  intros CState P J candidates_of jobs adm m C t j Hin.
  exact (lcacsc_candidates_sound (olacsc_admissible C) t j Hin).
Qed.

Lemma os_local_admissible_candidate_source_adapter_contract_admissible_complete :
  forall CState (P : OSLabeledProjection CState)
         J candidates_of jobs adm m
         (C : os_local_admissible_candidate_source_adapter_contract
                P J candidates_of jobs adm m) t j,
    J j ->
    eligible
      jobs
      m
      (project_schedule
         (osl_to_op_trace P
            (lce_trace (olac_execution (olcsac_base (olacsc_base C))))))
      j
      t ->
    admissible_somewhere
      adm
      jobs
      m
      (project_schedule
         (osl_to_op_trace P
            (lce_trace (olac_execution (olcsac_base (olacsc_base C))))))
      j
      t ->
    In j
       (projected_candidate_list
          jobs
          m
          (olac_execution (olcsac_base (olacsc_base C)))
          candidates_of
          t).
Proof.
  intros CState P J candidates_of jobs adm m C t j HJ Helig Hadm.
  exact (lcacsc_candidates_complete (olacsc_admissible C) t j HJ Helig Hadm).
Qed.

Lemma os_local_strong_admissible_candidate_source_adapter_contract_candidate_somewhere :
  forall CState (P : OSLabeledProjection CState)
         J candidates_of jobs adm m
         (C : os_local_strong_admissible_candidate_source_adapter_contract
                P J candidates_of jobs adm m) t j,
    In j
       (projected_candidate_list
          jobs
          m
          (olac_execution (olcsac_base (olacsc_base (olsacsc_base C))))
          candidates_of
          t) ->
    admissible_somewhere
      adm
      jobs
      m
      (project_schedule
         (osl_to_op_trace P
            (lce_trace (olac_execution (olcsac_base (olacsc_base (olsacsc_base C)))))))
      j
      t.
Proof.
  intros CState P J candidates_of jobs adm m C t j Hin.
  exact (lcsacsc_candidates_somewhere (olsacsc_strong C) t j Hin).
Qed.

Lemma os_local_strong_admissible_candidate_source_adapter_contract_candidate_in_subset :
  forall CState (P : OSLabeledProjection CState)
         J candidates_of jobs adm m
         (C : os_local_strong_admissible_candidate_source_adapter_contract
                P J candidates_of jobs adm m) t j,
    In j
       (projected_candidate_list
          jobs
          m
          (olac_execution (olcsac_base (olacsc_base (olsacsc_base C))))
          candidates_of
          t) ->
    J j.
Proof.
  intros CState P J candidates_of jobs adm m C t j Hin.
  exact (lcacsc_candidates_sound
           (olacsc_admissible (olsacsc_base C))
           t
           j
           Hin).
Qed.
