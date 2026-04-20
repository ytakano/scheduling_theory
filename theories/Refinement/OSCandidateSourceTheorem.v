From Stdlib Require Import List.
Import ListNotations.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Semantics.ScheduleLemmas.ScheduleFacts.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Multicore.Common.MultiCoreBase.
From RocqSched Require Import Multicore.Common.Admissibility.
From RocqSched Require Import Operational.Common.State.
From RocqSched Require Import Operational.Common.Step.
From RocqSched Require Import Operational.Common.OSProjectionInterface.
From RocqSched Require Import Operational.Common.ConcreteExecution.
From RocqSched Require Import Operational.Common.Projection.
From RocqSched Require Import Operational.Common.OSLocalAdapterContract.
From RocqSched Require Import Operational.Common.OSSchedulerViewContract.
From RocqSched Require Import Operational.Common.OSCandidateSourceContract.
From RocqSched Require Import Refinement.OSSchedulerViewTheorem.
From RocqSched Require Import Refinement.OSRefinementTheorem.

Lemma local_candidate_source_contract_visible_complete :
  forall CState (P : OSLabeledProjection CState) jobs m
         (candidates_of : CandidateSource)
         (ex : labeled_concrete_execution P m)
         (Hcand :
            labeled_concrete_candidate_source_contract
              jobs m candidates_of ex)
         t j,
    op_job_visible
      m
      (os_to_op_state (osl_to_os_projection P) (lce_trace ex t))
      j ->
    In j (projected_candidate_list jobs m ex candidates_of t).
Proof.
  intros CState P jobs m candidates_of ex Hcand t j Hvisible.
  destruct Hvisible as [[c [Hlt Hcur]] | [Hin | [c [Hlt Htarget]]]].
  - exact (lccsc_current_in_candidates Hcand t c j Hlt Hcur).
  - exact (lccsc_runnable_in_candidates Hcand t j Hin).
  - exact (lccsc_dispatch_target_in_candidates Hcand t c j Hlt Htarget).
Qed.

Lemma os_local_candidate_source_adapter_contract_candidate_implies_released :
  forall CState (P : OSLabeledProjection CState)
         candidates_of jobs adm m
         (C : os_local_candidate_source_adapter_contract
                P candidates_of jobs adm m) t j,
    In j
       (projected_candidate_list
          jobs
          m
          (olac_execution (olcsac_base C))
          candidates_of
          t) ->
    released jobs j t.
Proof.
  intros CState P candidates_of jobs adm m C t j Hin.
  pose proof (os_local_multicore_adapter_contract_to_scheduler_view_contract
                CState P jobs adm m (olcsac_base C)) as Hview.
  pose proof (lccsc_candidates_visible (olcsac_candidates C) t j Hin) as Hvisible.
  exact (lcsv_visible_released Hview t j Hvisible).
Qed.

Lemma os_local_candidate_source_adapter_contract_candidate_not_completed :
  forall CState (P : OSLabeledProjection CState)
         candidates_of jobs adm m
         (C : os_local_candidate_source_adapter_contract
                P candidates_of jobs adm m) t j,
    In j
       (projected_candidate_list
          jobs
          m
          (olac_execution (olcsac_base C))
          candidates_of
          t) ->
    ~ completed
        jobs
        m
        (project_schedule
           (osl_to_op_trace P (lce_trace (olac_execution (olcsac_base C)))))
        j
        t.
Proof.
  intros CState P candidates_of jobs adm m C t j Hin.
  pose proof (os_local_multicore_adapter_contract_to_scheduler_view_contract
                CState P jobs adm m (olcsac_base C)) as Hview.
  pose proof (lccsc_candidates_visible (olcsac_candidates C) t j Hin) as Hvisible.
  exact (lcsv_visible_not_completed Hview t j Hvisible).
Qed.

Lemma os_local_candidate_source_adapter_contract_candidate_implies_eligible :
  forall CState (P : OSLabeledProjection CState)
         candidates_of jobs adm m
         (C : os_local_candidate_source_adapter_contract
                P candidates_of jobs adm m) t j,
    In j
       (projected_candidate_list
          jobs
          m
          (olac_execution (olcsac_base C))
          candidates_of
          t) ->
    eligible
      jobs
      m
      (project_schedule
         (osl_to_op_trace P (lce_trace (olac_execution (olcsac_base C)))))
      j
      t.
Proof.
  intros CState P candidates_of jobs adm m C t j Hin.
  pose proof (os_local_multicore_adapter_contract_to_scheduler_view_contract
                CState P jobs adm m (olcsac_base C)) as Hview.
  pose proof (lccsc_candidates_visible (olcsac_candidates C) t j Hin) as Hvisible.
  apply eligible_iff_released_and_not_completed.
  split.
  - exact (lcsv_visible_released Hview t j Hvisible).
  - exact (lcsv_visible_not_completed Hview t j Hvisible).
Qed.

Lemma os_local_candidate_source_adapter_contract_visible_in_candidates :
  forall CState (P : OSLabeledProjection CState)
         candidates_of jobs adm m
         (C : os_local_candidate_source_adapter_contract
                P candidates_of jobs adm m) t j,
    op_job_visible
      m
      (os_to_op_state (osl_to_os_projection P)
         (lce_trace (olac_execution (olcsac_base C)) t))
      j ->
    In j
       (projected_candidate_list
          jobs
          m
          (olac_execution (olcsac_base C))
          candidates_of
          t).
Proof.
  intros CState P candidates_of jobs adm m C t j Hvisible.
  eapply local_candidate_source_contract_visible_complete.
  - exact (olcsac_candidates C).
  - exact Hvisible.
Qed.

Lemma os_local_candidate_source_adapter_contract_choose_in_candidates :
  forall CState (P : OSLabeledProjection CState)
         candidates_of jobs adm m
         (C : os_local_candidate_source_adapter_contract
                P candidates_of jobs adm m) t c j,
    c < m ->
    os_step_label P
      (lce_trace (olac_execution (olcsac_base C)) t)
      (lce_trace (olac_execution (olcsac_base C)) (S t)) = EvChoose c j ->
    In j
       (projected_candidate_list
          jobs
          m
          (olac_execution (olcsac_base C))
          candidates_of
          t).
Proof.
  intros CState P candidates_of jobs adm m C t c j Hlt Hchoose.
  apply os_local_candidate_source_adapter_contract_visible_in_candidates.
  pose proof (os_local_multicore_adapter_contract_choose_from_runnable
                CState P jobs adm m (olcsac_base C) t c j Hlt Hchoose) as Hin.
  exact (or_intror (or_introl Hin)).
Qed.

Lemma os_local_candidate_source_adapter_contract_current_in_candidates :
  forall CState (P : OSLabeledProjection CState)
         candidates_of jobs adm m
         (C : os_local_candidate_source_adapter_contract
                P candidates_of jobs adm m) t c j,
    c < m ->
    op_current
      (os_to_op_state (osl_to_os_projection P)
         (lce_trace (olac_execution (olcsac_base C)) t))
      c = Some j ->
    In j
       (projected_candidate_list
          jobs
          m
          (olac_execution (olcsac_base C))
          candidates_of
          t).
Proof.
  intros CState P candidates_of jobs adm m C t c j Hlt Hcur.
  exact (lccsc_current_in_candidates (olcsac_candidates C) t c j Hlt Hcur).
Qed.

Lemma os_local_candidate_source_adapter_contract_runnable_in_candidates :
  forall CState (P : OSLabeledProjection CState)
         candidates_of jobs adm m
         (C : os_local_candidate_source_adapter_contract
                P candidates_of jobs adm m) t j,
    In j
       (op_runnable
          (os_to_op_state (osl_to_os_projection P)
             (lce_trace (olac_execution (olcsac_base C)) t))) ->
    In j
       (projected_candidate_list
          jobs
          m
          (olac_execution (olcsac_base C))
          candidates_of
          t).
Proof.
  intros CState P candidates_of jobs adm m C t j Hin.
  exact (lccsc_runnable_in_candidates (olcsac_candidates C) t j Hin).
Qed.

Lemma os_local_candidate_source_adapter_contract_dispatch_target_in_candidates :
  forall CState (P : OSLabeledProjection CState)
         candidates_of jobs adm m
         (C : os_local_candidate_source_adapter_contract
                P candidates_of jobs adm m) t c j,
    c < m ->
    op_dispatch_target
      (os_to_op_state (osl_to_os_projection P)
         (lce_trace (olac_execution (olcsac_base C)) t))
      c = Some j ->
    In j
       (projected_candidate_list
          jobs
          m
          (olac_execution (olcsac_base C))
          candidates_of
          t).
Proof.
  intros CState P candidates_of jobs adm m C t c j Hlt Htarget.
  exact (lccsc_dispatch_target_in_candidates
           (olcsac_candidates C) t c j Hlt Htarget).
Qed.
