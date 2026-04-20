From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.Scheduler.Validity.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.TopMInterface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.TopMSchedulerBridge.
From RocqSched Require Import Refinement.SchedulingAlgorithmRefinement.
From RocqSched Require Import Multicore.Common.MultiCoreBase.
From RocqSched Require Import Multicore.Common.Admissibility.
From RocqSched Require Import Multicore.Common.AdmissibleCandidateSource.
From RocqSched Require Import Multicore.Common.TopMAdmissibilityBridge.
From RocqSched Require Import Operational.Common.OSProjectionInterface.
From RocqSched Require Import Operational.Common.ConcreteExecution.
From RocqSched Require Import Operational.Common.Projection.
From RocqSched Require Import Operational.Common.OSLocalAdapterContract.
From RocqSched Require Import Operational.Common.OSCandidateSourceContract.
From RocqSched Require Import Operational.Common.OSSchedulerRelationContract.
From RocqSched Require Import Operational.Common.OSAlgorithmAdapterContract.
From RocqSched Require Import Refinement.OSSchedulerRelationTheorem.

Lemma os_single_cpu_algorithm_adapter_contract_implies_scheduler_rel :
  forall CState (P : OSLabeledProjection CState)
         J spec candidates_of jobs adm
         (C : os_single_cpu_algorithm_adapter_contract
                P J spec candidates_of jobs adm),
    scheduler_rel
      (single_cpu_algorithm_schedule spec candidates_of)
      jobs
      1
      (project_schedule
         (osl_to_op_trace P
            (lce_trace
               (olac_execution
                  (olcsac_base
                     (olssrac_base (osaac_scheduler_relation C))))))).
Proof.
  intros CState P J spec candidates_of jobs adm C.
  apply os_local_single_cpu_scheduler_relation_adapter_contract_implies_scheduler_rel.
Qed.

Lemma os_single_cpu_algorithm_adapter_contract_implies_valid_schedule :
  forall CState (P : OSLabeledProjection CState)
         J spec candidates_of jobs adm
         (C : os_single_cpu_algorithm_adapter_contract
                P J spec candidates_of jobs adm),
    valid_schedule
      jobs
      1
      (project_schedule
         (osl_to_op_trace P
            (lce_trace
               (olac_execution
                  (olcsac_base
                     (olssrac_base (osaac_scheduler_relation C))))))).
Proof.
  intros CState P J spec candidates_of jobs adm C.
  eapply single_cpu_algorithm_valid.
  apply os_single_cpu_algorithm_adapter_contract_implies_scheduler_rel.
Qed.

Lemma os_single_cpu_algorithm_adapter_contract_scheduled_job_in_subset :
  forall CState (P : OSLabeledProjection CState)
         J spec candidates_of jobs adm
         (C : os_single_cpu_algorithm_adapter_contract
                P J spec candidates_of jobs adm) t j,
    project_schedule
      (osl_to_op_trace P
         (lce_trace
            (olac_execution
               (olcsac_base
                  (olssrac_base (osaac_scheduler_relation C)))))) t 0 = Some j ->
    J j.
Proof.
  intros CState P J spec candidates_of jobs adm C t j Hrun.
  eapply single_cpu_algorithm_in_subset.
  - exact (osaac_candidate_source_spec C).
  - apply os_single_cpu_algorithm_adapter_contract_implies_scheduler_rel.
  - exact Hrun.
Qed.

Lemma os_single_cpu_algorithm_adapter_contract_respects_algorithm_spec_at_with :
  forall CState (P : OSLabeledProjection CState)
         J spec policy candidates_of jobs adm t
         (C : os_single_cpu_algorithm_adapter_contract
                P J spec candidates_of jobs adm),
    algorithm_refines_spec spec policy ->
    respects_algorithm_spec_at_with
      policy
      jobs
      candidates_of
      (project_schedule
         (osl_to_op_trace P
            (lce_trace
               (olac_execution
                  (olcsac_base
                     (olssrac_base (osaac_scheduler_relation C)))))))
      t.
Proof.
  intros CState P J spec policy candidates_of jobs adm t C Href.
  eapply single_cpu_algorithm_schedule_respects_algorithm_spec_at_with.
  - exact Href.
  - apply os_single_cpu_algorithm_adapter_contract_implies_scheduler_rel.
Qed.

Lemma os_top_m_algorithm_adapter_contract_implies_scheduler_rel :
  forall CState (P : OSLabeledProjection CState)
         J spec candidates_of jobs adm m
         (C : os_top_m_algorithm_adapter_contract
                P J spec candidates_of jobs adm m),
    scheduler_rel
      (top_m_algorithm_schedule spec candidates_of)
      jobs
      m
      (project_schedule
         (osl_to_op_trace P
            (lce_trace
               (olac_execution
                  (olcsac_base
                     (oltsrac_base (otmaac_scheduler_relation C))))))).
Proof.
  intros CState P J spec candidates_of jobs adm m C.
  apply os_local_top_m_scheduler_relation_adapter_contract_implies_scheduler_rel.
Qed.

Lemma os_top_m_algorithm_adapter_contract_implies_valid_schedule :
  forall CState (P : OSLabeledProjection CState)
         J spec candidates_of jobs adm m
         (C : os_top_m_algorithm_adapter_contract
                P J spec candidates_of jobs adm m),
    valid_schedule
      jobs
      m
      (project_schedule
         (osl_to_op_trace P
            (lce_trace
               (olac_execution
                  (olcsac_base
                     (oltsrac_base (otmaac_scheduler_relation C))))))).
Proof.
  intros CState P J spec candidates_of jobs adm m C.
  eapply top_m_algorithm_valid.
  apply os_top_m_algorithm_adapter_contract_implies_scheduler_rel.
Qed.

Lemma os_top_m_algorithm_adapter_contract_running_in_subset :
  forall CState (P : OSLabeledProjection CState)
         J spec candidates_of jobs adm m
         (C : os_top_m_algorithm_adapter_contract
                P J spec candidates_of jobs adm m) t c j,
    c < m ->
    project_schedule
      (osl_to_op_trace P
         (lce_trace
            (olac_execution
               (olcsac_base
                  (oltsrac_base (otmaac_scheduler_relation C)))))) t c = Some j ->
    J j.
Proof.
  intros CState P J spec candidates_of jobs adm m C t c j Hlt Hrun.
  eapply top_m_algorithm_in_admissible_subset.
  - exact (otmaac_candidate_source_spec C).
  - apply os_top_m_algorithm_adapter_contract_implies_scheduler_rel.
  - exact Hlt.
  - exact Hrun.
Qed.

Lemma os_top_m_algorithm_adapter_contract_some_cpu_busy_if_subset_admissible_somewhere :
  forall CState (P : OSLabeledProjection CState)
         J spec candidates_of jobs adm m
         (C : os_top_m_algorithm_adapter_contract
                P J spec candidates_of jobs adm m) t,
    0 < m ->
    (exists j,
       J j /\
       admissible_somewhere
         adm
         jobs
         m
         (project_schedule
            (osl_to_op_trace P
               (lce_trace
                  (olac_execution
                     (olcsac_base
                        (oltsrac_base (otmaac_scheduler_relation C)))))))
         j
         t) ->
    exists c,
      c < m /\
      cpu_busy
        (project_schedule
           (osl_to_op_trace P
              (lce_trace
                 (olac_execution
                    (olcsac_base
                       (oltsrac_base (otmaac_scheduler_relation C)))))))
        t c.
Proof.
  intros CState P J spec candidates_of jobs adm m C t Hm Hex.
  eapply top_m_algorithm_some_cpu_busy_if_subset_admissible_somewhere_gen.
  - exact (otmaac_candidate_source_spec C).
  - apply os_top_m_algorithm_adapter_contract_implies_scheduler_rel.
  - exact Hm.
  - exact Hex.
Qed.

Lemma os_top_m_algorithm_adapter_contract_running_if_some_cpu_idle_and_subset_admissible_somewhere :
  forall CState (P : OSLabeledProjection CState)
         J spec candidates_of jobs adm m
         (C : os_top_m_algorithm_adapter_contract
                P J spec candidates_of jobs adm m) t j,
    some_cpu_idle
      m
      (project_schedule
         (osl_to_op_trace P
            (lce_trace
               (olac_execution
                  (olcsac_base
                     (oltsrac_base (otmaac_scheduler_relation C)))))))
      t ->
    J j ->
    admissible_somewhere
      adm
      jobs
      m
      (project_schedule
         (osl_to_op_trace P
            (lce_trace
               (olac_execution
                  (olcsac_base
                     (oltsrac_base (otmaac_scheduler_relation C)))))))
      j
      t ->
    running
      m
      (project_schedule
         (osl_to_op_trace P
            (lce_trace
               (olac_execution
                  (olcsac_base
                     (oltsrac_base (otmaac_scheduler_relation C)))))))
      j
      t.
Proof.
  intros CState P J spec candidates_of jobs adm m C t j Hidle HJ Hadm.
  eapply top_m_algorithm_running_if_some_cpu_idle_and_subset_admissible_somewhere_gen.
  - exact (otmaac_candidate_source_spec C).
  - apply os_top_m_algorithm_adapter_contract_implies_scheduler_rel.
  - exact Hidle.
  - exact HJ.
  - exact Hadm.
Qed.

Lemma os_strong_top_m_algorithm_adapter_contract_all_cpus_idle_if_no_subset_admissible_somewhere :
  forall CState (P : OSLabeledProjection CState)
         J spec candidates_of jobs adm m
         (C : os_strong_top_m_algorithm_adapter_contract
                P J spec candidates_of jobs adm m) t,
    (forall j,
        J j ->
        ~ admissible_somewhere
            adm
            jobs
            m
            (project_schedule
               (osl_to_op_trace P
                  (lce_trace
                     (olac_execution
                        (olcsac_base
                           (oltsrac_base
                              (otmaac_scheduler_relation (ostmaac_base C))))))))
            j
            t) ->
    all_cpus_idle
      m
      (project_schedule
         (osl_to_op_trace P
            (lce_trace
               (olac_execution
                  (olcsac_base
                     (oltsrac_base
                        (otmaac_scheduler_relation (ostmaac_base C))))))))
      t.
Proof.
  intros CState P J spec candidates_of jobs adm m C t Hnone.
  eapply top_m_algorithm_all_cpus_idle_if_no_subset_admissible_somewhere_gen.
  - exact (ostmaac_candidate_source_spec C).
  - apply os_top_m_algorithm_adapter_contract_implies_scheduler_rel.
  - exact Hnone.
Qed.

Lemma os_strong_top_m_algorithm_adapter_contract_selected_from_subset_admissible_somewhere :
  forall CState (P : OSLabeledProjection CState)
         J spec candidates_of jobs adm m
         (C : os_strong_top_m_algorithm_adapter_contract
                P J spec candidates_of jobs adm m) t,
    top_m_selected_from
      (subset_admissible_somewhere_at
         adm
         J
         jobs
         m
         (project_schedule
            (osl_to_op_trace P
               (lce_trace
                  (olac_execution
                     (olcsac_base
                        (oltsrac_base
                           (otmaac_scheduler_relation (ostmaac_base C))))))))
         t)
      m
      (project_schedule
         (osl_to_op_trace P
            (lce_trace
               (olac_execution
                  (olcsac_base
                     (oltsrac_base
                        (otmaac_scheduler_relation (ostmaac_base C))))))))
      t.
Proof.
  intros CState P J spec candidates_of jobs adm m C t.
  eapply top_m_algorithm_selected_from_subset_admissible_somewhere_strong_gen.
  - exact (ostmaac_candidate_source_spec C).
  - apply os_top_m_algorithm_adapter_contract_implies_scheduler_rel.
Qed.
