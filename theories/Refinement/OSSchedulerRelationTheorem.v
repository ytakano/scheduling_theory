From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.Scheduler.Validity.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.TopMInterface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.TopMSchedulerBridge.
From RocqSched Require Import Refinement.SchedulingAlgorithmRefinement.
From RocqSched Require Import Multicore.Common.Admissibility.
From RocqSched Require Import Operational.Common.OSProjectionInterface.
From RocqSched Require Import Operational.Common.ConcreteExecution.
From RocqSched Require Import Operational.Common.Projection.
From RocqSched Require Import Operational.Common.OSLocalAdapterContract.
From RocqSched Require Import Operational.Common.OSCandidateSourceContract.
From RocqSched Require Import Operational.Common.OSSchedulerRelationContract.

Lemma labeled_concrete_single_cpu_scheduler_relation_contract_implies_scheduler_rel :
  forall CState (P : OSLabeledProjection CState)
         jobs spec candidates_of
         (ex : labeled_concrete_execution P 1),
    labeled_concrete_single_cpu_scheduler_relation_contract
      jobs
      spec
      candidates_of
      ex ->
    scheduler_rel
      (single_cpu_algorithm_schedule spec candidates_of)
      jobs
      1
      (projected_scheduler_relation_schedule ex).
Proof.
  intros CState P jobs spec candidates_of ex Hcontract.
  split.
  - reflexivity.
  - intros t.
    split.
    + exact (lcssrc_cpu0_follows_choose Hcontract t).
    + intros c Hc.
      exact (lcssrc_other_cpus_idle Hcontract t c Hc).
Qed.

Lemma labeled_concrete_top_m_scheduler_relation_contract_implies_scheduler_rel :
  forall CState (P : OSLabeledProjection CState)
         jobs m spec candidates_of
         (ex : labeled_concrete_execution P m),
    labeled_concrete_top_m_scheduler_relation_contract
      jobs
      m
      spec
      candidates_of
      ex ->
    scheduler_rel
      (top_m_algorithm_schedule spec candidates_of)
      jobs
      m
      (projected_scheduler_relation_schedule ex).
Proof.
  intros CState P jobs m spec candidates_of ex Hcontract.
  intros t c.
  exact (lctmsrc_cpu_follows_choose_top_m Hcontract t c).
Qed.

Lemma os_local_single_cpu_scheduler_relation_adapter_contract_implies_scheduler_rel :
  forall CState (P : OSLabeledProjection CState)
         jobs adm spec candidates_of
         (C : os_local_single_cpu_scheduler_relation_adapter_contract
                P
                spec
                candidates_of
                jobs
                adm),
    scheduler_rel
      (single_cpu_algorithm_schedule spec candidates_of)
      jobs
      1
      (project_schedule
         (osl_to_op_trace P
            (lce_trace (olac_execution (olcsac_base (olssrac_base C)))))).
Proof.
  intros CState P jobs adm spec candidates_of C.
  exact
    (labeled_concrete_single_cpu_scheduler_relation_contract_implies_scheduler_rel
       CState
       P
       jobs
       spec
       candidates_of
       (olac_execution (olcsac_base (olssrac_base C)))
       (olssrac_relation C)).
Qed.

Lemma os_local_top_m_scheduler_relation_adapter_contract_implies_scheduler_rel :
  forall CState (P : OSLabeledProjection CState)
         jobs adm m spec candidates_of
         (C : os_local_top_m_scheduler_relation_adapter_contract
                P
                spec
                candidates_of
                jobs
                adm
                m),
    scheduler_rel
      (top_m_algorithm_schedule spec candidates_of)
      jobs
      m
      (project_schedule
         (osl_to_op_trace P
            (lce_trace (olac_execution (olcsac_base (oltsrac_base C)))))).
Proof.
  intros CState P jobs adm m spec candidates_of C.
  exact
    (labeled_concrete_top_m_scheduler_relation_contract_implies_scheduler_rel
       CState
       P
       jobs
       m
       spec
       candidates_of
       (olac_execution (olcsac_base (oltsrac_base C)))
       (oltsrac_relation C)).
Qed.

Lemma os_local_single_cpu_scheduler_relation_adapter_contract_respects_algorithm_spec_at_with :
  forall CState (P : OSLabeledProjection CState)
         jobs adm spec policy candidates_of t
         (C : os_local_single_cpu_scheduler_relation_adapter_contract
                P
                spec
                candidates_of
                jobs
                adm),
    algorithm_refines_spec spec policy ->
    respects_algorithm_spec_at_with
      policy
      jobs
      candidates_of
      (project_schedule
         (osl_to_op_trace P
            (lce_trace (olac_execution (olcsac_base (olssrac_base C))))))
      t.
Proof.
  intros CState P jobs adm spec policy candidates_of t C Href.
  eapply single_cpu_algorithm_schedule_respects_algorithm_spec_at_with.
  - exact Href.
  - apply os_local_single_cpu_scheduler_relation_adapter_contract_implies_scheduler_rel.
Qed.
