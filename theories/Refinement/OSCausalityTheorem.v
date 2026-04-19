From Stdlib Require Import List.
Import ListNotations.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Multicore.Common.MultiCoreBase.
From RocqSched Require Import Multicore.Common.Admissibility.
From RocqSched Require Import Operational.Common.State.
From RocqSched Require Import Operational.Common.Step.
From RocqSched Require Import Operational.Common.OSProjectionInterface.
From RocqSched Require Import Operational.Common.ConcreteExecution.
From RocqSched Require Import Operational.Common.OSLocalAdapterContract.
From RocqSched Require Import Operational.Common.OSCausalityContract.

Lemma os_local_multicore_adapter_contract_dispatch_sets_current :
  forall CState (P : OSLabeledProjection CState) jobs adm m
         (C : os_local_multicore_adapter_contract P jobs adm m) t c j,
    c < m ->
    os_step_label P (lce_trace (olac_execution C) t) (lce_trace (olac_execution C) (S t)) =
    EvDispatch c j ->
    op_current
      (os_to_op_state (osl_to_os_projection P) (lce_trace (olac_execution C) (S t)))
      c = Some j.
Proof.
  intros CState P jobs adm m C t c j Hlt Hdispatch.
  pose proof (os_local_multicore_adapter_contract_to_causality_contract
                CState P jobs adm m C) as Hcaus.
  exact (lcsc_dispatch_sets_current Hcaus t c j Hlt Hdispatch).
Qed.

Lemma os_local_multicore_adapter_contract_preempt_requeues_old :
  forall CState (P : OSLabeledProjection CState) jobs adm m
         (C : os_local_multicore_adapter_contract P jobs adm m) t c old new,
    c < m ->
    os_step_label P (lce_trace (olac_execution C) t) (lce_trace (olac_execution C) (S t)) =
    EvPreempt c old new ->
    In old
       (op_runnable
          (os_to_op_state (osl_to_os_projection P) (lce_trace (olac_execution C) (S t)))).
Proof.
  intros CState P jobs adm m C t c old new Hlt Hpreempt.
  pose proof (os_local_multicore_adapter_contract_to_causality_contract
                CState P jobs adm m C) as Hcaus.
  exact (lcsc_preempt_requeues_old Hcaus t c old new Hlt Hpreempt).
Qed.

Lemma os_local_multicore_adapter_contract_complete_clears_dispatch_target :
  forall CState (P : OSLabeledProjection CState) jobs adm m
         (C : os_local_multicore_adapter_contract P jobs adm m) t c j,
    c < m ->
    os_step_label P (lce_trace (olac_execution C) t) (lce_trace (olac_execution C) (S t)) =
    EvComplete j ->
    op_dispatch_target
      (os_to_op_state (osl_to_os_projection P) (lce_trace (olac_execution C) (S t)))
      c <> Some j.
Proof.
  intros CState P jobs adm m C t c j Hlt Hcomplete.
  pose proof (os_local_multicore_adapter_contract_to_causality_contract
                CState P jobs adm m C) as Hcaus.
  exact (lcsc_complete_clears_dispatch_target Hcaus t c j Hlt Hcomplete).
Qed.
