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
From RocqSched Require Import Operational.Common.OSHandoffContract.

Lemma os_local_multicore_adapter_contract_need_resched_preserved :
  forall CState (P : OSLabeledProjection CState) jobs adm m
         (C : os_local_multicore_adapter_contract P jobs adm m) t c,
    c < m ->
    op_need_resched
      (os_to_op_state (osl_to_os_projection P) (lce_trace (olac_execution C) t))
      c = true ->
    ~ ev_consumes_need_resched_on
        c
        (os_step_label P (lce_trace (olac_execution C) t)
           (lce_trace (olac_execution C) (S t))) ->
    op_need_resched
      (os_to_op_state (osl_to_os_projection P) (lce_trace (olac_execution C) (S t)))
      c = true.
Proof.
  intros CState P jobs adm m C t c Hlt Hneed Hnotconsume.
  pose proof (os_local_scheduler_handoff_contract C) as Hhandoff.
  exact (lchc_need_resched_preserved Hhandoff t c Hlt Hneed Hnotconsume).
Qed.

Lemma os_local_multicore_adapter_contract_dispatch_clears_need_resched :
  forall CState (P : OSLabeledProjection CState) jobs adm m
         (C : os_local_multicore_adapter_contract P jobs adm m) t c j,
    c < m ->
    os_step_label P (lce_trace (olac_execution C) t)
      (lce_trace (olac_execution C) (S t)) = EvDispatch c j ->
    op_need_resched
      (os_to_op_state (osl_to_os_projection P) (lce_trace (olac_execution C) (S t)))
      c = false.
Proof.
  intros CState P jobs adm m C t c j Hlt Hdispatch.
  pose proof (os_local_scheduler_handoff_contract C) as Hhandoff.
  exact (lchc_need_resched_cleared_by_dispatch Hhandoff t c j Hlt Hdispatch).
Qed.

Lemma os_local_multicore_adapter_contract_preempt_clears_need_resched :
  forall CState (P : OSLabeledProjection CState) jobs adm m
         (C : os_local_multicore_adapter_contract P jobs adm m) t c old new,
    c < m ->
    os_step_label P (lce_trace (olac_execution C) t)
      (lce_trace (olac_execution C) (S t)) = EvPreempt c old new ->
    op_need_resched
      (os_to_op_state (osl_to_os_projection P) (lce_trace (olac_execution C) (S t)))
      c = false.
Proof.
  intros CState P jobs adm m C t c old new Hlt Hpreempt.
  pose proof (os_local_scheduler_handoff_contract C) as Hhandoff.
  exact (lchc_need_resched_cleared_by_preempt Hhandoff t c old new Hlt Hpreempt).
Qed.

Lemma os_local_multicore_adapter_contract_dispatch_target_preserved :
  forall CState (P : OSLabeledProjection CState) jobs adm m
         (C : os_local_multicore_adapter_contract P jobs adm m) t c j,
    c < m ->
    op_dispatch_target
      (os_to_op_state (osl_to_os_projection P) (lce_trace (olac_execution C) t))
      c = Some j ->
    ~ ev_consumes_dispatch_target_on
        c
        j
        (os_step_label P (lce_trace (olac_execution C) t)
           (lce_trace (olac_execution C) (S t))) ->
    op_dispatch_target
      (os_to_op_state (osl_to_os_projection P) (lce_trace (olac_execution C) (S t)))
      c = Some j.
Proof.
  intros CState P jobs adm m C t c j Hlt Htarget Hnotconsume.
  pose proof (os_local_scheduler_handoff_contract C) as Hhandoff.
  exact (lchc_dispatch_target_preserved Hhandoff t c j Hlt Htarget Hnotconsume).
Qed.

Lemma os_local_multicore_adapter_contract_dispatch_consumes_dispatch_target :
  forall CState (P : OSLabeledProjection CState) jobs adm m
         (C : os_local_multicore_adapter_contract P jobs adm m) t c j,
    c < m ->
    os_step_label P (lce_trace (olac_execution C) t)
      (lce_trace (olac_execution C) (S t)) = EvDispatch c j ->
    op_dispatch_target
      (os_to_op_state (osl_to_os_projection P) (lce_trace (olac_execution C) (S t)))
      c = None.
Proof.
  intros CState P jobs adm m C t c j Hlt Hdispatch.
  pose proof (os_local_scheduler_handoff_contract C) as Hhandoff.
  exact (lchc_dispatch_target_consumed_by_dispatch Hhandoff t c j Hlt Hdispatch).
Qed.

Lemma os_local_multicore_adapter_contract_preempt_consumes_dispatch_target :
  forall CState (P : OSLabeledProjection CState) jobs adm m
         (C : os_local_multicore_adapter_contract P jobs adm m) t c old new,
    c < m ->
    os_step_label P (lce_trace (olac_execution C) t)
      (lce_trace (olac_execution C) (S t)) = EvPreempt c old new ->
    op_dispatch_target
      (os_to_op_state (osl_to_os_projection P) (lce_trace (olac_execution C) (S t)))
      c = None.
Proof.
  intros CState P jobs adm m C t c old new Hlt Hpreempt.
  pose proof (os_local_scheduler_handoff_contract C) as Hhandoff.
  exact (lchc_dispatch_target_consumed_by_preempt Hhandoff t c old new Hlt Hpreempt).
Qed.

Lemma os_local_multicore_adapter_contract_block_clears_dispatch_target :
  forall CState (P : OSLabeledProjection CState) jobs adm m
         (C : os_local_multicore_adapter_contract P jobs adm m) t c j,
    c < m ->
    os_step_label P (lce_trace (olac_execution C) t)
      (lce_trace (olac_execution C) (S t)) = EvBlock j ->
    op_dispatch_target
      (os_to_op_state (osl_to_os_projection P) (lce_trace (olac_execution C) (S t)))
      c <> Some j.
Proof.
  intros CState P jobs adm m C t c j Hlt Hblock.
  pose proof (os_local_scheduler_handoff_contract C) as Hhandoff.
  exact (lchc_dispatch_target_cleared_by_block Hhandoff t c j Hlt Hblock).
Qed.

Lemma os_local_multicore_adapter_contract_complete_clears_dispatch_target :
  forall CState (P : OSLabeledProjection CState) jobs adm m
         (C : os_local_multicore_adapter_contract P jobs adm m) t c j,
    c < m ->
    os_step_label P (lce_trace (olac_execution C) t)
      (lce_trace (olac_execution C) (S t)) = EvComplete j ->
    op_dispatch_target
      (os_to_op_state (osl_to_os_projection P) (lce_trace (olac_execution C) (S t)))
      c <> Some j.
Proof.
  intros CState P jobs adm m C t c j Hlt Hcomplete.
  pose proof (os_local_scheduler_handoff_contract C) as Hhandoff.
  exact (lchc_dispatch_target_cleared_by_complete Hhandoff t c j Hlt Hcomplete).
Qed.
