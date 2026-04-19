From Stdlib Require Import List.
Import ListNotations.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Semantics.ScheduleLemmas.ScheduleFacts.
From RocqSched Require Import Multicore.Common.MultiCoreBase.
From RocqSched Require Import Multicore.Common.Admissibility.
From RocqSched Require Import Operational.Common.State.
From RocqSched Require Import Operational.Common.Step.
From RocqSched Require Import Operational.Common.OSProjectionInterface.
From RocqSched Require Import Operational.Common.ConcreteExecution.
From RocqSched Require Import Operational.Common.Projection.
From RocqSched Require Import Operational.Common.OSLocalAdapterContract.
From RocqSched Require Import Operational.Common.OSSchedulerViewContract.

Lemma os_local_multicore_adapter_contract_runnable_implies_released :
  forall CState (P : OSLabeledProjection CState) jobs adm m
         (C : os_local_multicore_adapter_contract P jobs adm m) t j,
    In j
       (op_runnable
          (os_to_op_state (osl_to_os_projection P) (lce_trace (olac_execution C) t))) ->
    released jobs j t.
Proof.
  intros CState P jobs adm m C t j Hin.
  pose proof (os_local_multicore_adapter_contract_to_scheduler_view_contract
                CState P jobs adm m C) as Hview.
  exact (lcsv_visible_released Hview t j (or_intror (or_introl Hin))).
Qed.

Lemma os_local_multicore_adapter_contract_runnable_not_completed :
  forall CState (P : OSLabeledProjection CState) jobs adm m
         (C : os_local_multicore_adapter_contract P jobs adm m) t j,
    In j
       (op_runnable
          (os_to_op_state (osl_to_os_projection P) (lce_trace (olac_execution C) t))) ->
    ~ completed
        jobs
        m
        (project_schedule (osl_to_op_trace P (lce_trace (olac_execution C))))
        j t.
Proof.
  intros CState P jobs adm m C t j Hin.
  pose proof (os_local_multicore_adapter_contract_to_scheduler_view_contract
                CState P jobs adm m C) as Hview.
  exact (lcsv_visible_not_completed Hview t j (or_intror (or_introl Hin))).
Qed.

Lemma os_local_multicore_adapter_contract_dispatch_target_implies_released :
  forall CState (P : OSLabeledProjection CState) jobs adm m
         (C : os_local_multicore_adapter_contract P jobs adm m) t c j,
    c < m ->
    op_dispatch_target
      (os_to_op_state (osl_to_os_projection P) (lce_trace (olac_execution C) t))
      c = Some j ->
    released jobs j t.
Proof.
  intros CState P jobs adm m C t c j Hlt Htarget.
  pose proof (os_local_multicore_adapter_contract_to_scheduler_view_contract
                CState P jobs adm m C) as Hview.
  exact (lcsv_visible_released Hview t j (or_intror (or_intror (ex_intro _ c (conj Hlt Htarget))))).
Qed.

Lemma os_local_multicore_adapter_contract_dispatch_target_not_completed :
  forall CState (P : OSLabeledProjection CState) jobs adm m
         (C : os_local_multicore_adapter_contract P jobs adm m) t c j,
    c < m ->
    op_dispatch_target
      (os_to_op_state (osl_to_os_projection P) (lce_trace (olac_execution C) t))
      c = Some j ->
    ~ completed
        jobs
        m
        (project_schedule (osl_to_op_trace P (lce_trace (olac_execution C))))
        j t.
Proof.
  intros CState P jobs adm m C t c j Hlt Htarget.
  pose proof (os_local_multicore_adapter_contract_to_scheduler_view_contract
                CState P jobs adm m C) as Hview.
  exact (lcsv_visible_not_completed Hview t j (or_intror (or_intror (ex_intro _ c (conj Hlt Htarget))))).
Qed.

Lemma os_local_multicore_adapter_contract_visible_implies_eligible :
  forall CState (P : OSLabeledProjection CState) jobs adm m
         (C : os_local_multicore_adapter_contract P jobs adm m) t j,
    op_job_visible
      m
      (os_to_op_state (osl_to_os_projection P) (lce_trace (olac_execution C) t))
      j ->
    eligible
      jobs
      m
      (project_schedule (osl_to_op_trace P (lce_trace (olac_execution C))))
      j t.
Proof.
  intros CState P jobs adm m C t j Hvisible.
  pose proof (os_local_multicore_adapter_contract_to_scheduler_view_contract
                CState P jobs adm m C) as Hview.
  apply eligible_iff_released_and_not_completed.
  split.
  - exact (lcsv_visible_released Hview t j Hvisible).
  - exact (lcsv_visible_not_completed Hview t j Hvisible).
Qed.

Lemma os_local_multicore_adapter_contract_block_clears_runnable :
  forall CState (P : OSLabeledProjection CState) jobs adm m
         (C : os_local_multicore_adapter_contract P jobs adm m) t j,
    os_step_label P (lce_trace (olac_execution C) t) (lce_trace (olac_execution C) (S t)) =
    EvBlock j ->
    ~ In j
         (op_runnable
            (os_to_op_state (osl_to_os_projection P) (lce_trace (olac_execution C) (S t)))).
Proof.
  intros CState P jobs adm m C t j Hblock.
  pose proof (os_local_multicore_adapter_contract_to_scheduler_view_contract
                CState P jobs adm m C) as Hview.
  exact (lcsv_block_clears_runnable Hview t j Hblock).
Qed.
