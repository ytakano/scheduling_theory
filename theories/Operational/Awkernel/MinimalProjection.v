From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Operational.Common.State.
From RocqSched Require Import Operational.Common.Trace.
From RocqSched Require Import Operational.Common.Projection.
From RocqSched Require Import Operational.Common.Invariants.
From RocqSched Require Import Operational.Common.Execution.
From RocqSched Require Import Operational.Common.LabeledExecution.
From RocqSched Require Import Operational.Common.Step.
From RocqSched Require Import Operational.Common.ConcreteExecution.
From RocqSched Require Import Operational.Common.OSProjectionInterface.
From RocqSched Require Import Operational.Common.OSLocalAdapterContract.
From RocqSched Require Import Operational.Common.OSAdapterContract.
From RocqSched Require Import Operational.Common.OSCausalityContract.
From RocqSched Require Import Operational.Common.OSSchedulerViewContract.
From RocqSched Require Import Operational.Common.OSHandoffContract.
From RocqSched Require Import Operational.Common.OSCandidateSourceContract.
From RocqSched Require Import Operational.Common.OSAdmissibleCandidateSourceContract.
From RocqSched Require Import Operational.Common.OSSchedulerRelationContract.
From RocqSched Require Import Operational.Common.OSAlgorithmAdapterContract.
From RocqSched Require Import Operational.Common.OSDelayAdapterContract.
From RocqSched Require Import Refinement.OSCausalityTheorem.
From RocqSched Require Import Refinement.OSSchedulerViewTheorem.
From RocqSched Require Import Refinement.OSHandoffTheorem.
From RocqSched Require Import Refinement.OSCandidateSourceTheorem.
From RocqSched Require Import Refinement.OSAdmissibleCandidateSourceTheorem.
From RocqSched Require Import Refinement.OSSchedulerRelationTheorem.
From RocqSched Require Import Refinement.OSDelayAdapterTheorem.
From RocqSched Require Import Refinement.OSRefinementTheorem.
From RocqSched Require Import Operational.Common.ProjectionLemmas.
From RocqSched Require Import Operational.Common.ProjectionInvariants.
From RocqSched Require Import Operational.Common.ProjectionMulticoreValidity.
From RocqSched Require Import Multicore.Common.MultiCoreBase.
From RocqSched Require Import Multicore.Common.PlacementFacts.
From RocqSched Require Import Multicore.Common.ValidityFacts.
Import ListNotations.

Record AwkernelState : Type := mkAwkernelState {
  awk_current : CPU -> option JobId;
  awk_runnable : list JobId;
  awk_need_resched : CPU -> bool;
  awk_dispatch_target : CPU -> option JobId;
}.

Definition awk_to_op_state (st : AwkernelState) : OpState :=
  mkOpState
    (awk_current st)
    (awk_runnable st)
    (awk_need_resched st)
    (awk_dispatch_target st).

Definition AwkernelTrace : Type := Time -> AwkernelState.

Definition awk_to_op_trace (tr : AwkernelTrace) : OpTrace :=
  fun t => awk_to_op_state (tr t).

Definition awk_projection : OSProjection AwkernelState :=
  mkOSProjection AwkernelState awk_to_op_state.

Definition awk_labeled_projection
    (labeler : AwkernelState -> AwkernelState -> OpEvent)
    : OSLabeledProjection AwkernelState :=
  mkOSLabeledProjection AwkernelState awk_projection labeler.

Definition awk_labeled_concrete_projection_sound :=
  @labeled_concrete_projection_sound AwkernelState.

Definition awk_labeled_concrete_multicore_projection_sound :=
  @labeled_concrete_multicore_projection_sound AwkernelState.

Definition awk_local_labeled_concrete_projection_sound :=
  @local_labeled_concrete_projection_sound AwkernelState.

Definition awk_local_labeled_concrete_multicore_projection_sound :=
  @local_labeled_concrete_multicore_projection_sound AwkernelState.

Definition awk_local_adapter_contract :=
  @os_local_multicore_adapter_contract AwkernelState.

Definition awk_labeled_concrete_scheduling_causality_contract :=
  @labeled_concrete_scheduling_causality_contract AwkernelState.

Definition awk_local_scheduling_causality_contract :=
  @os_local_scheduling_causality_contract AwkernelState.

Definition awk_labeled_concrete_scheduler_view_contract :=
  @labeled_concrete_scheduler_view_contract AwkernelState.

Definition awk_local_scheduler_view_contract :=
  @os_local_scheduler_view_contract AwkernelState.

Definition awk_labeled_concrete_scheduler_handoff_contract :=
  @labeled_concrete_scheduler_handoff_contract AwkernelState.

Definition awk_local_scheduler_handoff_contract :=
  @os_local_scheduler_handoff_contract AwkernelState.

Definition awk_labeled_concrete_candidate_source_contract :=
  @labeled_concrete_candidate_source_contract AwkernelState.

Definition awk_local_candidate_source_adapter_contract :=
  @os_local_candidate_source_adapter_contract AwkernelState.

Definition awk_labeled_concrete_admissible_candidate_source_contract :=
  @labeled_concrete_admissible_candidate_source_contract AwkernelState.

Definition awk_labeled_concrete_strong_admissible_candidate_source_contract :=
  @labeled_concrete_strong_admissible_candidate_source_contract AwkernelState.

Definition awk_local_admissible_candidate_source_adapter_contract :=
  @os_local_admissible_candidate_source_adapter_contract AwkernelState.

Definition awk_local_strong_admissible_candidate_source_adapter_contract :=
  @os_local_strong_admissible_candidate_source_adapter_contract AwkernelState.

Definition awk_labeled_concrete_single_cpu_scheduler_relation_contract :=
  @labeled_concrete_single_cpu_scheduler_relation_contract AwkernelState.

Definition awk_labeled_concrete_top_m_scheduler_relation_contract :=
  @labeled_concrete_top_m_scheduler_relation_contract AwkernelState.

Definition awk_local_single_cpu_scheduler_relation_adapter_contract :=
  @os_local_single_cpu_scheduler_relation_adapter_contract AwkernelState.

Definition awk_local_top_m_scheduler_relation_adapter_contract :=
  @os_local_top_m_scheduler_relation_adapter_contract AwkernelState.

Definition awk_single_cpu_algorithm_adapter_contract :=
  @os_single_cpu_algorithm_adapter_contract AwkernelState.

Definition awk_top_m_algorithm_adapter_contract :=
  @os_top_m_algorithm_adapter_contract AwkernelState.

Definition awk_strong_top_m_algorithm_adapter_contract :=
  @os_strong_top_m_algorithm_adapter_contract AwkernelState.

Definition awk_adapter_contract :=
  @os_multicore_adapter_contract AwkernelState.

Definition awk_delay_adapter_contract :=
  @os_delay_adapter_contract AwkernelState.

Definition awk_delay_top_m_adapter_contract :=
  @os_delay_top_m_adapter_contract AwkernelState.

Definition awk_project_schedule (tr : AwkernelTrace) : Schedule :=
  project_schedule (awk_to_op_trace tr).

Definition awk_projected_running
    (m : nat) (tr : AwkernelTrace) (j : JobId) (t : Time) : Prop :=
  projected_running m (awk_to_op_trace tr) j t.

Definition awk_idle_outside_range (m : nat) (st : AwkernelState) : Prop :=
  op_idle_outside_range m (awk_to_op_state st).

Definition awk_respects_admissibility
    (adm : admissible_cpu) (m : nat) (st : AwkernelState) : Prop :=
  op_respects_admissibility adm m (awk_to_op_state st).

Record awk_execution (m : nat) : Type := mkAwkExecution {
  awk_ex_trace : AwkernelTrace;
  awk_ex_init : Prop;
  awk_ex_stepwise : trace_stepwise (awk_to_op_trace awk_ex_trace);
  awk_ex_struct_inv : forall t, op_struct_inv m (awk_to_op_state (awk_ex_trace t));
}.

Arguments awk_ex_trace {m} _ _.
Arguments awk_ex_init {m} _.
Arguments awk_ex_stepwise {m} _ _.
Arguments awk_ex_struct_inv {m} _ _.

Definition awk_to_execution {m} (ex : awk_execution m) : execution m :=
  mkExecution
    m
    (awk_to_op_trace (awk_ex_trace ex))
    (awk_ex_init ex)
    (awk_ex_stepwise ex)
    (awk_ex_struct_inv ex).

Definition awk_trace_sound
    (jobs : JobId -> Job) (m : nat) (ex : awk_execution m) : Prop :=
  execution_projection_sound jobs m (awk_to_execution ex).

Definition awk_multicore_projection_sound
    (jobs : JobId -> Job)
    (adm : admissible_cpu)
    (m : nat)
    (ex : awk_execution m) : Prop :=
  execution_multicore_projection_sound jobs adm m (awk_to_execution ex).

Lemma awk_project_schedule_eq :
  forall tr t c,
    awk_project_schedule tr t c = awk_current (tr t) c.
Proof.
  intros tr t c.
  reflexivity.
Qed.

Lemma awk_projected_running_iff :
  forall m tr j t,
    awk_projected_running m tr j t <->
    exists c, c < m /\ awk_current (tr t) c = Some j.
Proof.
  intros m tr j t.
  unfold awk_projected_running, awk_to_op_trace.
  rewrite projected_running_iff_current.
  tauto.
Qed.

Lemma awk_trace_sound_implies_valid_schedule :
  forall jobs m ex,
    awk_trace_sound jobs m ex ->
    valid_schedule jobs m (awk_project_schedule (awk_ex_trace ex)).
Proof.
  intros jobs m ex Hsound.
  unfold awk_trace_sound in Hsound.
  change (valid_schedule jobs m
            (project_schedule (ex_trace (awk_to_execution ex)))).
  apply execution_projection_sound_implies_valid_schedule.
  exact Hsound.
Qed.

Lemma awk_multicore_projection_sound_implies_semantic_validity :
  forall jobs adm m ex,
    awk_multicore_projection_sound jobs adm m ex ->
    multicore_semantic_validity jobs m (awk_project_schedule (awk_ex_trace ex)).
Proof.
  intros jobs adm m ex Hsound.
  unfold awk_multicore_projection_sound in Hsound.
  change (multicore_semantic_validity jobs m
            (project_schedule (ex_trace (awk_to_execution ex)))).
  eapply execution_multicore_projection_sound_implies_semantic_validity.
  exact Hsound.
Qed.

Lemma awk_multicore_projection_sound_implies_placement :
  forall jobs adm m ex,
    awk_multicore_projection_sound jobs adm m ex ->
    schedule_respects_admissibility adm m (awk_project_schedule (awk_ex_trace ex)).
Proof.
  intros jobs adm m ex Hsound.
  unfold awk_multicore_projection_sound in Hsound.
  change (schedule_respects_admissibility adm m
            (project_schedule (ex_trace (awk_to_execution ex)))).
  eapply execution_multicore_projection_sound_implies_placement.
  exact Hsound.
Qed.

Lemma awk_local_adapter_contract_implies_valid_schedule :
  forall (P : OSLabeledProjection AwkernelState) jobs adm m
         (C : awk_local_adapter_contract P jobs adm m),
    valid_schedule
      jobs
      m
      (project_schedule
         (lex_trace (concrete_to_labeled_execution (olac_execution C)))).
Proof.
  intros P jobs adm m C.
  apply os_local_multicore_adapter_contract_implies_valid_schedule.
Qed.

Lemma awk_local_adapter_contract_implies_semantic_validity :
  forall (P : OSLabeledProjection AwkernelState) jobs adm m
         (C : awk_local_adapter_contract P jobs adm m),
    multicore_semantic_validity
      jobs
      m
      (project_schedule
         (lex_trace (concrete_to_labeled_execution (olac_execution C)))).
Proof.
  intros P jobs adm m C.
  apply os_local_multicore_adapter_contract_implies_semantic_validity.
Qed.

Lemma awk_local_adapter_contract_implies_placement :
  forall (P : OSLabeledProjection AwkernelState) jobs adm m
         (C : awk_local_adapter_contract P jobs adm m),
    schedule_respects_admissibility
      adm
      m
      (project_schedule
         (lex_trace (concrete_to_labeled_execution (olac_execution C)))).
Proof.
  intros P jobs adm m C.
  apply os_local_multicore_adapter_contract_implies_placement.
Qed.

Lemma awk_local_adapter_contract_handle_sets_need_resched :
  forall (P : OSLabeledProjection AwkernelState) jobs adm m
         (C : awk_local_adapter_contract P jobs adm m) t c,
    c < m ->
    os_step_label P (lce_trace (olac_execution C) t)
      (lce_trace (olac_execution C) (S t)) = EvHandleResched c ->
    op_need_resched
      (os_to_op_state (osl_to_os_projection P) (lce_trace (olac_execution C) (S t)))
      c = true.
Proof.
  intros P jobs adm m C t c Hlt Hhandle.
  eapply os_local_multicore_adapter_contract_handle_sets_need_resched.
  - exact Hlt.
  - exact Hhandle.
Qed.

Lemma awk_local_adapter_contract_choose_sets_dispatch_target :
  forall (P : OSLabeledProjection AwkernelState) jobs adm m
         (C : awk_local_adapter_contract P jobs adm m) t c j,
    c < m ->
    os_step_label P (lce_trace (olac_execution C) t)
      (lce_trace (olac_execution C) (S t)) = EvChoose c j ->
    op_dispatch_target
      (os_to_op_state (osl_to_os_projection P) (lce_trace (olac_execution C) (S t)))
      c = Some j.
Proof.
  intros P jobs adm m C t c j Hlt Hchoose.
  eapply os_local_multicore_adapter_contract_choose_sets_dispatch_target.
  - exact Hlt.
  - exact Hchoose.
Qed.

Lemma awk_local_adapter_contract_dispatch_clears_need_resched :
  forall (P : OSLabeledProjection AwkernelState) jobs adm m
         (C : awk_local_adapter_contract P jobs adm m) t c j,
    c < m ->
    os_step_label P (lce_trace (olac_execution C) t)
      (lce_trace (olac_execution C) (S t)) = EvDispatch c j ->
    op_need_resched
      (os_to_op_state (osl_to_os_projection P) (lce_trace (olac_execution C) (S t)))
      c = false.
Proof.
  intros P jobs adm m C t c j Hlt Hdispatch.
  eapply os_local_multicore_adapter_contract_dispatch_clears_need_resched.
  - exact Hlt.
  - exact Hdispatch.
Qed.

Lemma awk_local_adapter_contract_block_clears_dispatch_target :
  forall (P : OSLabeledProjection AwkernelState) jobs adm m
         (C : awk_local_adapter_contract P jobs adm m) t c j,
    c < m ->
    os_step_label P (lce_trace (olac_execution C) t)
      (lce_trace (olac_execution C) (S t)) = EvBlock j ->
    op_dispatch_target
      (os_to_op_state (osl_to_os_projection P) (lce_trace (olac_execution C) (S t)))
      c <> Some j.
Proof.
  intros P jobs adm m C t c j Hlt Hblock.
  eapply os_local_multicore_adapter_contract_block_clears_dispatch_target.
  - exact Hlt.
  - exact Hblock.
Qed.
