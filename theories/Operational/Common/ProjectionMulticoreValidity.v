From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Multicore.Common.MultiCoreBase.
From RocqSched Require Import Multicore.Common.Admissibility.
From RocqSched Require Import Multicore.Common.PlacementFacts.
From RocqSched Require Import Multicore.Common.ValidityFacts.
From RocqSched Require Import Operational.Common.Trace.
From RocqSched Require Import Operational.Common.Projection.
From RocqSched Require Import Operational.Common.Execution.
From RocqSched Require Import Operational.Common.LabeledExecution.
From RocqSched Require Import Operational.Common.ProjectionLemmas.
From RocqSched Require Import Operational.Common.ProjectionInvariants.

Lemma op_idle_outside_range_projected :
  forall m tr,
    (forall t, op_idle_outside_range m (tr t)) ->
    forall t c,
      m <= c ->
      project_schedule tr t c = None.
Proof.
  intros m tr Hid t c Hge.
  unfold project_schedule.
  exact (Hid t c Hge).
Qed.

Lemma op_respects_admissibility_projected :
  forall adm m tr,
    (forall t, op_respects_admissibility adm m (tr t)) ->
    schedule_respects_admissibility adm m (project_schedule tr).
Proof.
  intros adm m tr Hadm j t c Hlt Hrun.
  unfold project_schedule in Hrun.
  eapply Hadm; eauto.
Qed.

Lemma projectable_trace_implies_projected_no_duplication :
  forall jobs m tr,
    projectable_trace jobs m tr ->
    no_duplication m (project_schedule tr).
Proof.
  intros jobs m tr Hproj.
  apply op_no_duplication_implies_projected_no_duplication.
  intro t.
  exact (pt_no_dup _ _ _ Hproj t).
Qed.

Lemma projectable_trace_with_range_implies_multicore_semantic_validity :
  forall jobs m tr,
    projectable_trace jobs m tr ->
    (forall t, op_idle_outside_range m (tr t)) ->
    multicore_semantic_validity jobs m (project_schedule tr).
Proof.
  intros jobs m tr Hproj Hrange.
  constructor.
  - apply projectable_trace_implies_valid_schedule.
    exact Hproj.
  - apply projectable_trace_implies_projected_no_duplication with (jobs := jobs).
    exact Hproj.
  - apply op_idle_outside_range_projected.
    exact Hrange.
  - intros j t Hrunning.
    unfold running_set_at in Hrunning.
    destruct Hrunning as [c [Hlt Hrun]].
    eapply projected_slot_eligible; eauto.
Qed.

Lemma projectable_trace_with_multicore_inv_implies_multicore_semantic_validity :
  forall jobs adm m tr,
    projectable_trace jobs m tr ->
    (forall t, op_multicore_projection_inv adm m (tr t)) ->
    multicore_semantic_validity jobs m (project_schedule tr) /\
    schedule_respects_admissibility adm m (project_schedule tr).
Proof.
  intros jobs adm m tr Hproj Hinv.
  split.
  - apply projectable_trace_with_range_implies_multicore_semantic_validity; auto.
    intro t.
    exact (ompi_idle_outside _ _ _ (Hinv t)).
  - apply op_respects_admissibility_projected.
    intro t.
    exact (ompi_placement _ _ _ (Hinv t)).
Qed.

Record execution_multicore_projection_sound
    (jobs : JobId -> Job)
    (adm : admissible_cpu)
    (m : nat)
    (ex : execution m) : Prop := {
  emps_projection_sound :
    execution_projection_sound jobs m ex;
  emps_idle_outside :
    forall t, op_idle_outside_range m (ex_trace ex t);
  emps_placement :
    forall t, op_respects_admissibility adm m (ex_trace ex t)
}.

Record labeled_execution_multicore_projection_sound
    (jobs : JobId -> Job)
    (adm : admissible_cpu)
    (m : nat)
    (ex : labeled_execution m) : Prop := {
  lemps_projection_sound :
    labeled_execution_projection_sound jobs m ex;
  lemps_idle_outside :
    forall t, op_idle_outside_range m (lex_trace ex t);
  lemps_placement :
    forall t, op_respects_admissibility adm m (lex_trace ex t)
}.

Lemma execution_multicore_projection_sound_implies_semantic_validity :
  forall jobs adm m ex,
    execution_multicore_projection_sound jobs adm m ex ->
    multicore_semantic_validity jobs m (project_schedule (ex_trace ex)).
Proof.
  intros jobs adm m ex Hsound.
  eapply projectable_trace_with_range_implies_multicore_semantic_validity.
  - apply execution_projection_sound_implies_projectable.
    exact (emps_projection_sound _ _ _ _ Hsound).
  - exact (emps_idle_outside _ _ _ _ Hsound).
Qed.

Lemma execution_multicore_projection_sound_implies_placement :
  forall jobs adm m ex,
    execution_multicore_projection_sound jobs adm m ex ->
    schedule_respects_admissibility adm m (project_schedule (ex_trace ex)).
Proof.
  intros jobs adm m ex Hsound.
  apply op_respects_admissibility_projected.
  exact (emps_placement _ _ _ _ Hsound).
Qed.

Lemma labeled_execution_multicore_projection_sound_to_execution :
  forall jobs adm m (ex : labeled_execution m),
    labeled_execution_multicore_projection_sound jobs adm m ex ->
    execution_multicore_projection_sound jobs adm m (labeled_to_execution ex).
Proof.
  intros jobs adm m ex Hsound.
  constructor.
  - apply labeled_execution_projection_sound_to_execution.
    exact (lemps_projection_sound _ _ _ _ Hsound).
  - exact (lemps_idle_outside _ _ _ _ Hsound).
  - exact (lemps_placement _ _ _ _ Hsound).
Qed.

Lemma labeled_execution_multicore_projection_sound_implies_semantic_validity :
  forall jobs adm m (ex : labeled_execution m),
    labeled_execution_multicore_projection_sound jobs adm m ex ->
    multicore_semantic_validity jobs m (project_schedule (lex_trace ex)).
Proof.
  intros jobs adm m ex Hsound.
  change
    (multicore_semantic_validity
       jobs m (project_schedule (ex_trace (labeled_to_execution ex)))).
  apply execution_multicore_projection_sound_implies_semantic_validity
    with (adm := adm).
  apply labeled_execution_multicore_projection_sound_to_execution.
  exact Hsound.
Qed.

Lemma labeled_execution_multicore_projection_sound_implies_placement :
  forall jobs adm m (ex : labeled_execution m),
    labeled_execution_multicore_projection_sound jobs adm m ex ->
    schedule_respects_admissibility adm m (project_schedule (lex_trace ex)).
Proof.
  intros jobs adm m ex Hsound.
  change
    (schedule_respects_admissibility
       adm m (project_schedule (ex_trace (labeled_to_execution ex)))).
  eapply execution_multicore_projection_sound_implies_placement
    with (jobs := jobs).
  apply labeled_execution_multicore_projection_sound_to_execution.
  exact Hsound.
Qed.
