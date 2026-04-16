From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Multicore.Common.MultiCoreBase.
From RocqSched Require Import Operational.Common.State.
From RocqSched Require Import Operational.Common.Trace.
From RocqSched Require Import Operational.Common.Projection.
From RocqSched Require Import Operational.Common.Invariants.
From RocqSched Require Import Operational.Common.Execution.

Record projectable_trace
    (jobs : JobId -> Job) (m : nat) (tr : OpTrace) : Prop := mkProjectableTrace {
  pt_no_dup :
    forall t, op_no_duplication m (tr t);
  pt_released :
    forall t c j,
      c < m ->
      op_current (tr t) c = Some j ->
      released jobs j t;
  pt_not_completed :
    forall t c j,
      c < m ->
      op_current (tr t) c = Some j ->
      ~ completed jobs m (project_schedule tr) j t;
}.

Record execution_projection_sound
    (jobs : JobId -> Job) (m : nat) (ex : execution m) : Prop :=
  mkExecutionProjectionSound {
    eps_release_sound :
      forall t c j,
        c < m ->
        op_current (ex_trace ex t) c = Some j ->
        released jobs j t;
    eps_completion_sound :
      forall t c j,
        c < m ->
        op_current (ex_trace ex t) c = Some j ->
        ~ completed jobs m (project_schedule (ex_trace ex)) j t;
  }.

Lemma current_implies_projected_running :
  forall m tr t c j,
    c < m ->
    op_current (tr t) c = Some j ->
    projected_running m tr j t.
Proof.
  intros m tr t c j Hlt Hcur.
  unfold projected_running, running, project_schedule.
  exists c. split; assumption.
Qed.

Lemma projected_running_implies_some_current :
  forall m tr j t,
    projected_running m tr j t ->
    exists c, c < m /\ op_current (tr t) c = Some j.
Proof.
  intros m tr j t.
  apply projected_running_iff_current.
Qed.

Lemma op_no_duplication_implies_projected_no_duplication :
  forall m tr,
    (forall t, op_no_duplication m (tr t)) ->
    no_duplication m (project_schedule tr).
Proof.
  intros m tr Hdup.
  unfold no_duplication, sequential_jobs, project_schedule.
  intros j t c1 c2 Hlt1 Hlt2 Hrun1 Hrun2.
  eapply Hdup; eauto.
Qed.

Lemma projected_slot_eligible :
  forall jobs m tr t c j,
    projectable_trace jobs m tr ->
    c < m ->
    project_schedule tr t c = Some j ->
    eligible jobs m (project_schedule tr) j t.
Proof.
  intros jobs m tr t c j Hproj Hlt Hrun.
  split.
  - eapply pt_released; eauto.
  - eapply pt_not_completed; eauto.
Qed.

Lemma execution_projection_sound_implies_projectable :
  forall jobs m ex,
    execution_projection_sound jobs m ex ->
    projectable_trace jobs m (ex_trace ex).
Proof.
  intros jobs m ex Hsound.
  refine (mkProjectableTrace jobs m (ex_trace ex) _ _ _).
  - intros t.
    exact (osi_no_dup _ _ (ex_struct_inv ex t)).
  - intros t c j Hlt Hrun.
    exact (eps_release_sound _ _ _ Hsound t c j Hlt Hrun).
  - intros t c j Hlt Hrun.
    exact (eps_completion_sound _ _ _ Hsound t c j Hlt Hrun).
Qed.

Lemma execution_projection_sound_implies_valid_schedule :
  forall jobs m ex,
    execution_projection_sound jobs m ex ->
    valid_schedule jobs m (project_schedule (ex_trace ex)).
Proof.
  intros jobs m ex Hsound j t c Hlt Hrun.
  split.
  - exact (eps_release_sound _ _ _ Hsound t c j Hlt Hrun).
  - exact (eps_completion_sound _ _ _ Hsound t c j Hlt Hrun).
Qed.

Lemma projectable_trace_implies_valid_schedule :
  forall jobs m tr,
    projectable_trace jobs m tr ->
    valid_schedule jobs m (project_schedule tr).
Proof.
  intros jobs m tr Hproj j t c Hlt Hrun.
  eapply projected_slot_eligible; eauto.
Qed.
