From Stdlib Require Import List Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Semantics.ScheduleLemmas.ScheduleFacts.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.TopMInterface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.TopMSchedulerBridge.
From RocqSched Require Import Multicore.Common.MultiCoreBase.
From RocqSched Require Import Multicore.Common.ValidityFacts.
From RocqSched Require Import Operational.Common.Execution.
From RocqSched Require Import Operational.Common.Projection.
From RocqSched Require Import Operational.Common.LabeledExecution.
From RocqSched Require Import Operational.Common.DelayModel.
From RocqSched Require Import Operational.Common.DelayBudget.
From RocqSched Require Import Operational.Common.ProjectionMulticoreValidity.
Import ListNotations.

Definition service_lag_le
    (m : nat) (ideal actual : Schedule) (delta : nat) : Prop :=
  forall j t,
    service_job m ideal j t <=
    service_job m actual j (t + delta).

Definition service_distance_le
    (m : nat) (s1 s2 : Schedule) (delta : nat) : Prop :=
  service_lag_le m s1 s2 delta /\
  service_lag_le m s2 s1 delta.

Lemma service_lag_le_refl :
  forall m sched,
    service_lag_le m sched sched 0.
Proof.
  intros m sched j t.
  replace (t + 0) with t by lia.
  lia.
Qed.

Lemma service_lag_le_monotone_delta :
  forall m ideal actual delta1 delta2,
    delta1 <= delta2 ->
    service_lag_le m ideal actual delta1 ->
    service_lag_le m ideal actual delta2.
Proof.
  intros m ideal actual delta1 delta2 Hle Hlag j t.
  pose proof (Hlag j t) as Hbase.
  eapply Nat.le_trans.
  - exact Hbase.
  - apply service_job_monotone.
    lia.
Qed.

Lemma service_lag_monotone_delta :
  forall m ideal actual d1 d2,
    service_lag_le m ideal actual d1 ->
    d1 <= d2 ->
    service_lag_le m ideal actual d2.
Proof.
  intros m ideal actual d1 d2 Hlag Hle.
  eapply service_lag_le_monotone_delta; eauto.
Qed.

Lemma service_distance_zero_implies_service_eq :
  forall m s1 s2,
    service_distance_le m s1 s2 0 ->
    forall j t,
      service_job m s1 j t = service_job m s2 j t.
Proof.
  intros m s1 s2 [H12 H21] j t.
  specialize (H12 j t).
  specialize (H21 j t).
  replace (t + 0) with t in H12 by lia.
  replace (t + 0) with t in H21 by lia.
  lia.
Qed.

Definition labeled_actual_schedule
    {m : nat} (ex : labeled_execution m) : Schedule :=
  project_schedule (lex_trace ex).

Record bounded_delay_projection_refinement
    (jobs : JobId -> Job)
    (adm : admissible_cpu)
    (m : nat)
    (ex : labeled_execution m)
    (ideal : Schedule)
    (delay_bounds : op_delay_bounds)
    (delay_sources : DelayTrace)
    (delta : nat) : Prop :=
  mkBoundedDelayProjectionRefinement {
    bdpr_actual_sound :
      execution_multicore_projection_sound
        jobs adm m (labeled_to_execution ex);
    bdpr_ideal_valid :
      multicore_semantic_validity jobs m ideal;
    bdpr_default_sources_covered :
      forall t src,
        In src (default_event_delay_sources (lex_event ex t)) ->
        In src (delay_sources t);
    bdpr_budget_within_delta :
      forall t,
        delay_budget_le delay_bounds delay_sources 0 t delta;
    bdpr_service_lag :
      service_lag_le
        m
        ideal
        (labeled_actual_schedule ex)
        delta;
  }.

Record bounded_delay_top_m_projection_refinement
    (spec : GenericTopMSchedulingAlgorithm)
    (candidates_of : CandidateSource)
    (jobs : JobId -> Job)
    (adm : admissible_cpu)
    (m : nat)
    (ex : labeled_execution m)
    (ideal : Schedule)
    (delay_bounds : op_delay_bounds)
    (delay_sources : DelayTrace)
    (delta : nat) : Prop :=
  mkBoundedDelayTopMProjectionRefinement {
    bdtmpr_actual_sound :
      execution_multicore_projection_sound
        jobs adm m (labeled_to_execution ex);
    bdtmpr_ideal_top_m :
      scheduler_rel
        (top_m_algorithm_schedule spec candidates_of)
        jobs m ideal;
    bdtmpr_default_sources_covered :
      forall t src,
        In src (default_event_delay_sources (lex_event ex t)) ->
        In src (delay_sources t);
    bdtmpr_budget_within_delta :
      forall t,
        delay_budget_le delay_bounds delay_sources 0 t delta;
    bdtmpr_service_lag :
      service_lag_le
        m
        ideal
        (labeled_actual_schedule ex)
        delta;
  }.

Record bounded_delay_refinement (m : nat) : Type :=
  mkBoundedDelayRefinement {
    bdr_execution : labeled_execution m;
    bdr_ideal_schedule : Schedule;
    bdr_delay_bounds : op_delay_bounds;
    bdr_delay_sources : DelayTrace;
    bdr_delta : nat;
    bdr_default_sources_covered :
      forall t src,
        In src (default_event_delay_sources (lex_event bdr_execution t)) ->
        In src (bdr_delay_sources t);
    bdr_budget_within_delta :
      forall t,
        delay_budget_le bdr_delay_bounds bdr_delay_sources 0 t bdr_delta;
    bdr_service_lag :
      service_lag_le
        m
        bdr_ideal_schedule
        (labeled_actual_schedule bdr_execution)
        bdr_delta;
  }.

Arguments bdr_execution {m} _.
Arguments bdr_ideal_schedule {m} _.
Arguments bdr_delay_bounds {m} _.
Arguments bdr_delay_sources {m} _ _.
Arguments bdr_delta {m} _.

Lemma bounded_delay_projection_refinement_actual_semantic_validity :
  forall jobs adm m ex ideal delay_bounds delay_sources delta,
    bounded_delay_projection_refinement
      jobs adm m ex ideal delay_bounds delay_sources delta ->
    multicore_semantic_validity jobs m (labeled_actual_schedule ex).
Proof.
  intros jobs adm m ex ideal delay_bounds delay_sources delta Href.
  change
    (multicore_semantic_validity
       jobs m (project_schedule (Execution.ex_trace (labeled_to_execution ex)))).
  apply execution_multicore_projection_sound_implies_semantic_validity with (adm := adm).
  exact (bdpr_actual_sound _ _ _ _ _ _ _ _ Href).
Qed.

Lemma bounded_delay_projection_refinement_ideal_semantic_validity :
  forall jobs adm m ex ideal delay_bounds delay_sources delta,
    bounded_delay_projection_refinement
      jobs adm m ex ideal delay_bounds delay_sources delta ->
    multicore_semantic_validity jobs m ideal.
Proof.
  intros jobs adm m ex ideal delay_bounds delay_sources delta Href.
  exact (bdpr_ideal_valid _ _ _ _ _ _ _ _ Href).
Qed.

Lemma bounded_delay_projection_refinement_service_lag :
  forall jobs adm m ex ideal delay_bounds delay_sources delta,
    bounded_delay_projection_refinement
      jobs adm m ex ideal delay_bounds delay_sources delta ->
    service_lag_le m ideal (labeled_actual_schedule ex) delta.
Proof.
  intros jobs adm m ex ideal delay_bounds delay_sources delta Href.
  exact (bdpr_service_lag _ _ _ _ _ _ _ _ Href).
Qed.

Lemma bounded_delay_top_m_actual_semantic_validity :
  forall spec candidates_of jobs adm m ex ideal delay_bounds delay_sources delta,
    bounded_delay_top_m_projection_refinement
      spec candidates_of jobs adm m ex ideal delay_bounds delay_sources delta ->
    multicore_semantic_validity jobs m (labeled_actual_schedule ex).
Proof.
  intros spec candidates_of jobs adm m ex ideal delay_bounds delay_sources delta Href.
  change
    (multicore_semantic_validity
       jobs m (project_schedule (Execution.ex_trace (labeled_to_execution ex)))).
  apply execution_multicore_projection_sound_implies_semantic_validity with (adm := adm).
  exact (bdtmpr_actual_sound _ _ _ _ _ _ _ _ _ _ Href).
Qed.

Lemma bounded_delay_top_m_ideal_semantic_validity :
  forall spec candidates_of jobs adm m ex ideal delay_bounds delay_sources delta,
    bounded_delay_top_m_projection_refinement
      spec candidates_of jobs adm m ex ideal delay_bounds delay_sources delta ->
    multicore_semantic_validity jobs m ideal.
Proof.
  intros spec candidates_of jobs adm m ex ideal delay_bounds delay_sources delta Href.
  apply top_m_algorithm_semantic_validity with (spec := spec) (candidates_of := candidates_of).
  exact (bdtmpr_ideal_top_m _ _ _ _ _ _ _ _ _ _ Href).
Qed.

Lemma bounded_delay_refinement_service_lag :
  forall m (R : bounded_delay_refinement m),
    service_lag_le
      m
      (bdr_ideal_schedule R)
      (labeled_actual_schedule (bdr_execution R))
      (bdr_delta R).
Proof.
  intros m R.
  destruct R.
  simpl.
  exact bdr_service_lag0.
Qed.
