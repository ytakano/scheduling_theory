From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.EnumCandidates.
From RocqSched Require Import Uniprocessor.Policies.EDF.
From RocqSched Require Import Uniprocessor.Policies.EDFOptimality.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Periodic.PeriodicFiniteHorizon.
From RocqSched Require Import TaskModels.Periodic.PeriodicEnumeration.
From RocqSched Require Import TaskModels.Periodic.PeriodicFiniteOptimalityLift.
From RocqSched Require Import TaskModels.Periodic.PeriodicWindowDemandBound.
From RocqSched Require Import Analysis.Uniprocessor.EDFProcessorDemand.
Import ListNotations.

Theorem periodic_edf_optimality_on_finite_horizon :
  forall T T_bool tasks offset H enumJ jobs,
    (forall τ, T_bool τ = true <-> T τ) ->
    (forall j, periodic_jobset_upto T tasks offset jobs H j -> In j enumJ) ->
    (forall j, In j enumJ -> periodic_jobset_upto T tasks offset jobs H j) ->
    feasible_on (periodic_jobset_upto T tasks offset jobs H) jobs 1 ->
    schedulable_by_on
      (periodic_jobset_upto T tasks offset jobs H)
      (edf_scheduler (enum_candidates_of enumJ))
      jobs 1.
Proof.
  intros T T_bool tasks offset H enumJ jobs HTbool Henum_complete Henum_sound Hfeas.
  exact (periodic_finite_optimality_lift edf_scheduler
    (fun J J_bool enumJ' cands cand_spec jobs' Hb Hc Hs Hf =>
      edf_optimality_on_finite_jobs J J_bool enumJ' cands cand_spec jobs' Hb Hc Hs Hf)
    T T_bool tasks offset H enumJ jobs HTbool Henum_complete Henum_sound Hfeas).
Qed.

(* Auto version: derive the job enumeration from a task list and a codec,
   eliminating the need to hand-write enumJ and its soundness/completeness proofs. *)
Theorem periodic_edf_optimality_on_finite_horizon_auto :
  forall T tasks offset H enumT jobs
         (codec : PeriodicFiniteHorizonCodec T tasks offset jobs H),
    well_formed_periodic_tasks_on T tasks ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    feasible_on (periodic_jobset_upto T tasks offset jobs H) jobs 1 ->
    schedulable_by_on
      (periodic_jobset_upto T tasks offset jobs H)
      (edf_scheduler
         (enum_candidates_of
            (enum_periodic_jobs_upto T tasks offset jobs H enumT codec)))
      jobs 1.
Proof.
  intros T tasks offset H enumT jobs codec Hwf HenumT_complete HenumT_sound Hfeas.
  exact (periodic_finite_optimality_lift_auto edf_scheduler
    (fun J J_bool enumJ' cands cand_spec jobs' Hb Hc Hs Hf =>
      edf_optimality_on_finite_jobs J J_bool enumJ' cands cand_spec jobs' Hb Hc Hs Hf)
    T tasks offset H enumT jobs codec Hwf HenumT_complete HenumT_sound Hfeas).
Qed.

Theorem periodic_edf_schedulable_by_window_dbf_on_finite_horizon :
  forall T T_bool tasks offset H enumT enumJ jobs,
    well_formed_periodic_tasks_on T tasks ->
    (forall τ, T_bool τ = true <-> T τ) ->
    (forall j, periodic_jobset_upto T tasks offset jobs H j -> In j enumJ) ->
    (forall j, In j enumJ -> periodic_jobset_upto T tasks offset jobs H j) ->
    (forall t1 t2,
      t1 <= t2 ->
      t2 <= H ->
      taskset_periodic_dbf_window tasks offset enumT t1 t2 <= t2 - t1) ->
    schedulable_by_on
      (periodic_jobset_upto T tasks offset jobs H)
      (edf_scheduler (enum_candidates_of enumJ))
      jobs 1.
Proof.
  intros T T_bool tasks offset H enumT enumJ jobs
         Hwf HTbool Henum_complete Henum_sound Hdbf.
  apply periodic_edf_optimality_on_finite_horizon
    with (T_bool := T_bool) (enumJ := enumJ).
  - exact HTbool.
  - exact Henum_complete.
  - exact Henum_sound.
  - exact (periodic_window_dbf_implies_edf_feasible_on_finite_horizon
             T tasks offset H enumT jobs Hwf Hdbf).
Qed.

Theorem periodic_edf_schedulable_by_window_dbf_on_finite_horizon_auto :
  forall T tasks offset H enumT jobs
         (codec : PeriodicFiniteHorizonCodec T tasks offset jobs H),
    well_formed_periodic_tasks_on T tasks ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    (forall t1 t2,
      t1 <= t2 ->
      t2 <= H ->
      taskset_periodic_dbf_window tasks offset enumT t1 t2 <= t2 - t1) ->
    schedulable_by_on
      (periodic_jobset_upto T tasks offset jobs H)
      (edf_scheduler
         (enum_candidates_of
            (enum_periodic_jobs_upto T tasks offset jobs H enumT codec)))
      jobs 1.
Proof.
  intros T tasks offset H enumT jobs codec
         Hwf HenumT_complete HenumT_sound Hdbf.
  apply periodic_edf_optimality_on_finite_horizon_auto.
  - exact Hwf.
  - exact HenumT_complete.
  - exact HenumT_sound.
  - exact (periodic_window_dbf_implies_edf_feasible_on_finite_horizon
             T tasks offset H enumT jobs Hwf Hdbf).
Qed.
