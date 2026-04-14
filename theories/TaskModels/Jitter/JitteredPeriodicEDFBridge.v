From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.EnumCandidates.
From RocqSched Require Import Uniprocessor.Policies.EDF.
From RocqSched Require Import Uniprocessor.Policies.EDFOptimality.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicFiniteHorizon.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicEnumeration.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicFiniteOptimalityLift.
Import ListNotations.

Theorem jittered_periodic_edf_optimality_on_finite_horizon :
  forall T T_bool tasks offset jitter H jobs
         (w : JitteredPeriodicFiniteHorizonWitness T tasks offset jitter jobs H),
    (forall τ, T_bool τ = true <-> T τ) ->
    feasible_on (jittered_periodic_jobset_upto T tasks offset jitter jobs H) jobs 1 ->
    schedulable_by_on
      (jittered_periodic_jobset_upto T tasks offset jitter jobs H)
      (edf_scheduler
         (enum_candidates_of (jittered_enumJ T tasks offset jitter jobs H w)))
      jobs 1.
Proof.
  intros T T_bool tasks offset jitter H jobs w HTbool Hfeas.
  exact (jittered_periodic_finite_optimality_lift_with_witness edf_scheduler
    (fun J J_bool enumJ' cands cand_spec jobs' Hb Hc Hs Hf =>
      edf_optimality_on_finite_jobs J J_bool enumJ' cands cand_spec jobs' Hb Hc Hs Hf)
    T T_bool tasks offset jitter H jobs w HTbool Hfeas).
Qed.

