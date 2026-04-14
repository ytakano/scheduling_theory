From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.EnumCandidates.
From RocqSched Require Import Uniprocessor.Policies.EDF.
From RocqSched Require Import Uniprocessor.Policies.EDFOptimality.
From RocqSched Require Import TaskModels.Sporadic.SporadicTasks.
From RocqSched Require Import TaskModels.Sporadic.SporadicFiniteHorizon.
From RocqSched Require Import TaskModels.Sporadic.SporadicFiniteOptimalityLift.
Import ListNotations.

Theorem sporadic_edf_optimality_on_finite_horizon :
  forall T T_bool tasks H enumJ jobs,
    (forall τ, T_bool τ = true <-> T τ) ->
    (forall j, sporadic_jobset_upto T tasks jobs H j -> In j enumJ) ->
    (forall j, In j enumJ -> sporadic_jobset_upto T tasks jobs H j) ->
    feasible_on (sporadic_jobset_upto T tasks jobs H) jobs 1 ->
    schedulable_by_on
      (sporadic_jobset_upto T tasks jobs H)
      (edf_scheduler (enum_candidates_of enumJ))
      jobs 1.
Proof.
  intros T T_bool tasks H enumJ jobs HTbool Henum_complete Henum_sound Hfeas.
  exact (sporadic_finite_optimality_lift edf_scheduler
    (fun J J_bool enumJ' cands cand_spec jobs' Hb Hc Hs Hf =>
      edf_optimality_on_finite_jobs J J_bool enumJ' cands cand_spec jobs' Hb Hc Hs Hf)
    T T_bool tasks H enumJ jobs HTbool Henum_complete Henum_sound Hfeas).
Qed.
