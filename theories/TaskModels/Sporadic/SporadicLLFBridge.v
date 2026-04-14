From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.EnumCandidates.
From RocqSched Require Import Uniprocessor.Policies.LLF.
From RocqSched Require Import Uniprocessor.Policies.LLFOptimality.
From RocqSched Require Import TaskModels.Sporadic.SporadicTasks.
From RocqSched Require Import TaskModels.Sporadic.SporadicFiniteHorizon.
From RocqSched Require Import TaskModels.Sporadic.SporadicEnumeration.
From RocqSched Require Import TaskModels.Sporadic.SporadicWitnessCandidates.
From RocqSched Require Import TaskModels.Sporadic.SporadicFiniteOptimalityLift.
Import ListNotations.

Theorem sporadic_llf_optimality_on_finite_horizon :
  forall T T_bool tasks H jobs
         (w : SporadicFiniteHorizonWitness T tasks jobs H),
    (forall τ, T_bool τ = true <-> T τ) ->
    feasible_on (sporadic_jobset_upto T tasks jobs H) jobs 1 ->
    schedulable_by_on
      (sporadic_jobset_upto T tasks jobs H)
      (llf_scheduler (sporadic_witness_candidates_of T tasks jobs H w))
      jobs 1.
Proof.
  intros T T_bool tasks H jobs w HTbool Hfeas.
  exact (sporadic_finite_optimality_lift_with_witness llf_scheduler
    (fun J J_bool enumJ' cands cand_spec jobs' Hb Hc Hs Hf =>
      llf_optimality_on_finite_jobs J J_bool enumJ' cands cand_spec jobs' Hb Hc Hs Hf)
    T T_bool tasks H jobs w HTbool Hfeas).
Qed.
