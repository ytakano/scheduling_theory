From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.EnumCandidates.
From RocqSched Require Import TaskModels.Common.FiniteHorizonWitness.
From RocqSched Require Import TaskModels.Common.WitnessCandidates.
From RocqSched Require Import TaskModels.Common.WitnessFiniteOptimalityLift.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicFiniteHorizon.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicEnumeration.
Import ListNotations.

Theorem jittered_periodic_finite_optimality_lift :
  forall (local_scheduler : CandidateSource -> Scheduler)
         (Hoptimal : forall J (J_bool : JobId -> bool) enumJ
                            (cands : CandidateSource)
                            (cand_spec : CandidateSourceSpec J cands) jobs,
                       (forall x, J_bool x = true <-> J x) ->
                       (forall j, J j -> In j enumJ) ->
                       (forall j, In j enumJ -> J j) ->
                       feasible_on J jobs 1 ->
                       schedulable_by_on J (local_scheduler cands) jobs 1)
         T T_bool tasks offset jitter H enumJ jobs,
    (forall τ, T_bool τ = true <-> T τ) ->
    (forall j, jittered_periodic_jobset_upto T tasks offset jitter jobs H j -> In j enumJ) ->
    (forall j, In j enumJ -> jittered_periodic_jobset_upto T tasks offset jitter jobs H j) ->
    feasible_on (jittered_periodic_jobset_upto T tasks offset jitter jobs H) jobs 1 ->
    schedulable_by_on
      (jittered_periodic_jobset_upto T tasks offset jitter jobs H)
      (local_scheduler (enum_candidates_of enumJ))
      jobs 1.
Proof.
  intros local_scheduler Hoptimal T T_bool tasks offset jitter H enumJ jobs
         HTbool Henum_complete Henum_sound Hfeas.
  apply (Hoptimal
    (jittered_periodic_jobset_upto T tasks offset jitter jobs H)
    (jittered_periodic_jobset_upto_bool T_bool tasks offset jitter jobs H)
    enumJ
    (enum_candidates_of enumJ)
    (enum_candidates_spec
       (jittered_periodic_jobset_upto T tasks offset jitter jobs H)
       enumJ
       Henum_complete
       Henum_sound)
    jobs).
  - intros j.
    exact (jittered_periodic_jobset_upto_bool_spec
      T T_bool tasks offset jitter jobs H HTbool j).
  - exact Henum_complete.
  - exact Henum_sound.
  - exact Hfeas.
Qed.

Theorem jittered_periodic_finite_optimality_lift_with_witness :
  forall (local_scheduler : CandidateSource -> Scheduler)
         (Hoptimal : forall J (J_bool : JobId -> bool) enumJ
                            (cands : CandidateSource)
                            (cand_spec : CandidateSourceSpec J cands) jobs,
                       (forall x, J_bool x = true <-> J x) ->
                       (forall j, J j -> In j enumJ) ->
                       (forall j, In j enumJ -> J j) ->
                       feasible_on J jobs 1 ->
                       schedulable_by_on J (local_scheduler cands) jobs 1)
         T T_bool tasks offset jitter H jobs
         (w : FiniteHorizonWitness
                (jittered_periodic_jobset_upto T tasks offset jitter jobs H)),
    (forall τ, T_bool τ = true <-> T τ) ->
    feasible_on (jittered_periodic_jobset_upto T tasks offset jitter jobs H) jobs 1 ->
    schedulable_by_on
      (jittered_periodic_jobset_upto T tasks offset jitter jobs H)
      (local_scheduler
         (witness_candidates_of
            (jittered_periodic_jobset_upto T tasks offset jitter jobs H) w))
      jobs 1.
Proof.
  intros local_scheduler Hoptimal T T_bool tasks offset jitter H jobs w HTbool Hfeas.
  exact (witness_finite_optimality_lift
    local_scheduler
    Hoptimal
    (jittered_periodic_jobset_upto T tasks offset jitter jobs H)
    (jittered_periodic_jobset_upto_bool T_bool tasks offset jitter jobs H)
    jobs
    w
    (fun j =>
       jittered_periodic_jobset_upto_bool_spec
         T T_bool tasks offset jitter jobs H HTbool j)
    Hfeas).
Qed.
