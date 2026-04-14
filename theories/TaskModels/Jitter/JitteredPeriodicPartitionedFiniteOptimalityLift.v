From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.EnumCandidates.
From RocqSched Require Import Multicore.Partitioned.Partitioned.
From RocqSched Require Import Multicore.Partitioned.Policies.PartitionedFiniteOptimalityLift.
From RocqSched Require Import TaskModels.Common.FiniteHorizonWitness.
From RocqSched Require Import TaskModels.Common.WitnessFiniteOptimalityLift.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicFiniteHorizon.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicEnumeration.
Import ListNotations.

Theorem partitioned_jittered_periodic_finite_optimality_lift :
  forall (local_scheduler : CandidateSource -> Scheduler)
         (spec : GenericSchedulingAlgorithm),
    (forall cands,
       local_scheduler cands = single_cpu_algorithm_schedule spec cands) ->
    (forall J (J_bool : JobId -> bool) enumJ
           (cands : CandidateSource)
           (cand_spec : CandidateSourceSpec J cands) jobs,
       (forall x, J_bool x = true <-> J x) ->
       (forall j, J j -> In j enumJ) ->
       (forall j, In j enumJ -> J j) ->
       feasible_on J jobs 1 ->
       schedulable_by_on J (local_scheduler cands) jobs 1) ->
    forall (assign : JobId -> CPU) (m : nat)
           (valid_assignment : forall j, assign j < m)
           T T_bool tasks offset jitter H enumJ jobs,
      (forall τ, T_bool τ = true <-> T τ) ->
      (forall j, jittered_periodic_jobset_upto T tasks offset jitter jobs H j -> In j enumJ) ->
      (forall j, In j enumJ -> jittered_periodic_jobset_upto T tasks offset jitter jobs H j) ->
      (forall c, c < m ->
         feasible_on
           (local_jobset assign
              (jittered_periodic_jobset_upto T tasks offset jitter jobs H) c)
           jobs 1) ->
      schedulable_by_on
        (jittered_periodic_jobset_upto T tasks offset jitter jobs H)
        (partitioned_scheduler m spec (enum_local_candidates_of assign enumJ))
        jobs m.
Proof.
  intros local_scheduler spec Hscheduler Hoptimal
         assign m valid_assignment T T_bool tasks offset jitter H enumJ jobs
         HTbool Henum_complete Henum_sound Hlocal_feasible.
  apply (partitioned_finite_optimality_lift local_scheduler spec Hscheduler Hoptimal
           assign m valid_assignment
           (jittered_periodic_jobset_upto T tasks offset jitter jobs H)
           (jittered_periodic_jobset_upto_bool T_bool tasks offset jitter jobs H)
           enumJ jobs).
  - intros j.
    exact (jittered_periodic_jobset_upto_bool_spec
      T T_bool tasks offset jitter jobs H HTbool j).
  - exact Henum_complete.
  - exact Henum_sound.
  - exact Hlocal_feasible.
Qed.

Theorem partitioned_jittered_periodic_finite_optimality_lift_with_witness :
  forall (local_scheduler : CandidateSource -> Scheduler)
         (spec : GenericSchedulingAlgorithm),
    (forall cands,
       local_scheduler cands = single_cpu_algorithm_schedule spec cands) ->
    (forall J (J_bool : JobId -> bool) enumJ
           (cands : CandidateSource)
           (cand_spec : CandidateSourceSpec J cands) jobs,
       (forall x, J_bool x = true <-> J x) ->
       (forall j, J j -> In j enumJ) ->
       (forall j, In j enumJ -> J j) ->
       feasible_on J jobs 1 ->
       schedulable_by_on J (local_scheduler cands) jobs 1) ->
    forall (assign : JobId -> CPU) (m : nat)
           (valid_assignment : forall j, assign j < m)
           T T_bool tasks offset jitter H jobs
           (w : FiniteHorizonWitness
                  (jittered_periodic_jobset_upto T tasks offset jitter jobs H)),
      (forall τ, T_bool τ = true <-> T τ) ->
      (forall c, c < m ->
         feasible_on
           (local_jobset assign
              (jittered_periodic_jobset_upto T tasks offset jitter jobs H) c)
           jobs 1) ->
      schedulable_by_on
        (jittered_periodic_jobset_upto T tasks offset jitter jobs H)
        (partitioned_scheduler m spec
           (enum_local_candidates_of assign
              (witness_enumJ
                 (jittered_periodic_jobset_upto T tasks offset jitter jobs H) w)))
        jobs m.
Proof.
  intros local_scheduler spec Hscheduler Hoptimal
         assign m valid_assignment T T_bool tasks offset jitter H jobs w
         HTbool Hlocal_feasible.
  exact (partitioned_witness_finite_optimality_lift
    local_scheduler spec
    Hscheduler Hoptimal
    assign m valid_assignment
    (jittered_periodic_jobset_upto T tasks offset jitter jobs H)
    (jittered_periodic_jobset_upto_bool T_bool tasks offset jitter jobs H)
    jobs
    w
    (fun j =>
       jittered_periodic_jobset_upto_bool_spec
         T T_bool tasks offset jitter jobs H HTbool j)
    Hlocal_feasible).
Qed.
