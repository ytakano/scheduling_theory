From Stdlib Require Import List.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Multicore.Partitioned.Partitioned.
From RocqSched Require Import Multicore.Partitioned.Policies.PartitionedFiniteOptimalityLift.
From RocqSched Require Import TaskModels.Common.FiniteHorizonWitness.
From RocqSched Require Import TaskModels.Common.WitnessCandidates.
Import ListNotations.

Theorem witness_finite_optimality_lift :
  forall (local_scheduler : CandidateSource -> Scheduler)
         (Hoptimal : forall J (J_bool : JobId -> bool) enumJ
                            (cands : CandidateSource)
                            (cand_spec : CandidateSourceSpec J cands) jobs,
                       (forall x, J_bool x = true <-> J x) ->
                       (forall j, J j -> In j enumJ) ->
                       (forall j, In j enumJ -> J j) ->
                       feasible_on J jobs 1 ->
                       schedulable_by_on J (local_scheduler cands) jobs 1)
         (J : JobId -> Prop)
         (J_bool : JobId -> bool)
         jobs
         (w : FiniteHorizonWitness J),
    (forall x, J_bool x = true <-> J x) ->
    feasible_on J jobs 1 ->
    schedulable_by_on
      J
      (local_scheduler (witness_candidates_of J w))
      jobs 1.
Proof.
  intros local_scheduler Hoptimal J J_bool jobs w HJbool Hfeas.
  apply (Hoptimal
    J J_bool
    (witness_enumJ J w)
    (witness_candidates_of J w)
    (witness_candidates_spec J w)
    jobs).
  - exact HJbool.
  - exact (witness_enum_complete J w).
  - exact (witness_enum_sound J w).
  - exact Hfeas.
Qed.

Theorem partitioned_witness_finite_optimality_lift :
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
           (J : JobId -> Prop)
           (J_bool : JobId -> bool)
           jobs
           (w : FiniteHorizonWitness J),
      (forall x, J_bool x = true <-> J x) ->
      (forall c, c < m ->
         feasible_on (local_jobset assign J c) jobs 1) ->
      schedulable_by_on
        J
        (partitioned_scheduler m spec
           (enum_local_candidates_of assign (witness_enumJ J w)))
        jobs m.
Proof.
  intros local_scheduler spec Hscheduler Hoptimal
         assign m valid_assignment J J_bool jobs w
         HJbool Hlocal_feasible.
  apply (partitioned_finite_optimality_lift local_scheduler spec Hscheduler Hoptimal
           assign m valid_assignment J J_bool (witness_enumJ J w) jobs).
  - exact HJbool.
  - exact (witness_enum_complete J w).
  - exact (witness_enum_sound J w).
  - exact Hlocal_feasible.
Qed.
