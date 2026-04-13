From Stdlib Require Import Arith List.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Multicore.Partitioned.Partitioned.
From RocqSched Require Import Multicore.Partitioned.PartitionedCompose.
From RocqSched Require Import Multicore.Partitioned.Policies.PartitionedPolicyLift.
From RocqSched Require Import Multicore.Partitioned.Policies.PartitionedBoolLemmas.

(* Fully constructive: no Classical import. *)

(** * Generic finite-optimality lifting for partitioned schedulers

    Given a uniprocessor policy with a finite-optimality theorem, this file
    provides a single generic lifting theorem that promotes local-CPU
    feasibility to global partitioned schedulability.

    Both [PartitionedEDF.v] and [PartitionedLLF.v] reduce their main
    [partitioned_*_schedulable_by_on_of_local_feasible] theorems to
    instantiations of [partitioned_finite_optimality_lift]. *)

(** Generic lifting: given a [local_scheduler] that is definitionally equal to
    [single_cpu_algorithm_schedule spec] and admits a finite-optimality theorem,
    per-CPU feasibility of the local job sets implies global partitioned
    schedulability under [partitioned_scheduler m spec]. *)
Theorem partitioned_finite_optimality_lift :
    forall (local_scheduler : CandidateSource -> Scheduler)
           (spec : GenericSchedulingAlgorithm),
      (forall cands, local_scheduler cands =
        single_cpu_algorithm_schedule spec cands) ->
      (forall J (J_bool : JobId -> bool) (enumJ : list JobId)
             (candidates_of : CandidateSource)
             (cand_spec : CandidateSourceSpec J candidates_of)
             jobs,
        (forall x, J_bool x = true <-> J x) ->
        (forall j, J j -> In j enumJ) ->
        (forall j, In j enumJ -> J j) ->
        feasible_on J jobs 1 ->
        schedulable_by_on J (local_scheduler candidates_of) jobs 1) ->
      forall (assign : JobId -> CPU) (m : nat)
             (valid_assignment : forall j, assign j < m)
             (J : JobId -> Prop)
             (J_bool : JobId -> bool)
             (enumJ : list JobId) jobs,
        (forall x, J_bool x = true <-> J x) ->
        (forall j, J j -> In j enumJ) ->
        (forall j, In j enumJ -> J j) ->
        (forall c, c < m ->
          feasible_on (local_jobset assign J c) jobs 1) ->
        schedulable_by_on
          J
          (partitioned_scheduler m spec (enum_local_candidates_of assign enumJ))
          jobs m.
Proof.
  intros local_scheduler spec Hscheduler Hoptimal
         assign m valid_assignment J J_bool enumJ jobs
         HJbool Henum_complete Henum_sound Hlocal_feasible.
  eapply (local_policy_schedulable_by_on_implies_partitioned_schedulable_by_on
            local_scheduler spec Hscheduler
            assign m valid_assignment J
            (enum_local_candidates_of assign enumJ)).
  - intros c Hlt.
    exact (enum_local_candidates_spec assign m J enumJ
             Henum_complete Henum_sound c Hlt).
  - intros c Hlt.
    eapply (Hoptimal
              (local_jobset assign J c)
              (local_jobset_bool assign J_bool c)
              (local_candidates assign enumJ c)
              (enum_local_candidates_of assign enumJ c)).
    + exact (enum_local_candidates_spec assign m J enumJ
               Henum_complete Henum_sound c Hlt).
    + intros x.
      exact (local_jobset_bool_spec assign J J_bool c HJbool x).
    + intros j Hj.
      exact (local_candidates_complete assign J enumJ
               Henum_complete j c (proj1 Hj) (proj2 Hj)).
    + intros j Hin.
      split.
      * apply Henum_sound.
        unfold local_candidates in Hin.
        apply filter_In in Hin.
        exact (proj1 Hin).
      * exact (local_candidates_sound assign enumJ c j Hin).
    + exact (Hlocal_feasible c Hlt).
Qed.
