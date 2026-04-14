From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.EnumCandidates.
From RocqSched Require Import Multicore.Partitioned.Partitioned.
From RocqSched Require Import Multicore.Partitioned.Policies.PartitionedFiniteOptimalityLift.
From RocqSched Require Import TaskModels.Sporadic.SporadicTasks.
From RocqSched Require Import TaskModels.Sporadic.SporadicFiniteHorizon.
Import ListNotations.

(** * Partitioned sporadic finite-optimality lifting

    Combines the uniprocessor sporadic finite-optimality lift
    ([SporadicFiniteOptimalityLift]) with the generic partitioned lift
    ([PartitionedFiniteOptimalityLift]) to connect

      sporadic task generation → partitioned multiprocessor schedulability

    in a single theorem.

    Typical usage pattern:
      1. Fix tasks, horizon H, and a static job-to-CPU assignment.
      2. Provide per-CPU feasibility of the local sporadic job sets.
      3. Instantiate [local_scheduler] / [spec] with a concrete policy
         (e.g. EDF: [edf_scheduler] / [edf_generic_spec]) and supply
         [edf_optimality_on_finite_jobs] as [Hoptimal].
      4. Conclude global [schedulable_by_on] under the partitioned scheduler.
*)

(** Generic partitioned lifting for sporadic job sets.

    Given a [local_scheduler] that
    (a) is equal to [single_cpu_algorithm_schedule spec] on every candidate
        source, and
    (b) admits a finite-optimality theorem [Hoptimal] for any job set [J],

    per-CPU feasibility of the local sporadic job sets implies global
    partitioned schedulability under [partitioned_scheduler m spec]. *)
Theorem partitioned_sporadic_finite_optimality_lift :
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
           T T_bool tasks H enumJ jobs,
      (forall τ, T_bool τ = true <-> T τ) ->
      (forall j, sporadic_jobset_upto T tasks jobs H j -> In j enumJ) ->
      (forall j, In j enumJ -> sporadic_jobset_upto T tasks jobs H j) ->
      (forall c, c < m ->
         feasible_on
           (local_jobset assign (sporadic_jobset_upto T tasks jobs H) c)
           jobs 1) ->
      schedulable_by_on
        (sporadic_jobset_upto T tasks jobs H)
        (partitioned_scheduler m spec (enum_local_candidates_of assign enumJ))
        jobs m.
Proof.
  intros local_scheduler spec Hscheduler Hoptimal
         assign m valid_assignment T T_bool tasks H enumJ jobs
         HTbool Henum_complete Henum_sound Hlocal_feasible.
  apply (partitioned_finite_optimality_lift local_scheduler spec Hscheduler Hoptimal
           assign m valid_assignment
           (sporadic_jobset_upto T tasks jobs H)
           (sporadic_jobset_upto_bool T_bool tasks jobs H)
           enumJ jobs).
  - intros j.
    exact (sporadic_jobset_upto_bool_spec T T_bool tasks jobs H HTbool j).
  - exact Henum_complete.
  - exact Henum_sound.
  - exact Hlocal_feasible.
Qed.
