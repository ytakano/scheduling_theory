From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.EnumCandidates.
From RocqSched Require Import Multicore.Partitioned.Partitioned.
From RocqSched Require Import Multicore.Partitioned.Policies.PartitionedFiniteOptimalityLift.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Periodic.PeriodicFiniteHorizon.
From RocqSched Require Import TaskModels.Periodic.PeriodicEnumeration.
Import ListNotations.

(** * Partitioned periodic finite-optimality lifting

    Combines the uniprocessor periodic finite-optimality lift
    ([PeriodicFiniteOptimalityLift]) with the generic partitioned lift
    ([PartitionedFiniteOptimalityLift]) to connect

      periodic task generation → partitioned multiprocessor schedulability

    in a single theorem.

    Typical usage pattern:
      1. Fix tasks, offset, horizon H, and a static assignment.
      2. Provide per-CPU feasibility of the local periodic job sets.
      3. Instantiate [local_scheduler] / [spec] with a concrete policy
         (e.g. EDF: [edf_scheduler] / [edf_generic_spec]) and supply
         [edf_optimality_on_finite_jobs] as [Hoptimal].
      4. Conclude global [schedulable_by_on] under the partitioned scheduler.
*)

(** Generic partitioned lifting for periodic job sets.

    Given a [local_scheduler] that
    (a) is equal to [single_cpu_algorithm_schedule spec] on every candidate
        source, and
    (b) admits a finite-optimality theorem [Hoptimal] for any job set [J],

    per-CPU feasibility of the local periodic job sets implies global
    partitioned schedulability under [partitioned_scheduler m spec]. *)
Theorem partitioned_periodic_finite_optimality_lift :
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
           T T_bool tasks offset H enumJ jobs,
      (forall τ, T_bool τ = true <-> T τ) ->
      (forall j, periodic_jobset_upto T tasks offset jobs H j -> In j enumJ) ->
      (forall j, In j enumJ -> periodic_jobset_upto T tasks offset jobs H j) ->
      (forall c, c < m ->
         feasible_on
           (local_jobset assign (periodic_jobset_upto T tasks offset jobs H) c)
           jobs 1) ->
      schedulable_by_on
        (periodic_jobset_upto T tasks offset jobs H)
        (partitioned_scheduler m spec (enum_local_candidates_of assign enumJ))
        jobs m.
Proof.
  intros local_scheduler spec Hscheduler Hoptimal
         assign m valid_assignment T T_bool tasks offset H enumJ jobs
         HTbool Henum_complete Henum_sound Hlocal_feasible.
  apply (partitioned_finite_optimality_lift local_scheduler spec Hscheduler Hoptimal
           assign m valid_assignment
           (periodic_jobset_upto T tasks offset jobs H)
           (periodic_jobset_upto_bool T_bool tasks offset jobs H)
           enumJ jobs).
  - intros j.
    exact (periodic_jobset_upto_bool_spec T T_bool tasks offset jobs H HTbool j).
  - exact Henum_complete.
  - exact Henum_sound.
  - exact Hlocal_feasible.
Qed.
