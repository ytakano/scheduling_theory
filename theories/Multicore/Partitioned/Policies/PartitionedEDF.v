From Stdlib Require Import Arith Arith.PeanoNat Lia List Bool.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Multicore.Partitioned.Partitioned.
From RocqSched Require Import Multicore.Partitioned.PartitionedCompose.
From RocqSched Require Import Multicore.Partitioned.Policies.PartitionedPolicyLift.
From RocqSched Require Import Multicore.Partitioned.Policies.PartitionedBoolLemmas.
From RocqSched Require Import Multicore.Partitioned.Policies.PartitionedFiniteOptimalityLift.
From RocqSched Require Import Uniprocessor.Policies.EDF.
From RocqSched Require Import Uniprocessor.Policies.EDFOptimality.

(* Fully constructive: no Classical import. *)

(** * Partitioned EDF: thin wrapper over PartitionedCompose

    Specialises the generic [partitioned_scheduler] to [edf_generic_spec]
    and provides a convenience intro theorem that accepts per-CPU
    [edf_scheduler] witness schedules directly.

    This file intentionally stays thin: it re-exports the generic wrapper
    theorems from [PartitionedPolicyLift.v] under EDF-specific names and adds
    the finite-optimality-based entry theorem built on
    [PartitionedFiniteOptimalityLift.v]. *)

(* ===== Definition: partitioned_edf_scheduler ===== *)

(** EDF-specific partitioned multiprocessor scheduler.
    Equivalent to [partitioned_scheduler m edf_generic_spec cands]. *)
Definition partitioned_edf_scheduler
    (m : nat)
    (cands : CPU -> CandidateSource) : Scheduler :=
  partitioned_scheduler m edf_generic_spec cands.

(* ===== Theorem: local_edf_witnesses_imply_partitioned_edf_schedulable_by_on ===== *)

(** EDF-specific entry point for partitioned schedulability.

    Given per-CPU witness schedules each satisfying the [edf_scheduler]
    relation and local feasibility on the assigned job set, conclude
    [schedulable_by_on J (partitioned_edf_scheduler m cands) jobs m]. *)
Theorem local_edf_witnesses_imply_partitioned_edf_schedulable_by_on :
    forall (assign : JobId -> CPU) (m : nat)
           (valid_assignment : forall j, assign j < m)
           (J : JobId -> Prop)
           (cands : CPU -> CandidateSource)
           (cands_spec : forall c, c < m ->
             CandidateSourceSpec (local_jobset assign J c) (cands c))
           (jobs : JobId -> Job)
           (locals : CPU -> Schedule),
      (forall c, c < m ->
        scheduler_rel (edf_scheduler (cands c)) jobs 1 (locals c) /\
        feasible_schedule_on (local_jobset assign J c) jobs 1 (locals c)) ->
      schedulable_by_on J (partitioned_edf_scheduler m cands) jobs m.
Proof.
  intros assign m valid_assignment J cands cands_spec jobs locals Hlocals.
  unfold partitioned_edf_scheduler.
  eapply (local_policy_witnesses_imply_partitioned_schedulable_by_on
            edf_scheduler edf_generic_spec
            (fun cands0 => eq_refl)
            assign m valid_assignment J cands cands_spec jobs locals).
  exact Hlocals.
Qed.

Theorem local_edf_schedulable_by_on_implies_partitioned_edf_schedulable_by_on :
    forall (assign : JobId -> CPU) (m : nat)
           (valid_assignment : forall j, assign j < m)
           (J : JobId -> Prop)
           (cands : CPU -> CandidateSource)
           (cands_spec : forall c, c < m ->
             CandidateSourceSpec (local_jobset assign J c) (cands c))
           (jobs : JobId -> Job),
      (forall c, c < m ->
        schedulable_by_on
          (local_jobset assign J c)
          (edf_scheduler (cands c))
          jobs 1) ->
      schedulable_by_on J (partitioned_edf_scheduler m cands) jobs m.
Proof.
  intros assign m valid_assignment J cands cands_spec jobs Hlocal.
  unfold partitioned_edf_scheduler.
  eapply (local_policy_schedulable_by_on_implies_partitioned_schedulable_by_on
            edf_scheduler edf_generic_spec
            (fun cands0 => eq_refl)
            assign m valid_assignment J cands cands_spec jobs).
  exact Hlocal.
Qed.

Theorem partitioned_edf_schedulable_by_on_of_local_feasible :
    forall (assign : JobId -> CPU) (m : nat)
           (valid_assignment : forall j, assign j < m)
           (J : JobId -> Prop)
           (J_bool : JobId -> bool)
           enumJ jobs,
      (forall x, J_bool x = true <-> J x) ->
      (forall j, J j -> In j enumJ) ->
      (forall j, In j enumJ -> J j) ->
      (forall c, c < m ->
        feasible_on (local_jobset assign J c) jobs 1) ->
      schedulable_by_on
        J
        (partitioned_edf_scheduler m (enum_local_candidates_of assign enumJ))
        jobs m.
Proof.
  intros assign m valid_assignment J J_bool enumJ jobs
         HJbool Henum_complete Henum_sound Hlocal_feasible.
  unfold partitioned_edf_scheduler.
  exact (partitioned_finite_optimality_lift
           edf_scheduler edf_generic_spec (fun _ => eq_refl)
           edf_optimality_on_finite_jobs
           assign m valid_assignment J J_bool enumJ jobs
           HJbool Henum_complete Henum_sound Hlocal_feasible).
Qed.
