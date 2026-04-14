(* Fully constructive: no Classical import. *)
From Stdlib Require Import Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Multicore.Partitioned.Partitioned.
From RocqSched Require Import Multicore.Partitioned.PartitionedCompose.
From RocqSched Require Import Multicore.Partitioned.Policies.PartitionedPolicyLift.
From RocqSched Require Import Uniprocessor.Policies.RoundRobin.

(** * Partitioned RR: thin wrapper over PartitionedCompose

    Specialises the generic [partitioned_scheduler] to [rr_generic_spec]
    and provides a convenience intro theorem that accepts per-CPU
    [rr_scheduler_on] witness schedules directly.

    The RR queue rotation semantics is encoded in the per-CPU CandidateSources:
    each [cands c] must return candidates in the current RR rotation order for
    CPU [c].  At unit quantum (q = 1) the CandidateSource rotates the front
    job to the back at every tick.

    This file is intentionally wrapper-only at present: RR has the generic
    witness-based and local-schedulable entry points, but no
    finite-optimality-based partitioned lift is exposed yet. *)

(* ===== Definition: partitioned_rr_scheduler ===== *)

(** RR-specific partitioned multiprocessor scheduler.
    Equivalent to [partitioned_scheduler m rr_generic_spec cands]. *)
Definition partitioned_rr_scheduler
    (m : nat)
    (cands : CPU -> CandidateSource) : Scheduler :=
  partitioned_scheduler m rr_generic_spec cands.

(* ===== Theorem: local_rr_witnesses_imply_partitioned_rr_schedulable_by_on ===== *)

(** RR-specific entry point for partitioned schedulability.

    Given per-CPU witness schedules each satisfying the [rr_scheduler_on]
    relation and local feasibility on the assigned job set, conclude
    [schedulable_by_on J (partitioned_rr_scheduler m cands) jobs m]. *)
Theorem local_rr_witnesses_imply_partitioned_rr_schedulable_by_on :
    forall (assign : JobId -> CPU) (m : nat)
           (valid_assignment : forall j, assign j < m)
           (J : JobId -> Prop)
           (cands : CPU -> CandidateSource)
           (cands_spec : forall c, c < m ->
             CandidateSourceSpec (local_jobset assign J c) (cands c))
           (jobs : JobId -> Job)
           (locals : CPU -> Schedule),
      (forall c, c < m ->
        scheduler_rel (rr_scheduler (cands c)) jobs 1 (locals c) /\
        feasible_schedule_on (local_jobset assign J c) jobs 1 (locals c)) ->
      schedulable_by_on J (partitioned_rr_scheduler m cands) jobs m.
Proof.
  intros assign m valid_assignment J cands cands_spec jobs locals Hlocals.
  unfold partitioned_rr_scheduler.
  eapply (local_policy_witnesses_imply_partitioned_schedulable_by_on
            rr_scheduler rr_generic_spec
            (fun cands0 => eq_refl)
            assign m valid_assignment J cands cands_spec jobs locals).
  exact Hlocals.
Qed.

Theorem local_rr_schedulable_by_on_implies_partitioned_rr_schedulable_by_on :
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
          (rr_scheduler (cands c))
          jobs 1) ->
      schedulable_by_on J (partitioned_rr_scheduler m cands) jobs m.
Proof.
  intros assign m valid_assignment J cands cands_spec jobs Hlocal.
  unfold partitioned_rr_scheduler.
  eapply (local_policy_schedulable_by_on_implies_partitioned_schedulable_by_on
            rr_scheduler rr_generic_spec
            (fun cands0 => eq_refl)
            assign m valid_assignment J cands cands_spec jobs).
  exact Hlocal.
Qed.
