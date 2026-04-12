(* Fully constructive: no Classical import. *)
From Stdlib Require Import Arith Arith.PeanoNat Lia.
From SchedulingTheory Require Import Foundation.Base.
From SchedulingTheory Require Import Semantics.Schedule.
From SchedulingTheory Require Import Abstractions.Scheduler.Interface.
From SchedulingTheory Require Import Abstractions.SchedulingAlgorithm.Interface.
From SchedulingTheory Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From SchedulingTheory Require Import Multicore.Partitioned.Partitioned.
From SchedulingTheory Require Import Multicore.Partitioned.PartitionedCompose.
From SchedulingTheory Require Import Multicore.Partitioned.Policies.PartitionedPolicyLift.
From SchedulingTheory Require Import Uniprocessor.Policies.FIFO.

(** * Partitioned FIFO: thin wrapper over PartitionedCompose

    Specialises the generic [partitioned_scheduler] to [fifo_generic_spec]
    and provides a convenience intro theorem that accepts per-CPU
    [fifo_scheduler] witness schedules directly. *)

(* ===== Definition: partitioned_fifo_scheduler ===== *)

(** FIFO-specific partitioned multiprocessor scheduler.
    Equivalent to [partitioned_scheduler m fifo_generic_spec cands]. *)
Definition partitioned_fifo_scheduler
    (m : nat)
    (cands : CPU -> CandidateSource) : Scheduler :=
  partitioned_scheduler m fifo_generic_spec cands.

(* ===== Theorem: local_fifo_witnesses_imply_partitioned_fifo_schedulable_by_on ===== *)

(** FIFO-specific entry point for partitioned schedulability.

    Given per-CPU witness schedules each satisfying the [fifo_scheduler]
    relation and local feasibility on the assigned job set, conclude
    [schedulable_by_on J (partitioned_fifo_scheduler m cands) jobs m]. *)
Theorem local_fifo_witnesses_imply_partitioned_fifo_schedulable_by_on :
    forall (assign : JobId -> CPU) (m : nat)
           (valid_assignment : forall j, assign j < m)
           (J : JobId -> Prop)
           (cands : CPU -> CandidateSource)
           (cands_spec : forall c, c < m ->
             CandidateSourceSpec (local_jobset assign J c) (cands c))
           (jobs : JobId -> Job)
           (locals : CPU -> Schedule),
      (forall c, c < m ->
        scheduler_rel (fifo_scheduler (cands c)) jobs 1 (locals c) /\
        feasible_schedule_on (local_jobset assign J c) jobs 1 (locals c)) ->
      schedulable_by_on J (partitioned_fifo_scheduler m cands) jobs m.
Proof.
  intros assign m valid_assignment J cands cands_spec jobs locals Hlocals.
  unfold partitioned_fifo_scheduler.
  eapply (local_policy_witnesses_imply_partitioned_schedulable_by_on
            fifo_scheduler fifo_generic_spec
            (fun cands0 => eq_refl)
            assign m valid_assignment J cands cands_spec jobs locals).
  exact Hlocals.
Qed.

Theorem local_fifo_schedulable_by_on_implies_partitioned_fifo_schedulable_by_on :
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
          (fifo_scheduler (cands c))
          jobs 1) ->
      schedulable_by_on J (partitioned_fifo_scheduler m cands) jobs m.
Proof.
  intros assign m valid_assignment J cands cands_spec jobs Hlocal.
  unfold partitioned_fifo_scheduler.
  eapply (local_policy_schedulable_by_on_implies_partitioned_schedulable_by_on
            fifo_scheduler fifo_generic_spec
            (fun cands0 => eq_refl)
            assign m valid_assignment J cands cands_spec jobs).
  exact Hlocal.
Qed.
