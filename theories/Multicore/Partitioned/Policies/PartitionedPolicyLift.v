From SchedulingTheory Require Import Foundation.Base.
From SchedulingTheory Require Import Semantics.Schedule.
From SchedulingTheory Require Import Abstractions.Scheduler.Interface.
From SchedulingTheory Require Import Abstractions.SchedulingAlgorithm.Interface.
From SchedulingTheory Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From SchedulingTheory Require Import Multicore.Partitioned.Partitioned.
From SchedulingTheory Require Import Multicore.Partitioned.PartitionedCompose.

(* Fully constructive: no Classical import. *)

(** * Generic policy lifting for partitioned schedulers

    This file factors out the proof pattern shared by partitioned EDF/FIFO/RR/LLF:
    once a policy-specific local scheduler is definitionally equal to
    [single_cpu_algorithm_schedule spec], local witness schedules and local
    schedulability theorems lift to the generic partitioned scheduler. *)

Theorem local_policy_witnesses_imply_partitioned_schedulable_by_on :
    forall (local_scheduler : CandidateSource -> Scheduler)
           (spec : GenericSchedulingAlgorithm),
      (forall cands, local_scheduler cands =
        single_cpu_algorithm_schedule spec cands) ->
      forall (assign : JobId -> CPU) (m : nat)
             (valid_assignment : forall j, assign j < m)
             (J : JobId -> Prop)
             (cands : CPU -> CandidateSource)
             (cands_spec : forall c, c < m ->
               CandidateSourceSpec (local_jobset assign J c) (cands c))
             (jobs : JobId -> Job)
             (locals : CPU -> Schedule),
        (forall c, c < m ->
          scheduler_rel (local_scheduler (cands c)) jobs 1 (locals c) /\
          feasible_schedule_on (local_jobset assign J c) jobs 1 (locals c)) ->
        schedulable_by_on J (partitioned_scheduler m spec cands) jobs m.
Proof.
  intros local_scheduler spec Hscheduler
         assign m valid_assignment J cands cands_spec jobs locals Hlocals.
  eapply (local_witnesses_imply_partitioned_schedulable_by_on
            assign m valid_assignment spec J cands cands_spec jobs locals).
  intros c Hlt.
  destruct (Hlocals c Hlt) as [Hrel Hfeas].
  split.
  - rewrite Hscheduler in Hrel.
    exact Hrel.
  - exact Hfeas.
Qed.

Theorem local_policy_schedulable_by_on_implies_partitioned_schedulable_by_on :
    forall (local_scheduler : CandidateSource -> Scheduler)
           (spec : GenericSchedulingAlgorithm),
      (forall cands, local_scheduler cands =
        single_cpu_algorithm_schedule spec cands) ->
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
            (local_scheduler (cands c))
            jobs 1) ->
        schedulable_by_on J (partitioned_scheduler m spec cands) jobs m.
Proof.
  intros local_scheduler spec Hscheduler
         assign m valid_assignment J cands cands_spec jobs Hlocal.
  eapply (local_schedulable_by_on_implies_partitioned_schedulable_by_on
            assign m valid_assignment spec J cands cands_spec jobs).
  intros c Hlt.
  pose proof (Hlocal c Hlt) as Hsched.
  rewrite Hscheduler in Hsched.
  exact Hsched.
Qed.
