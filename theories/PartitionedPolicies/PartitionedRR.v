(* Fully constructive: no Classical import. *)
From Stdlib Require Import Arith Arith.PeanoNat Lia.
Require Import Base.
Require Import ScheduleModel.
Require Import SchedulerInterface.
Require Import SchedulingAlgorithmInterface.
Require Import SchedulingAlgorithmSchedulerBridge.
Require Import Partitioned.
Require Import PartitionedCompose.
Require Import UniPolicies.RoundRobin.

(** * Partitioned RR: thin wrapper over PartitionedCompose

    Specialises the generic [partitioned_scheduler] to [rr_generic_spec]
    and provides a convenience intro theorem that accepts per-CPU
    [rr_scheduler_on] witness schedules directly.

    The RR queue rotation semantics is encoded in the per-CPU CandidateSources:
    each [cands c] must return candidates in the current RR rotation order for
    CPU [c].  At unit quantum (q = 1) the CandidateSource rotates the front
    job to the back at every tick. *)

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
  apply (local_witnesses_imply_partitioned_schedulable_by_on
           assign m valid_assignment rr_generic_spec J cands cands_spec
           jobs locals).
  intros c Hlt.
  destruct (Hlocals c Hlt) as [Hrel Hfeas].
  split.
  - unfold rr_scheduler in Hrel.
    exact Hrel.
  - exact Hfeas.
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
  eapply (local_schedulable_by_on_implies_partitioned_schedulable_by_on
            assign m valid_assignment rr_generic_spec J cands cands_spec jobs).
  intros c Hlt.
  unfold rr_scheduler.
  exact (Hlocal c Hlt).
Qed.
