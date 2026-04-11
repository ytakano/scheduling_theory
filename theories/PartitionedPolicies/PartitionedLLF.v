From Stdlib Require Import Arith Arith.PeanoNat Lia.
Require Import Base.
Require Import ScheduleModel.
Require Import SchedulerInterface.
Require Import SchedulingAlgorithmInterface.
Require Import SchedulingAlgorithmSchedulerBridge.
Require Import Partitioned.
Require Import PartitionedCompose.
Require Import UniPolicies.Laxity.

(* Fully constructive: no Classical import. *)

(** * Partitioned LLF: thin wrapper over PartitionedCompose

    Specialises the generic [partitioned_scheduler] to [llf_generic_spec]
    and provides a convenience intro theorem that accepts per-CPU
    [llf_scheduler] witness schedules directly. *)

(* ===== Definition: partitioned_llf_scheduler ===== *)

(** LLF-specific partitioned multiprocessor scheduler.
    Equivalent to [partitioned_scheduler m llf_generic_spec cands]. *)
Definition partitioned_llf_scheduler
    (m : nat)
    (cands : CPU -> CandidateSource) : Scheduler :=
  partitioned_scheduler m llf_generic_spec cands.

(* ===== Theorem: local_llf_witnesses_imply_partitioned_llf_schedulable_by_on ===== *)

(** LLF-specific entry point for partitioned schedulability.

    Given per-CPU witness schedules each satisfying the [llf_scheduler]
    relation and local feasibility on the assigned job set, conclude
    [schedulable_by_on J (partitioned_llf_scheduler m cands) jobs m]. *)
Theorem local_llf_witnesses_imply_partitioned_llf_schedulable_by_on :
    forall (assign : JobId -> CPU) (m : nat)
           (valid_assignment : forall j, assign j < m)
           (J : JobId -> Prop)
           (cands : CPU -> CandidateSource)
           (cands_spec : forall c, c < m ->
             CandidateSourceSpec (local_jobset assign J c) (cands c))
           (jobs : JobId -> Job)
           (locals : CPU -> Schedule),
      (forall c, c < m ->
        scheduler_rel (llf_scheduler (cands c)) jobs 1 (locals c) /\
        feasible_schedule_on (local_jobset assign J c) jobs 1 (locals c)) ->
      schedulable_by_on J (partitioned_llf_scheduler m cands) jobs m.
Proof.
  intros assign m valid_assignment J cands cands_spec jobs locals Hlocals.
  unfold partitioned_llf_scheduler.
  apply (local_witnesses_imply_partitioned_schedulable_by_on
           assign m valid_assignment llf_generic_spec J cands cands_spec
           jobs locals).
  intros c Hlt.
  destruct (Hlocals c Hlt) as [Hrel Hfeas].
  split.
  - unfold llf_scheduler in Hrel.
    exact Hrel.
  - exact Hfeas.
Qed.
