From Stdlib Require Import Arith Arith.PeanoNat Lia List Bool.
From SchedulingTheory Require Import Foundation.Base.
From SchedulingTheory Require Import Semantics.Schedule.
From SchedulingTheory Require Import Abstractions.Scheduler.Interface.
From SchedulingTheory Require Import Abstractions.SchedulingAlgorithm.Interface.
From SchedulingTheory Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From SchedulingTheory Require Import Multicore.Partitioned.Partitioned.
From SchedulingTheory Require Import Multicore.Partitioned.PartitionedCompose.
From SchedulingTheory Require Import Uniprocessor.Policies.LLF.
From SchedulingTheory Require Import Uniprocessor.Policies.LLFOptimality.

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

Theorem local_llf_schedulable_by_on_implies_partitioned_llf_schedulable_by_on :
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
          (llf_scheduler (cands c))
          jobs 1) ->
      schedulable_by_on J (partitioned_llf_scheduler m cands) jobs m.
Proof.
  intros assign m valid_assignment J cands cands_spec jobs Hlocal.
  unfold partitioned_llf_scheduler.
  eapply (local_schedulable_by_on_implies_partitioned_schedulable_by_on
            assign m valid_assignment llf_generic_spec J cands cands_spec jobs).
  intros c Hlt.
  unfold llf_scheduler.
  exact (Hlocal c Hlt).
Qed.

Definition local_jobset_bool
    (assign : JobId -> CPU)
    (J_bool : JobId -> bool)
    (c : CPU) : JobId -> bool :=
  fun j => andb (J_bool j) (Nat.eqb (assign j) c).

Lemma local_jobset_bool_spec :
    forall (assign : JobId -> CPU)
           (J : JobId -> Prop)
           (J_bool : JobId -> bool)
           c,
      (forall x, J_bool x = true <-> J x) ->
      forall x,
        local_jobset_bool assign J_bool c x = true <->
        local_jobset assign J c x.
Proof.
  intros assign J J_bool c HJbool x.
  unfold local_jobset_bool, local_jobset.
  split.
  - intro Hx.
    apply andb_prop in Hx.
    destruct Hx as [HJx Hassign].
    apply Nat.eqb_eq in Hassign.
    apply HJbool in HJx.
    tauto.
  - intros [HJx Hassign].
    apply <- HJbool in HJx.
    apply Nat.eqb_eq in Hassign.
    rewrite HJx, Hassign.
    reflexivity.
Qed.

Theorem partitioned_llf_schedulable_by_on_of_local_feasible :
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
        (partitioned_llf_scheduler m (enum_local_candidates_of assign enumJ))
        jobs m.
Proof.
  intros assign m valid_assignment J J_bool enumJ jobs
         HJbool Henum_complete Henum_sound Hlocal_feasible.
  eapply (local_llf_schedulable_by_on_implies_partitioned_llf_schedulable_by_on
            assign m valid_assignment J
            (enum_local_candidates_of assign enumJ)).
  - intros c Hlt.
    exact (enum_local_candidates_spec assign m J enumJ
             Henum_complete Henum_sound c Hlt).
  - intros c Hlt.
    eapply (llf_optimality_on_finite_jobs
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
