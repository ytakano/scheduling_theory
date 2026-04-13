From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.EnumCandidates.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Periodic.PeriodicFiniteHorizon.
From RocqSched Require Import TaskModels.Periodic.PeriodicEnumeration.
Import ListNotations.

(** * Generic periodic finite-optimality lifting for uniprocessor schedulers

    Given a uniprocessor policy whose finite-optimality theorem has the standard
    form (takes a [CandidateSourceSpec] and [J_bool] and derives
    [schedulable_by_on J (local_scheduler cands) jobs 1]),
    this file provides a single generic lifting theorem that promotes the
    standard hypothesis to work over [periodic_jobset_upto].

    Both [PeriodicEDFBridge.v] and [PeriodicLLFBridge.v] reduce their main
    theorems to instantiations of [periodic_finite_optimality_lift]. *)

(** ** Manual-enumeration variant

    The caller provides [enumJ] explicitly together with completeness and
    soundness proofs for [periodic_jobset_upto T tasks offset jobs H]. *)
Theorem periodic_finite_optimality_lift :
  forall (local_scheduler : CandidateSource -> Scheduler)
         (Hoptimal : forall J (J_bool : JobId -> bool) enumJ
                            (cands : CandidateSource)
                            (cand_spec : CandidateSourceSpec J cands) jobs,
                       (forall x, J_bool x = true <-> J x) ->
                       (forall j, J j -> In j enumJ) ->
                       (forall j, In j enumJ -> J j) ->
                       feasible_on J jobs 1 ->
                       schedulable_by_on J (local_scheduler cands) jobs 1)
         T T_bool tasks offset H enumJ jobs,
    (forall τ, T_bool τ = true <-> T τ) ->
    (forall j, periodic_jobset_upto T tasks offset jobs H j -> In j enumJ) ->
    (forall j, In j enumJ -> periodic_jobset_upto T tasks offset jobs H j) ->
    feasible_on (periodic_jobset_upto T tasks offset jobs H) jobs 1 ->
    schedulable_by_on
      (periodic_jobset_upto T tasks offset jobs H)
      (local_scheduler (enum_candidates_of enumJ))
      jobs 1.
Proof.
  intros local_scheduler Hoptimal T T_bool tasks offset H enumJ jobs
         HTbool Henum_complete Henum_sound Hfeas.
  apply (Hoptimal
    (periodic_jobset_upto T tasks offset jobs H)
    (periodic_jobset_upto_bool T_bool tasks offset jobs H)
    enumJ
    (enum_candidates_of enumJ)
    (enum_candidates_spec
       (periodic_jobset_upto T tasks offset jobs H)
       enumJ
       Henum_complete
       Henum_sound)
    jobs).
  - intros j.
    exact (periodic_jobset_upto_bool_spec T T_bool tasks offset jobs H HTbool j).
  - exact Henum_complete.
  - exact Henum_sound.
  - exact Hfeas.
Qed.

(** ** Codec-based automatic-enumeration variant

    The job list is derived automatically from a task list [enumT] and a
    [PeriodicFiniteHorizonCodec], eliminating the need to hand-write [enumJ]
    and its soundness/completeness proofs. *)
Theorem periodic_finite_optimality_lift_auto :
  forall (local_scheduler : CandidateSource -> Scheduler)
         (Hoptimal : forall J (J_bool : JobId -> bool) enumJ
                            (cands : CandidateSource)
                            (cand_spec : CandidateSourceSpec J cands) jobs,
                       (forall x, J_bool x = true <-> J x) ->
                       (forall j, J j -> In j enumJ) ->
                       (forall j, In j enumJ -> J j) ->
                       feasible_on J jobs 1 ->
                       schedulable_by_on J (local_scheduler cands) jobs 1)
         T tasks offset H enumT jobs
         (codec : PeriodicFiniteHorizonCodec T tasks offset jobs H),
    well_formed_periodic_tasks_on T tasks ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    feasible_on (periodic_jobset_upto T tasks offset jobs H) jobs 1 ->
    schedulable_by_on
      (periodic_jobset_upto T tasks offset jobs H)
      (local_scheduler
         (enum_candidates_of
            (enum_periodic_jobs_upto T tasks offset jobs H enumT codec)))
      jobs 1.
Proof.
  intros local_scheduler Hoptimal T tasks offset H enumT jobs codec
         Hwf HenumT_complete HenumT_sound Hfeas.
  eapply periodic_finite_optimality_lift with (T_bool := task_in_list_b enumT).
  - exact Hoptimal.
  - intros τ. rewrite task_in_list_b_spec.
    split; [apply HenumT_sound | apply HenumT_complete].
  - apply enum_periodic_jobs_upto_complete; assumption.
  - apply enum_periodic_jobs_upto_sound; assumption.
  - exact Hfeas.
Qed.
