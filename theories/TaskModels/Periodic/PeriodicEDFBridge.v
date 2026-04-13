From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.EnumCandidates.
From RocqSched Require Import Uniprocessor.Policies.EDF.
From RocqSched Require Import Uniprocessor.Policies.EDFOptimality.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Periodic.PeriodicFiniteHorizon.
From RocqSched Require Import TaskModels.Periodic.PeriodicEnumeration.
Import ListNotations.

Theorem periodic_edf_optimality_on_finite_horizon :
  forall T T_bool tasks offset H enumJ jobs,
    (forall τ, T_bool τ = true <-> T τ) ->
    (forall j, periodic_jobset_upto T tasks offset jobs H j -> In j enumJ) ->
    (forall j, In j enumJ -> periodic_jobset_upto T tasks offset jobs H j) ->
    feasible_on (periodic_jobset_upto T tasks offset jobs H) jobs 1 ->
    schedulable_by_on
      (periodic_jobset_upto T tasks offset jobs H)
      (edf_scheduler (enum_candidates_of enumJ))
      jobs 1.
Proof.
  intros T T_bool tasks offset H enumJ jobs HTbool Henum_complete Henum_sound Hfeas.
  eapply (edf_optimality_on_finite_jobs
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

(* Auto version: derive the job enumeration from a task list and a codec,
   eliminating the need to hand-write enumJ and its soundness/completeness proofs. *)
Theorem periodic_edf_optimality_on_finite_horizon_auto :
  forall T tasks offset H enumT jobs
         (codec : PeriodicFiniteHorizonCodec T tasks offset jobs H),
    well_formed_periodic_tasks_on T tasks ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    feasible_on (periodic_jobset_upto T tasks offset jobs H) jobs 1 ->
    schedulable_by_on
      (periodic_jobset_upto T tasks offset jobs H)
      (edf_scheduler
         (enum_candidates_of
            (enum_periodic_jobs_upto T tasks offset jobs H enumT codec)))
      jobs 1.
Proof.
  intros T tasks offset H enumT jobs codec Hwf HenumT_complete HenumT_sound Hfeas.
  eapply periodic_edf_optimality_on_finite_horizon
    with (T_bool := task_in_list_b enumT)
         (enumJ := enum_periodic_jobs_upto T tasks offset jobs H enumT codec).
  - intros τ. rewrite task_in_list_b_spec.
    split; [apply HenumT_sound | apply HenumT_complete].
  - apply enum_periodic_jobs_upto_complete; assumption.
  - apply enum_periodic_jobs_upto_sound; assumption.
  - exact Hfeas.
Qed.
