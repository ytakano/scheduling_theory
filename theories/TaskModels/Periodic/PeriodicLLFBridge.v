From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From SchedulingTheory Require Import Foundation.Base.
From SchedulingTheory Require Import Semantics.Schedule.
From SchedulingTheory Require Import Abstractions.Scheduler.Interface.
From SchedulingTheory Require Import Abstractions.SchedulingAlgorithm.Interface.
From SchedulingTheory Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From SchedulingTheory Require Import Abstractions.SchedulingAlgorithm.EnumCandidates.
From SchedulingTheory Require Import Uniprocessor.Policies.LLF.
From SchedulingTheory Require Import Uniprocessor.Policies.LLFOptimality.
From SchedulingTheory Require Import TaskModels.Periodic.PeriodicTasks.
From SchedulingTheory Require Import TaskModels.Periodic.PeriodicFiniteHorizon.
Import ListNotations.

Theorem periodic_llf_optimality_on_finite_horizon :
  forall T T_bool tasks offset H enumJ jobs,
    (forall τ, T_bool τ = true <-> T τ) ->
    (forall j, periodic_jobset_upto T tasks offset jobs H j -> In j enumJ) ->
    (forall j, In j enumJ -> periodic_jobset_upto T tasks offset jobs H j) ->
    feasible_on (periodic_jobset_upto T tasks offset jobs H) jobs 1 ->
    schedulable_by_on
      (periodic_jobset_upto T tasks offset jobs H)
      (llf_scheduler (enum_candidates_of enumJ))
      jobs 1.
Proof.
  intros T T_bool tasks offset H enumJ jobs HTbool Henum_complete Henum_sound Hfeas.
  eapply (llf_optimality_on_finite_jobs
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
