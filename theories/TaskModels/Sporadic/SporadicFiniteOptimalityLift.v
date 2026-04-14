From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.EnumCandidates.
From RocqSched Require Import TaskModels.Sporadic.SporadicTasks.
From RocqSched Require Import TaskModels.Sporadic.SporadicFiniteHorizon.
From RocqSched Require Import TaskModels.Sporadic.SporadicEnumeration.
Import ListNotations.

(** * Generic sporadic finite-optimality lifting for uniprocessor schedulers

    Given a uniprocessor policy whose finite-optimality theorem has the standard
    form (takes a [CandidateSourceSpec] and [J_bool] and derives
    [schedulable_by_on J (local_scheduler cands) jobs 1]),
    this file provides a single generic lifting theorem that promotes the
    standard hypothesis to work over [sporadic_jobset_upto].

    Both [SporadicEDFBridge.v] and [SporadicLLFBridge.v] reduce their main
    theorems to instantiations of [sporadic_finite_optimality_lift].

    No automatic codec variant is provided: sporadic release times are not
    determined by (task, index) alone, so codec-based enumeration would require
    additional arrival information. The intended API is a thin witness wrapper
    around a manual finite enumeration. *)

(** ** Manual-enumeration variant

    The caller provides [enumJ] explicitly together with completeness and
    soundness proofs for [sporadic_jobset_upto T tasks jobs H]. *)
Theorem sporadic_finite_optimality_lift :
  forall (local_scheduler : CandidateSource -> Scheduler)
         (Hoptimal : forall J (J_bool : JobId -> bool) enumJ
                            (cands : CandidateSource)
                            (cand_spec : CandidateSourceSpec J cands) jobs,
                       (forall x, J_bool x = true <-> J x) ->
                       (forall j, J j -> In j enumJ) ->
                       (forall j, In j enumJ -> J j) ->
                       feasible_on J jobs 1 ->
                       schedulable_by_on J (local_scheduler cands) jobs 1)
         T T_bool tasks H enumJ jobs,
    (forall τ, T_bool τ = true <-> T τ) ->
    (forall j, sporadic_jobset_upto T tasks jobs H j -> In j enumJ) ->
    (forall j, In j enumJ -> sporadic_jobset_upto T tasks jobs H j) ->
    feasible_on (sporadic_jobset_upto T tasks jobs H) jobs 1 ->
    schedulable_by_on
      (sporadic_jobset_upto T tasks jobs H)
      (local_scheduler (enum_candidates_of enumJ))
      jobs 1.
Proof.
  intros local_scheduler Hoptimal T T_bool tasks H enumJ jobs
         HTbool Henum_complete Henum_sound Hfeas.
  apply (Hoptimal
    (sporadic_jobset_upto T tasks jobs H)
    (sporadic_jobset_upto_bool T_bool tasks jobs H)
    enumJ
    (enum_candidates_of enumJ)
    (enum_candidates_spec
       (sporadic_jobset_upto T tasks jobs H)
       enumJ
       Henum_complete
       Henum_sound)
    jobs).
  - intros j.
    exact (sporadic_jobset_upto_bool_spec T T_bool tasks jobs H HTbool j).
  - exact Henum_complete.
  - exact Henum_sound.
  - exact Hfeas.
Qed.

Theorem sporadic_finite_optimality_lift_with_witness :
  forall (local_scheduler : CandidateSource -> Scheduler)
         (Hoptimal : forall J (J_bool : JobId -> bool) enumJ
                            (cands : CandidateSource)
                            (cand_spec : CandidateSourceSpec J cands) jobs,
                       (forall x, J_bool x = true <-> J x) ->
                       (forall j, J j -> In j enumJ) ->
                       (forall j, In j enumJ -> J j) ->
                       feasible_on J jobs 1 ->
                       schedulable_by_on J (local_scheduler cands) jobs 1)
         T T_bool tasks H jobs
         (w : SporadicFiniteHorizonWitness T tasks jobs H),
    (forall τ, T_bool τ = true <-> T τ) ->
    feasible_on (sporadic_jobset_upto T tasks jobs H) jobs 1 ->
    schedulable_by_on
      (sporadic_jobset_upto T tasks jobs H)
      (local_scheduler (enum_candidates_of (sporadic_enumJ T tasks jobs H w)))
      jobs 1.
Proof.
  intros local_scheduler Hoptimal T T_bool tasks H jobs w HTbool Hfeas.
  exact (sporadic_finite_optimality_lift local_scheduler Hoptimal
    T T_bool tasks H (sporadic_enumJ T tasks jobs H w) jobs HTbool
    (sporadic_enum_complete T tasks jobs H w)
    (sporadic_enum_sound T tasks jobs H w)
    Hfeas).
Qed.
