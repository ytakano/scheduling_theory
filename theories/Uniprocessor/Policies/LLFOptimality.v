From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From SchedulingTheory Require Import Foundation.Base.
From SchedulingTheory Require Import Semantics.Schedule.
From SchedulingTheory Require Import Semantics.ScheduleLemmas.ScheduleFacts.
From SchedulingTheory Require Import Semantics.ScheduleLemmas.SchedulePrefix.
From SchedulingTheory Require Import Semantics.ScheduleLemmas.ScheduleTransform.
From SchedulingTheory Require Import Semantics.ScheduleLemmas.ScheduleRestriction.
From SchedulingTheory Require Import Abstractions.Scheduler.Interface.
From SchedulingTheory Require Import Abstractions.SchedulingAlgorithm.Interface.
From SchedulingTheory Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From SchedulingTheory Require Import Uniprocessor.Generic.SchedulingAlgorithmCanonicalBridge.
From SchedulingTheory Require Import Uniprocessor.Generic.SchedulingAlgorithmNormalization.
From SchedulingTheory Require Import Uniprocessor.Generic.SchedulingAlgorithmOptimalitySkeleton.
From SchedulingTheory Require Import Uniprocessor.Policies.Common.MetricChooserLemmas.
From SchedulingTheory Require Import Uniprocessor.Policies.LLF.
From SchedulingTheory Require Import Uniprocessor.Policies.LLFLemmas.
From SchedulingTheory Require Import Uniprocessor.Policies.LLFTransform.
Import ListNotations.

(* === Canonicality decider === *)

(* Policy-specific decidability of canonicality at one time point.
   This is the LLF instance of the generic [canonical_at_dec] obligation. *)
Lemma llf_canonical_at_dec :
  forall candidates_of jobs sched t,
    {matches_choose_llf_at_with jobs candidates_of sched t} +
    {~ matches_choose_llf_at_with jobs candidates_of sched t}.
Proof.
  intros candidates_of jobs sched t.
  destruct (is_llf_canonical_at_b candidates_of jobs sched t) eqn:Hb.
  - left. apply (is_llf_canonical_at_b_true_iff candidates_of jobs sched t). exact Hb.
  - right. apply (is_llf_canonical_at_b_false_iff candidates_of jobs sched t). exact Hb.
Qed.

(* === Packaging LLF into the generic repair interface === *)

(* LLF adapter into the generic canonical-repair interface.

   The actual LLF-specific ingredients are provided separately:
   - the LLF canonical predicate,
   - its constructive decider,
   - the local one-step repair lemma,
   - and the scheduling algorithm prefix-agreement proof.

   This definition only packages those ingredients for reuse by the generic
   normalization theorem. *)
Definition LLFCanonicalRepairSpec
    (J : JobId -> Prop)
    (candidates_of : CandidateSource)
    (cand_spec : CandidateSourceSpec J candidates_of)
    (jobs : JobId -> Job) :
    CanonicalRepairSpec llf_generic_spec J candidates_of jobs.
  refine ({|
    canonical_at := fun sched t => matches_choose_llf_at_with jobs candidates_of sched t;
    canonical_before := fun sched H => matches_choose_llf_before jobs candidates_of sched H;
    canonical_before_def := fun sched H => conj (fun Hcanon => Hcanon) (fun Hcanon => Hcanon);
    canonical_at_def := fun sched t => conj (fun Hcanon => Hcanon) (fun Hcanon => Hcanon);
    canonical_at_dec := fun sched t => llf_canonical_at_dec candidates_of jobs sched t;
    repair_non_canonical := fun J_bool sched t HJbool Hvalid Hfeas HJonly Hcpu Hnot =>
      repair_non_canonical_at_llf J J_bool candidates_of cand_spec jobs sched t
        HJbool Hvalid Hfeas HJonly Hcpu Hnot
  |}).
Defined.

(* === Normalization wrapper === *)

(* LLF-specific wrapper around the generic normalization theorem.
   The normalization procedure itself is shared with EDF and other policies;
   only the packaged LLF obligations differ. *)
Lemma llf_normalize_to_canonical :
  forall J (J_bool : JobId -> bool) (candidates_of : CandidateSource)
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched H,
    (forall x, J_bool x = true <-> J x) ->
    valid_schedule jobs 1 sched ->
    feasible_schedule_on J jobs 1 sched ->
    (forall t j, sched t 0 = Some j -> J j) ->
    single_cpu_only sched ->
    exists sched',
      valid_schedule jobs 1 sched' /\
      feasible_schedule_on J jobs 1 sched' /\
      (forall t j, sched' t 0 = Some j -> J j) /\
      single_cpu_only sched' /\
      matches_choose_llf_before jobs candidates_of sched' H.
Proof.
  intros J J_bool candidates_of cand_spec jobs sched H HJbool Hvalid Hfeas HJonly Hcpu.
  eapply normalize_to_canonical_generic with
      (alg := llf_generic_spec)
      (J_bool := J_bool)
      (sched := sched).
  - exact (LLFCanonicalRepairSpec J candidates_of cand_spec jobs).
  - intros s1 s2 t Hagree.
    exact (llf_choose_agrees_before J candidates_of cand_spec jobs s1 s2 t Hagree).
  - exact HJbool.
  - exact Hvalid.
  - exact Hfeas.
  - exact HJonly.
  - exact Hcpu.
Qed.

(* === Finite optimality wrapper === *)

(* LLF-specific wrapper around the generic finite optimality theorem.
   After instantiating the common normalization-and-truncation pipeline with
   LLF's local obligations, the finite optimality statement is inherited from
   the generic skeleton. *)
Theorem llf_optimality_on_finite_jobs :
  forall J (J_bool : JobId -> bool) enumJ
         (candidates_of : CandidateSource)
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs,
    (forall x, J_bool x = true <-> J x) ->
    (forall j, J j -> In j enumJ) ->
    (forall j, In j enumJ -> J j) ->
    feasible_on J jobs 1 ->
    schedulable_by_on J (llf_scheduler candidates_of) jobs 1.
Proof.
  intros J J_bool enumJ candidates_of cand_spec jobs
         HJbool HJ_in _HJ_complete Hfeas_on.
  change (schedulable_by_on
            J
            (single_cpu_algorithm_scheduler_on J llf_generic_spec candidates_of cand_spec)
            jobs 1).
  eapply finite_optimality_via_normalization.
  - exact HJbool.
  - exact HJ_in.
  - intros sched0 H Hvalid Hfeas HJonly Hcpu.
    exact (llf_normalize_to_canonical J J_bool candidates_of cand_spec jobs sched0 H
             HJbool Hvalid Hfeas HJonly Hcpu).
  - intros s1 s2 t Hagree.
    exact (llf_choose_agrees_before J candidates_of cand_spec jobs s1 s2 t Hagree).
  - exact Hfeas_on.
Qed.
