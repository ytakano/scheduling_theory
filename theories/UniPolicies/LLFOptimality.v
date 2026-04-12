From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
Require Import Base.
Require Import ScheduleModel.
Require Import ScheduleLemmas.ScheduleFacts.
Require Import ScheduleLemmas.SchedulePrefix.
Require Import ScheduleLemmas.ScheduleTransform.
Require Import ScheduleLemmas.ScheduleRestriction.
Require Import SchedulerInterface.
Require Import SchedulingAlgorithmInterface.
Require Import SchedulingAlgorithmSchedulerBridge.
Require Import SchedulingAlgorithmCanonicalBridge.
Require Import SchedulingAlgorithmNormalization.
Require Import SchedulingAlgorithmOptimalitySkeleton.
Require Import UniPolicies.MetricChooserLemmas.
Require Import UniPolicies.LLF.
Require Import UniPolicies.LLFLemmas.
Require Import UniPolicies.LLFTransform.
Import ListNotations.

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
    exact (llf_dispatch_agrees_before J candidates_of cand_spec jobs s1 s2 t Hagree).
  - exact HJbool.
  - exact Hvalid.
  - exact Hfeas.
  - exact HJonly.
  - exact Hcpu.
Qed.

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
    exact (llf_dispatch_agrees_before J candidates_of cand_spec jobs s1 s2 t Hagree).
  - exact Hfeas_on.
Qed.
