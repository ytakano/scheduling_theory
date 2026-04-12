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

Lemma repair_pushes_first_violation_forward_llf :
  forall J (candidates_of : CandidateSource)
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched sched' t0,
    single_cpu_only sched ->
    single_cpu_only sched' ->
    agrees_before sched sched' t0 ->
    matches_choose_llf_at_with jobs candidates_of sched' t0 ->
    matches_choose_llf_before jobs candidates_of sched t0 ->
    matches_choose_llf_before jobs candidates_of sched' (S t0).
Proof.
  intros J candidates_of cand_spec jobs sched sched' t0
         Honly Honly' Hagree Hmatch Hbefore.
  unfold matches_choose_llf_before, matches_dispatch_before.
  intros t Hlt.
  assert (Hcases : t < t0 \/ t = t0) by lia.
  destruct Hcases as [Hlt' | Heq].
  - unfold matches_choose_llf_at_with, matches_dispatch_at_with.
    simpl.
    specialize (Hbefore t Hlt').
    unfold matches_choose_llf_at_with, matches_dispatch_at_with in Hbefore.
    simpl in Hbefore.
    assert (Hpre : agrees_before sched sched' t).
    { apply (agrees_before_weaken sched sched' t t0). lia. exact Hagree. }
    assert (Hpre_sym : agrees_before sched' sched t)
      by (exact (agrees_before_sym _ _ _ Hpre)).
    assert (Hs't0 : sched' t 0 = sched t 0)
      by (symmetry; exact (Hagree t 0 Hlt')).
    assert (Hcand_eq : candidates_of jobs 1 sched' t = candidates_of jobs 1 sched t).
    { apply (candidates_prefix_extensional J candidates_of cand_spec jobs 1 sched' sched t).
      intros t' c Hlt''.
      destruct (Nat.eq_dec c 0) as [-> | Hcne].
      - symmetry. exact (Hpre t' 0 Hlt'').
      - assert (Hcpos : 0 < c) by lia.
        rewrite (Honly' t' c Hcpos). rewrite (Honly t' c Hcpos). reflexivity. }
    assert (Hchoose_eq : choose_llf jobs 1 sched' t (candidates_of jobs 1 sched' t) =
                         choose_llf jobs 1 sched t (candidates_of jobs 1 sched t)).
    { rewrite Hcand_eq.
      apply (choose_llf_agrees_before jobs sched' sched t (candidates_of jobs 1 sched t)).
      exact Hpre_sym. }
    rewrite Hs't0. rewrite Hchoose_eq. exact Hbefore.
  - subst t. exact Hmatch.
Qed.

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
Proof.
  refine ({|
    canonical_at := fun sched t => matches_choose_llf_at_with jobs candidates_of sched t;
    canonical_before := fun sched H => matches_choose_llf_before jobs candidates_of sched H;
    canonical_before_def := _;
    canonical_at_def := _;
    canonical_at_dec := _;
    repair_non_canonical := _;
    repair_pushes_forward := _
  |}).
  - intros sched H. tauto.
  - intros sched t. tauto.
  - intros sched t. apply llf_canonical_at_dec.
  - intros J_bool sched t HJbool Hvalid Hfeas HJonly Hcpu Hnot.
    exact (repair_non_canonical_at_llf J J_bool candidates_of cand_spec jobs sched t
             HJbool Hvalid Hfeas HJonly Hcpu Hnot).
  - intros sched sched' t Hcpu Hcpu' Hagree Hcanon Hat.
    exact (repair_pushes_first_violation_forward_llf J candidates_of cand_spec
             jobs sched sched' t Hcpu Hcpu' Hagree Hcanon Hat).
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
      (cand_spec := cand_spec)
      (J_bool := J_bool)
      (sched := sched).
  - exact (LLFCanonicalRepairSpec J candidates_of cand_spec jobs).
  - exact HJbool.
  - exact Hvalid.
  - exact Hfeas.
  - exact HJonly.
  - exact Hcpu.
Qed.

Lemma canonical_and_idle_implies_scheduler_rel_llf :
  forall J enumJ (candidates_of : CandidateSource)
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched,
    (forall j, J j -> In j enumJ) ->
    valid_schedule jobs 1 sched ->
    feasible_schedule_on J jobs 1 sched ->
    single_cpu_only sched ->
    matches_choose_llf_before jobs candidates_of sched (deadline_horizon jobs enumJ) ->
    (forall t, deadline_horizon jobs enumJ <= t -> sched t 0 = None) ->
    scheduler_rel (llf_scheduler candidates_of) jobs 1 sched.
Proof.
  intros J enumJ candidates_of cand_spec jobs sched
         HJ_in Hvalid Hfeas Honly Hcanon Hidle.
  unfold llf_scheduler.
  eapply canonical_and_idle_implies_scheduler_rel_generic; eauto.
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
