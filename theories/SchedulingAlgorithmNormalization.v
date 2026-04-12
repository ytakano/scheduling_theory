From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
Require Import Base.
Require Import ScheduleModel.
Require Import ScheduleLemmas.SchedulePrefix.
Require Import ScheduleLemmas.ScheduleRestriction.
Require Import SchedulingAlgorithmInterface.
Require Import SchedulingAlgorithmSchedulerBridge.
Require Import SchedulingAlgorithmCanonicalBridge.
Import ListNotations.

(* A policy participates in generic canonicalization through three obligations:
   - canonical_at / canonical_before identify the policy-specific notion of
     "already matches the dispatcher"
   - repair_non_canonical locally fixes one non-canonical step while preserving
     validity, feasibility, J-only execution, and prefix agreement
   - canonical_at_dec lets the normalization proof stay constructive *)
Record CanonicalRepairSpec
    (alg : GenericSchedulingAlgorithm)
    (J : JobId -> Prop)
    (candidates_of : CandidateSource)
    (jobs : JobId -> Job) : Type := {
  canonical_at : Schedule -> Time -> Prop;
  canonical_before : Schedule -> Time -> Prop;

  canonical_before_def :
    forall sched H,
      canonical_before sched H <->
      matches_dispatch_before alg jobs candidates_of sched H;

  canonical_at_def :
    forall sched t,
      canonical_at sched t <->
      matches_dispatch_at_with alg jobs candidates_of sched t;

  canonical_at_dec :
    forall sched t,
      {canonical_at sched t} + {~ canonical_at sched t};

  repair_non_canonical :
    forall (J_bool : JobId -> bool) sched t,
      (forall x, J_bool x = true <-> J x) ->
      valid_schedule jobs 1 sched ->
      feasible_schedule_on J jobs 1 sched ->
      (forall t' j, sched t' 0 = Some j -> J j) ->
      single_cpu_only sched ->
      ~ canonical_at sched t ->
      exists sched',
        valid_schedule jobs 1 sched' /\
        feasible_schedule_on J jobs 1 sched' /\
        (forall t' j, sched' t' 0 = Some j -> J j) /\
        single_cpu_only sched' /\
        agrees_before sched sched' t /\
        canonical_at sched' t
}.

(* Canonicalization also needs the policy choice at time [t] to depend only on
   the schedule prefix before [t]. Candidate extensionality contributes one
   half of this fact; the policy-specific chooser contributes the other. *)
Definition DispatchAgreesBefore
    (alg : GenericSchedulingAlgorithm)
    (jobs : JobId -> Job)
    (candidates_of : CandidateSource) : Prop :=
  forall s1 s2 t,
    agrees_before s1 s2 t ->
    dispatch alg jobs 1 s1 t (candidates_of jobs 1 s1 t) =
    dispatch alg jobs 1 s2 t (candidates_of jobs 1 s2 t).

Lemma repair_pushes_forward_generic :
  forall alg candidates_of
         jobs sched sched' t,
    DispatchAgreesBefore alg jobs candidates_of ->
    agrees_before sched sched' t ->
    matches_dispatch_at_with alg jobs candidates_of sched' t ->
    matches_dispatch_before alg jobs candidates_of sched t ->
    matches_dispatch_before alg jobs candidates_of sched' (S t).
Proof.
  intros alg candidates_of jobs sched sched' t
         Hdispatch Hagree Hmatch Hbefore.
  unfold matches_dispatch_before.
  intros t' Hlt.
  assert (Hcases : t' < t \/ t' = t) by lia.
  destruct Hcases as [Hlt' | ->].
  - unfold matches_dispatch_at_with.
    specialize (Hbefore t' Hlt').
    unfold matches_dispatch_at_with in Hbefore.
    assert (Hpre : agrees_before sched sched' t').
    { apply (agrees_before_weaken sched sched' t' t). lia. exact Hagree. }
    assert (Hsched_eq : sched' t' 0 = sched t' 0)
      by (symmetry; exact (Hagree t' 0 Hlt')).
    rewrite Hsched_eq.
    rewrite (Hdispatch sched' sched t').
    + exact Hbefore.
    + exact (agrees_before_sym _ _ _ Hpre).
  - exact Hmatch.
Qed.

Lemma normalize_to_canonical_generic :
  forall alg J (J_bool : JobId -> bool)
         (candidates_of : CandidateSource)
         jobs sched H,
    CanonicalRepairSpec alg J candidates_of jobs ->
    DispatchAgreesBefore alg jobs candidates_of ->
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
      matches_dispatch_before alg jobs candidates_of sched' H.
Proof.
  intros alg J J_bool candidates_of jobs sched H Hspec Hdispatch HJbool.
  destruct Hspec as [canonical_at canonical_before
                      Hbefore_def Hat_def Hdec Hrepair].
  induction H as [| H' IH].
  - intros Hvalid Hfeas HJonly Hcpu.
    exists sched.
    refine (conj Hvalid (conj Hfeas (conj HJonly (conj Hcpu _)))).
    unfold matches_dispatch_before.
    intros t Hlt. lia.
  - intros Hvalid Hfeas HJonly Hcpu.
    destruct (IH Hvalid Hfeas HJonly Hcpu)
      as [sched_ih [Hvalid_ih [Hfeas_ih [HJonly_ih [Hcpu_ih Hcanon_ih]]]]].
    destruct (Hdec sched_ih H') as [Hat | Hnot].
    + exists sched_ih.
      refine (conj Hvalid_ih (conj Hfeas_ih (conj HJonly_ih (conj Hcpu_ih _)))).
      eapply (repair_pushes_forward_generic
                alg candidates_of jobs sched_ih sched_ih H').
      * exact Hdispatch.
      * apply agrees_before_refl.
      * apply (proj1 (Hat_def sched_ih H')).
        exact Hat.
      * exact Hcanon_ih.
    + destruct (Hrepair J_bool sched_ih H'
                  HJbool Hvalid_ih Hfeas_ih HJonly_ih Hcpu_ih Hnot)
        as [sched_r [Hvalid_r [Hfeas_r [HJonly_r [Hcpu_r [Hagree Hat_r]]]]]].
      exists sched_r.
      refine (conj Hvalid_r (conj Hfeas_r (conj HJonly_r (conj Hcpu_r _)))).
      eapply (repair_pushes_forward_generic
                alg candidates_of jobs sched_ih sched_r H').
      * exact Hdispatch.
      * exact Hagree.
      * apply (proj1 (Hat_def sched_r H')).
        exact Hat_r.
      * exact Hcanon_ih.
Qed.
