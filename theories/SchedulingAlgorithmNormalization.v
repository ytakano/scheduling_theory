From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
Require Import Base.
Require Import ScheduleModel.
Require Import ScheduleLemmas.SchedulePrefix.
Require Import ScheduleLemmas.ScheduleRestriction.
Require Import SchedulingAlgorithmInterface.
Require Import SchedulingAlgorithmSchedulerBridge.
Require Import SchedulingAlgorithmCanonicalBridge.
Import ListNotations.

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
        canonical_at sched' t;

  repair_pushes_forward :
    forall sched sched' t,
      single_cpu_only sched ->
      single_cpu_only sched' ->
      agrees_before sched sched' t ->
      canonical_at sched' t ->
      canonical_before sched t ->
      canonical_before sched' (S t)
}.

Lemma normalize_to_canonical_generic :
  forall alg J (J_bool : JobId -> bool)
         (candidates_of : CandidateSource)
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched H,
    CanonicalRepairSpec alg J candidates_of jobs ->
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
  intros alg J J_bool candidates_of cand_spec jobs sched H Hspec HJbool.
  destruct Hspec as [canonical_at canonical_before
                      Hbefore_def Hat_def Hdec Hrepair Hpush].
  induction H as [| H' IH].
  - intros Hvalid Hfeas HJonly Hcpu.
    exists sched.
    refine (conj Hvalid (conj Hfeas (conj HJonly (conj Hcpu _)))).
    unfold matches_dispatch_before.
    intros t Hlt. lia.
  - intros Hvalid Hfeas HJonly Hcpu.
    destruct (IH Hvalid Hfeas HJonly Hcpu)
      as [sched_ih [Hvalid_ih [Hfeas_ih [HJonly_ih [Hcpu_ih Hcanon_ih]]]]].
    assert (Hbefore_ih : canonical_before sched_ih H').
    { apply (proj2 (Hbefore_def sched_ih H')).
      exact Hcanon_ih. }
    destruct (Hdec sched_ih H') as [Hat | Hnot].
    + exists sched_ih.
      refine (conj Hvalid_ih (conj Hfeas_ih (conj HJonly_ih (conj Hcpu_ih _)))).
      apply (proj1 (Hbefore_def sched_ih (S H'))).
      eapply Hpush.
      * exact Hcpu_ih.
      * exact Hcpu_ih.
      * apply agrees_before_refl.
      * exact Hat.
      * exact Hbefore_ih.
    + destruct (Hrepair J_bool sched_ih H'
                  HJbool Hvalid_ih Hfeas_ih HJonly_ih Hcpu_ih Hnot)
        as [sched_r [Hvalid_r [Hfeas_r [HJonly_r [Hcpu_r [Hagree Hat_r]]]]]].
      exists sched_r.
      refine (conj Hvalid_r (conj Hfeas_r (conj HJonly_r (conj Hcpu_r _)))).
      apply (proj1 (Hbefore_def sched_r (S H'))).
      eapply Hpush.
      * exact Hcpu_ih.
      * exact Hcpu_r.
      * exact Hagree.
      * exact Hat_r.
      * exact Hbefore_ih.
Qed.
