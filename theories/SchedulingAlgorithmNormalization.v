From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
Require Import Base.
Require Import ScheduleModel.
Require Import ScheduleLemmas.SchedulePrefix.
Require Import ScheduleLemmas.ScheduleRestriction.
Require Import SchedulingAlgorithmInterface.
Require Import SchedulingAlgorithmSchedulerBridge.
Require Import SchedulingAlgorithmCanonicalBridge.
Import ListNotations.

(* A policy enters the generic normalization framework by providing:
   (1) a policy-specific notion of "already canonical",
   (2) a constructive test for that notion, and
   (3) a one-step repair lemma that fixes a single non-canonical time point.

   The repair lemma is intentionally local: it only needs to repair the choice
   at time [t], while preserving schedule validity, feasibility on the target
   job set, the J-only execution invariant, the single-CPU shape invariant,
   and agreement with the original schedule before [t].

   This separation is what makes the normalization procedure reusable across
   different uniprocessor scheduling policies such as EDF and LLF. *)
Record CanonicalRepairSpec
    (alg : GenericSchedulingAlgorithm)
    (J : JobId -> Prop)
    (candidates_of : CandidateSource)
    (jobs : JobId -> Job) : Type := {
  (* Policy-specific canonicality at a single time instant. *)
  canonical_at : Schedule -> Time -> Prop;
  (* Canonicality of the whole prefix strictly before the given horizon. *)
  canonical_before : Schedule -> Time -> Prop;

  (* These equivalence fields serve as the bridge between a policy-facing
     presentation and the generic normalization infrastructure. A policy is
     free to expose canonicality under its own preferred names, as long as it
     proves equivalence with the generic dispatcher-match predicates. *)
  (* The policy-specific prefix notion must coincide with the generic
     dispatcher-based notion used by the normalization skeleton. *)
  canonical_before_def :
    forall sched H,
      canonical_before sched H <->
      matches_dispatch_before alg jobs candidates_of sched H;

  (* The policy-specific one-step notion must coincide with the generic
     dispatcher-match predicate at the current time. *)
  canonical_at_def :
    forall sched t,
      canonical_at sched t <->
      matches_dispatch_at_with alg jobs candidates_of sched t;

  (* Decidability keeps the normalization proof constructive: at each time
     point, we can inspect whether repair is needed. *)
  canonical_at_dec :
    forall sched t,
      {canonical_at sched t} + {~ canonical_at sched t};

  (* Local repair obligation: if the schedule is not canonical at time [t],
     build a new schedule that agrees before [t] and becomes canonical at [t],
     while preserving all global invariants needed by later phases. *)
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

(* Generic normalization does not only rely on candidate-source extensionality.
   It also needs the policy-specific dispatcher to be prefix-extensional:
   if two schedules agree strictly before [t], then the policy decision made
   at [t] from the corresponding candidate lists must also agree.

   Intuitively, normalization rewrites the future while keeping the past fixed.
   This hypothesis guarantees that changing the schedule at or after [t] does
   not retroactively change what the dispatcher should have done before [t]. *)
Definition DispatchAgreesBefore
    (alg : GenericSchedulingAlgorithm)
    (jobs : JobId -> Job)
    (candidates_of : CandidateSource) : Prop :=
  forall s1 s2 t,
    agrees_before s1 s2 t ->
    dispatch alg jobs 1 s1 t (candidates_of jobs 1 s1 t) =
    dispatch alg jobs 1 s2 t (candidates_of jobs 1 s2 t).

(* One-step propagation lemma for canonicalization.

   If a repaired schedule agrees with the original one before [t], is canonical
   at [t], and the original schedule was already canonical on every earlier
   time point, then the repaired schedule is canonical on the whole prefix
   before [S t]. *)
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

(* Generic finite-horizon normalization.

   The proof proceeds by induction on the horizon [H].
   - For [H = 0], the empty prefix is trivially canonical.
   - For [H = S H'], first normalize the prefix before [H'].
   - Then inspect whether the resulting schedule is already canonical at [H'].
   - If yes, keep it.
   - If not, apply the local repair lemma at [H'].
   - In both cases, use [repair_pushes_forward_generic] to extend canonicality
     from the prefix before [H'] to the prefix before [S H']. *)
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
