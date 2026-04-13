(* Fully constructive: no Classical import. *)
From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Semantics.ScheduleLemmas.ScheduleFacts.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Abstractions.Scheduler.Validity.
From RocqSched Require Import Refinement.SchedulingAlgorithmRefinement.
Import ListNotations.

(** * Round Robin choose policy (unit quantum, q = 1)

    Design note:
    The *semantics* of Round Robin lives entirely in the [CandidateSource],
    not in this chooser.  At each tick t the caller supplies a candidate list
    whose order already reflects the current RR rotation state (i.e. the job
    that is "next in the wheel" appears first).  The chooser simply picks the
    first eligible entry — identical to FIFO.

    Concretely:
    - [candidates_of jobs m sched t] is expected to return jobs in the
      "current RR queue order", taking into account the schedule prefix
      [sched] up to time t (which encodes which job ran last and thus needs
      to be moved to the back of the wheel).
    - The chooser does NOT update queue state; queue rotation is the
      responsibility of the CandidateSource.
    - q = 1 is assumed throughout: after each tick, the running job is
      moved to the back of the queue by the CandidateSource.

    This design matches the CandidateSource / CandidateSourceSpec split used
    by all other policies in this project and keeps the chooser simple and
    reusable. *)

(* ===== Phase 1: choose_rr choose function ===== *)

(** Round Robin choose: linear scan through the candidate list; return the
    first eligible job.  The candidate list encodes RR order, so "first
    eligible" is exactly the RR choice. *)
Fixpoint choose_rr (jobs : JobId -> Job) (m : nat) (sched : Schedule)
                    (t : Time) (candidates : list JobId) : option JobId :=
  match candidates with
  | []       => None
  | j :: rest =>
    if eligibleb jobs m sched j t
    then Some j
    else choose_rr jobs m sched t rest
  end.

(* ===== Phase 2: GenericSchedulingAlgorithm Lemmas ===== *)

(** Lemma 1: The chosen job is eligible. *)
Lemma choose_rr_eligible : forall jobs m sched t candidates j,
    choose_rr jobs m sched t candidates = Some j ->
    eligible jobs m sched j t.
Proof.
  intros jobs m sched t candidates.
  induction candidates as [| j0 rest IH].
  - intros j H. discriminate.
  - intros j H.
    simpl in H.
    destruct (eligibleb jobs m sched j0 t) eqn:Erb.
    + injection H as Heq. subst j.
      apply eligibleb_iff. exact Erb.
    + apply IH. exact H.
Qed.

(** Lemma 2: If no candidate is eligible, choose_rr returns None. *)
Lemma choose_rr_none_if_no_eligible : forall jobs m sched t candidates,
    (forall j, In j candidates -> ~eligible jobs m sched j t) ->
    choose_rr jobs m sched t candidates = None.
Proof.
  intros jobs m sched t candidates Hnone.
  induction candidates as [| j0 rest IH].
  - reflexivity.
  - simpl.
    destruct (eligibleb jobs m sched j0 t) eqn:Erb.
    + exfalso.
      apply (Hnone j0 (or_introl eq_refl)).
      apply eligibleb_iff. exact Erb.
    + apply IH.
      intros j Hin. apply Hnone. right. exact Hin.
Qed.

(** Lemma 3: If an eligible candidate exists, choose_rr returns Some. *)
Lemma choose_rr_some_if_exists : forall jobs m sched t candidates,
    (exists j, In j candidates /\ eligible jobs m sched j t) ->
    exists j', choose_rr jobs m sched t candidates = Some j'.
Proof.
  intros jobs m sched t.
  induction candidates as [| h rest IHc].
  - intros [j [Hin _]]. contradiction.
  - intros [j [Hin Helig]].
    simpl.
    destruct (eligibleb jobs m sched h t) eqn:Erh.
    + exists h. reflexivity.
    + destruct Hin as [-> | Hin'].
      * exfalso.
        apply Bool.not_true_iff_false in Erh.
        apply Erh. apply eligibleb_iff. exact Helig.
      * apply IHc. exists j. split. exact Hin'. exact Helig.
Qed.

(** Lemma 4: The chosen job is in the candidate list. *)
Lemma choose_rr_in_candidates : forall jobs m sched t candidates j,
    choose_rr jobs m sched t candidates = Some j ->
    In j candidates.
Proof.
  intros jobs m sched t candidates.
  induction candidates as [| j0 rest IH].
  - intros j H. discriminate.
  - intros j H.
    simpl in H.
    destruct (eligibleb jobs m sched j0 t) eqn:Erb.
    + injection H as Heq. subst j. left. reflexivity.
    + right. apply IH. exact H.
Qed.

(* ===== Phase 3: Assemble GenericSchedulingAlgorithm ===== *)

Definition rr_generic_spec : GenericSchedulingAlgorithm :=
  mkGenericSchedulingAlgorithm
    choose_rr
    choose_rr_eligible
    choose_rr_some_if_exists
    choose_rr_none_if_no_eligible
    choose_rr_in_candidates.

(* ===== Phase 4: RR-specific policy invariant ===== *)

(** The chosen job is the FIRST eligible job in the (RR-ordered) candidate list.
    All jobs before it in the list are NOT eligible. *)
Lemma choose_rr_first_eligible : forall jobs m sched t candidates j,
    choose_rr jobs m sched t candidates = Some j ->
    exists prefix suffix,
      candidates = prefix ++ j :: suffix /\
      forall j', In j' prefix -> ~eligible jobs m sched j' t.
Proof.
  intros jobs m sched t candidates.
  induction candidates as [| j0 rest IH].
  - intros j H. discriminate.
  - intros j H.
    simpl in H.
    destruct (eligibleb jobs m sched j0 t) eqn:Erb.
    + injection H as Heq. subst j.
      exists [], rest.
      split.
      * reflexivity.
      * intros j' Hin. contradiction.
    + destruct (IH j H) as [prefix [suffix [Heq Hpre]]].
      exists (j0 :: prefix), suffix.
      split.
      * simpl. rewrite Heq. reflexivity.
      * intros j' Hin.
        destruct Hin as [-> | Hin'].
        -- apply Bool.not_true_iff_false in Erb.
           intro Helig. apply Erb. apply eligibleb_iff. exact Helig.
        -- apply Hpre. exact Hin'.
Qed.

(* ===== Phase 5: Abstract RR policy ===== *)

(** Abstract RR policy: the first eligible job in RR candidate order wins.
    The candidate list represents the current RR queue rotation; the
    first eligible entry is the job that the RR wheel points to.
    - None: all candidates are ineligible.
    - Some j: j is the first eligible entry — candidates = prefix ++ j :: suffix,
      j is eligible, and no job in prefix is eligible. *)
Definition rr_policy : SchedulingAlgorithmSpec :=
  fun jobs m sched t candidates oj =>
    match oj with
    | None =>
        forall j, In j candidates -> ~eligible jobs m sched j t
    | Some j =>
        exists prefix suffix,
          candidates = prefix ++ j :: suffix /\
          eligible jobs m sched j t /\
          forall j', In j' prefix -> ~eligible jobs m sched j' t
    end.

Lemma rr_policy_sane : SchedulingAlgorithmSpecSanity rr_policy.
Proof.
  constructor.
  - intros jobs m sched t candidates j Hpol.
    unfold rr_policy in Hpol.
    destruct Hpol as [prefix [suffix [Heq _]]].
    rewrite Heq.
    apply in_or_app. right. left. reflexivity.
  - intros jobs m sched t candidates j Hpol.
    unfold rr_policy in Hpol.
    destruct Hpol as [prefix [suffix [_ [Helig _]]]].
    exact Helig.
Qed.

(** Auxiliary: choose_rr returns None implies all candidates ineligible. *)
Lemma choose_rr_none_implies_no_eligible : forall jobs m sched t candidates,
    choose_rr jobs m sched t candidates = None ->
    forall j, In j candidates -> ~eligible jobs m sched j t.
Proof.
  intros jobs m sched t candidates.
  induction candidates as [| j0 rest IH].
  - intros _ j Hin. exact (False_ind _ Hin).
  - intros Hnone j Hin Helig.
    simpl in Hnone.
    destruct (eligibleb jobs m sched j0 t) eqn:Erb.
    + discriminate.
    + destruct Hin as [-> | Hin'].
      * apply eligibleb_iff in Helig. rewrite Helig in Erb. discriminate.
      * exact (IH Hnone j Hin' Helig).
Qed.

Lemma choose_rr_refines_rr_policy :
    algorithm_refines_spec rr_generic_spec rr_policy.
Proof.
  unfold algorithm_refines_spec.
  intros jobs m sched t candidates.
  unfold rr_policy. simpl.
  destruct (choose_rr jobs m sched t candidates) as [j|] eqn:Hchoose.
  - destruct (choose_rr_first_eligible jobs m sched t candidates j Hchoose)
        as [prefix [suffix [Heq Hpre]]].
    exists prefix, suffix.
    split. exact Heq.
    split.
    + exact (choose_rr_eligible jobs m sched t candidates j Hchoose).
    + exact Hpre.
  - intros j Hin Helig.
    exact (choose_rr_none_implies_no_eligible jobs m sched t candidates Hchoose j Hin Helig).
Qed.

(* ===== Phase 6: Concrete RR scheduler ===== *)

(** Lift rr_generic_spec into a Scheduler relation for the single-CPU case.
    [candidates_of] supplies the candidate list in RR rotation order at each
    time step.  The caller is responsible for encoding the RR state (which
    job ran last and thus moves to the back of the queue) into the list
    ordering. *)
Definition rr_scheduler
    (candidates_of : (JobId -> Job) -> nat -> Schedule -> Time -> list JobId)
    : Scheduler :=
  single_cpu_algorithm_schedule rr_generic_spec candidates_of.

(* ===== Phase 7: UniSchedulerBundle instance for RR ===== *)

From RocqSched Require Import Uniprocessor.Core.UniSchedulerInterface.
From RocqSched Require Import Uniprocessor.Core.UniSchedulerLemmas.

(** Bundle that packages all RR components into the standard UniSchedulerBundle
    interface.  Client supplies the candidate source (which encodes RR order);
    the rest is fixed to RR. *)
Definition rr_bundle
    (J : JobId -> Prop)
    (candidates_of : CandidateSource)
    (cand_spec : CandidateSourceSpec J candidates_of)
  : UniSchedulerBundle J GenericSchedulingAlgorithm :=
  mkUniSchedulerBundle
    candidates_of
    rr_generic_spec
    cand_spec
    rr_policy
    rr_policy_sane
    choose_rr_refines_rr_policy.

(** Thin wrapper: concrete single-CPU RR scheduler from a bundle. *)
Definition rr_scheduler_on
    (J : JobId -> Prop)
    (candidates_of : CandidateSource)
    (cand_spec : CandidateSourceSpec J candidates_of)
    : Scheduler :=
  uni_scheduler_on (rr_bundle J candidates_of cand_spec).

(** Thin wrapper: abstract RR policy scheduler from a bundle. *)
Definition rr_policy_scheduler_on
    (J : JobId -> Prop)
    (candidates_of : CandidateSource)
    (cand_spec : CandidateSourceSpec J candidates_of)
    : Scheduler :=
  uni_policy_scheduler_on (rr_bundle J candidates_of cand_spec).
