From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
Require Import Base.
Require Import ScheduleModel.
Require Import ScheduleLemmas.ScheduleFacts.
Require Import SchedulerInterface.
Require Import SchedulingAlgorithmInterface.
Require Import SchedulingAlgorithmSchedulerBridge.
Require Import SchedulerValidity.
Require Import SchedulingAlgorithmRefinement.
Import ListNotations.

(* FIFO choose function:
   Linear scan through candidates in order; return the first eligible job.
   This implements "ordered eligible queue" semantics: the candidate list
   determines priority, and the first eligible entry wins.
   Returns None iff no candidate is eligible at time t. *)
Fixpoint choose_fifo (jobs : JobId -> Job) (m : nat) (sched : Schedule)
                      (t : Time) (candidates : list JobId) : option JobId :=
  match candidates with
  | []       => None
  | j :: rest =>
    if eligibleb jobs m sched j t
    then Some j
    else choose_fifo jobs m sched t rest
  end.

(* ===== Phase 1: GenericSchedulingAlgorithm Lemmas ===== *)

(* Lemma 1: The chosen job is eligible. *)
Lemma choose_fifo_eligible : forall jobs m sched t candidates j,
    choose_fifo jobs m sched t candidates = Some j ->
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

(* Lemma 2: If no candidate is eligible, choose_fifo returns None. *)
Lemma choose_fifo_none_if_no_eligible : forall jobs m sched t candidates,
    (forall j, In j candidates -> ~eligible jobs m sched j t) ->
    choose_fifo jobs m sched t candidates = None.
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

(* Lemma 3: If an eligible candidate exists, choose_fifo returns Some. *)
Lemma choose_fifo_some_if_exists : forall jobs m sched t candidates,
    (exists j, In j candidates /\ eligible jobs m sched j t) ->
    exists j', choose_fifo jobs m sched t candidates = Some j'.
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

(* Lemma 4: The chosen job is in the candidate list. *)
Lemma choose_fifo_in_candidates : forall jobs m sched t candidates j,
    choose_fifo jobs m sched t candidates = Some j ->
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

(* ===== Phase 2: Assemble GenericSchedulingAlgorithm ===== *)

Definition fifo_generic_spec : GenericSchedulingAlgorithm :=
  mkGenericSchedulingAlgorithm
    choose_fifo
    choose_fifo_eligible
    choose_fifo_some_if_exists
    choose_fifo_none_if_no_eligible
    choose_fifo_in_candidates.

(* ===== Phase 3: FIFO-Specific Invariant ===== *)

(* FIFO policy invariant: the chosen job is the FIRST eligible job in candidate order.
   All jobs before it in the list are NOT eligible. *)
Lemma choose_fifo_first_eligible : forall jobs m sched t candidates j,
    choose_fifo jobs m sched t candidates = Some j ->
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

(* ===== Phase 4: FIFO Scheduler Section ===== *)

Section FIFOSchedulerLemmasSection.

  Variable jobs        : JobId -> Job.
  Variable m           : nat.
  Variable sched       : Schedule.
  Variable t           : Time.
  Variable candidates  : list JobId.

  (* The chosen job is at the front of the eligible sub-sequence of candidates. *)
  Lemma fifo_choose_some_implies_first_in_order :
      forall j,
        choose_fifo jobs m sched t candidates = Some j ->
        forall j', In j' candidates ->
        eligible jobs m sched j' t ->
        (* j' either equals j or appears at or after j in candidates *)
        exists prefix suffix,
          candidates = prefix ++ j :: suffix /\
          ~In j' prefix.
  Proof.
    intros j Hchoose j' Hin' Helig'.
    destruct (choose_fifo_first_eligible jobs m sched t candidates j Hchoose)
        as [prefix [suffix [Heq Hpre]]].
    exists prefix, suffix.
    split.
    - exact Heq.
    - intro Hin_pre.
      exact (Hpre j' Hin_pre Helig').
  Qed.

End FIFOSchedulerLemmasSection.

(* Lift fifo_generic_spec into a Scheduler relation for the single-CPU case.
   candidates_of supplies the candidate list (in FIFO order) at each time step. *)
Definition fifo_scheduler
    (candidates_of : (JobId -> Job) -> nat -> Schedule -> Time -> list JobId)
    : Scheduler :=
  single_cpu_algorithm_schedule fifo_generic_spec candidates_of.

(* ===== Phase 5: Abstract FIFO policy ===== *)

(* Auxiliary: if choose_fifo returns None, all candidates are ineligible.
   (Converse of choose_fifo_none_if_no_eligible.) *)
Lemma choose_fifo_none_implies_no_eligible : forall jobs m sched t candidates,
    choose_fifo jobs m sched t candidates = None ->
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

(* Abstract FIFO policy: the first eligible job in candidate order wins.
   - None: all candidates are ineligible.
   - Some j: j is the first eligible entry — there exist prefix and suffix such
     that candidates = prefix ++ j :: suffix, j is eligible, and no job in
     prefix is eligible. *)
Definition fifo_policy : SchedulingAlgorithmSpec :=
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

Lemma fifo_policy_sane : SchedulingAlgorithmSpecSanity fifo_policy.
Proof.
  constructor.
  - intros jobs m sched t candidates j Hpol.
    unfold fifo_policy in Hpol.
    destruct Hpol as [prefix [suffix [Heq _]]].
    rewrite Heq.
    apply in_or_app. right. left. reflexivity.
  - intros jobs m sched t candidates j Hpol.
    unfold fifo_policy in Hpol.
    destruct Hpol as [prefix [suffix [_ [Helig _]]]].
    exact Helig.
Qed.

Lemma choose_fifo_refines_fifo_policy :
  algorithm_refines_spec fifo_generic_spec fifo_policy.
Proof.
  unfold algorithm_refines_spec.
  intros jobs m sched t candidates.
  unfold fifo_policy. simpl.
  destruct (choose_fifo jobs m sched t candidates) as [j|] eqn:Hchoose.
  - destruct (choose_fifo_first_eligible jobs m sched t candidates j Hchoose)
        as [prefix [suffix [Heq Hpre]]].
    exists prefix, suffix.
    split. exact Heq.
    split.
    + exact (choose_fifo_eligible jobs m sched t candidates j Hchoose).
    + exact Hpre.
  - intros j Hin Helig.
    exact (choose_fifo_none_implies_no_eligible jobs m sched t candidates Hchoose j Hin Helig).
Qed.

(* ===== Phase 6: UniSchedulerBundle instance for FIFO ===== *)

Require Import UniSchedulerInterface.
Require Import UniSchedulerLemmas.

(* Bundle that packages all FIFO components into the standard UniSchedulerBundle
   interface.  Spec is GenericSchedulingAlgorithm (identity instance from UniSchedulerInterface).
   Client supplies the candidate source; the rest is fixed to FIFO. *)
Definition fifo_bundle
    (J : JobId -> Prop)
    (candidates_of : CandidateSource)
    (cand_spec : CandidateSourceSpec J candidates_of)
  : UniSchedulerBundle J GenericSchedulingAlgorithm :=
  mkUniSchedulerBundle
    candidates_of
    fifo_generic_spec
    cand_spec
    fifo_policy
    fifo_policy_sane
    choose_fifo_refines_fifo_policy.

(* Thin wrapper: concrete single-CPU FIFO scheduler from a bundle. *)
Definition fifo_scheduler_on
    (J : JobId -> Prop)
    (candidates_of : CandidateSource)
    (cand_spec : CandidateSourceSpec J candidates_of)
    : Scheduler :=
  uni_scheduler_on (fifo_bundle J candidates_of cand_spec).

(* Thin wrapper: abstract FIFO policy scheduler from a bundle. *)
Definition fifo_policy_scheduler_on
    (J : JobId -> Prop)
    (candidates_of : CandidateSource)
    (cand_spec : CandidateSourceSpec J candidates_of)
    : Scheduler :=
  uni_policy_scheduler_on (fifo_bundle J candidates_of cand_spec).
