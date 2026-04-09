From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
Require Import Base.
Require Import Schedule.
Require Import DispatchInterface.
Import ListNotations.

(* ===== FIFO Dispatcher: Definitions ===== *)

(* FIFO dispatch function:
   Linear scan through candidates in order; return the first ready job.
   This implements "ordered ready queue" semantics: the candidate list
   determines priority, and the first ready entry wins.
   Returns None iff no candidate is ready at time t. *)
Fixpoint choose_fifo (jobs : JobId -> Job) (m : nat) (sched : Schedule)
                      (t : Time) (candidates : list JobId) : option JobId :=
  match candidates with
  | []       => None
  | j :: rest =>
    if readyb jobs m sched j t
    then Some j
    else choose_fifo jobs m sched t rest
  end.

(* ===== Phase 1: GenericDispatchSpec Lemmas ===== *)

(* Lemma 1: The chosen job is ready. *)
Lemma choose_fifo_ready : forall jobs m sched t candidates j,
    choose_fifo jobs m sched t candidates = Some j ->
    ready jobs m sched j t.
Proof.
  intros jobs m sched t candidates.
  induction candidates as [| j0 rest IH].
  - intros j H. discriminate.
  - intros j H.
    simpl in H.
    destruct (readyb jobs m sched j0 t) eqn:Erb.
    + injection H as Heq. subst j.
      apply readyb_iff. exact Erb.
    + apply IH. exact H.
Qed.

(* Lemma 2: If no candidate is ready, choose_fifo returns None. *)
Lemma choose_fifo_none_if_no_ready : forall jobs m sched t candidates,
    (forall j, In j candidates -> ~ready jobs m sched j t) ->
    choose_fifo jobs m sched t candidates = None.
Proof.
  intros jobs m sched t candidates Hnone.
  induction candidates as [| j0 rest IH].
  - reflexivity.
  - simpl.
    destruct (readyb jobs m sched j0 t) eqn:Erb.
    + exfalso.
      apply (Hnone j0 (or_introl eq_refl)).
      apply readyb_iff. exact Erb.
    + apply IH.
      intros j Hin. apply Hnone. right. exact Hin.
Qed.

(* Lemma 3: If a ready candidate exists, choose_fifo returns Some. *)
Lemma choose_fifo_some_if_exists : forall jobs m sched t candidates,
    (exists j, In j candidates /\ ready jobs m sched j t) ->
    exists j', choose_fifo jobs m sched t candidates = Some j'.
Proof.
  intros jobs m sched t.
  induction candidates as [| h rest IHc].
  - intros [j [Hin _]]. contradiction.
  - intros [j [Hin Hready]].
    simpl.
    destruct (readyb jobs m sched h t) eqn:Erh.
    + exists h. reflexivity.
    + destruct Hin as [-> | Hin'].
      * exfalso.
        apply Bool.not_true_iff_false in Erh.
        apply Erh. apply readyb_iff. exact Hready.
      * apply IHc. exists j. split. exact Hin'. exact Hready.
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
    destruct (readyb jobs m sched j0 t) eqn:Erb.
    + injection H as Heq. subst j. left. reflexivity.
    + right. apply IH. exact H.
Qed.

(* ===== Phase 2: Assemble GenericDispatchSpec ===== *)

Definition fifo_generic_spec : GenericDispatchSpec :=
  mkGenericDispatchSpec
    choose_fifo
    choose_fifo_ready
    choose_fifo_some_if_exists
    choose_fifo_none_if_no_ready
    choose_fifo_in_candidates.

(* ===== Phase 3: FIFO-Specific Invariant ===== *)

(* FIFO policy invariant: the chosen job is the FIRST ready job in candidate order.
   All jobs before it in the list are NOT ready. *)
Lemma choose_fifo_first_ready : forall jobs m sched t candidates j,
    choose_fifo jobs m sched t candidates = Some j ->
    exists prefix suffix,
      candidates = prefix ++ j :: suffix /\
      forall j', In j' prefix -> ~ready jobs m sched j' t.
Proof.
  intros jobs m sched t candidates.
  induction candidates as [| j0 rest IH].
  - intros j H. discriminate.
  - intros j H.
    simpl in H.
    destruct (readyb jobs m sched j0 t) eqn:Erb.
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
           intro Hready. apply Erb. apply readyb_iff. exact Hready.
        -- apply Hpre. exact Hin'.
Qed.

(* ===== Phase 4: FIFO Scheduler Section ===== *)

Section FIFOSchedulerLemmasSection.

  Variable jobs        : JobId -> Job.
  Variable m           : nat.
  Variable sched       : Schedule.
  Variable t           : Time.
  Variable candidates  : list JobId.

  (* The chosen job is at the front of the ready sub-sequence of candidates. *)
  Lemma fifo_choose_some_implies_first_in_order :
      forall j,
        choose_fifo jobs m sched t candidates = Some j ->
        forall j', In j' candidates ->
        ready jobs m sched j' t ->
        (* j' either equals j or appears at or after j in candidates *)
        exists prefix suffix,
          candidates = prefix ++ j :: suffix /\
          ~In j' prefix.
  Proof.
    intros j Hchoose j' Hin' Hready'.
    destruct (choose_fifo_first_ready jobs m sched t candidates j Hchoose)
        as [prefix [suffix [Heq Hpre]]].
    exists prefix, suffix.
    split.
    - exact Heq.
    - intro Hin_pre.
      exact (Hpre j' Hin_pre Hready').
  Qed.

End FIFOSchedulerLemmasSection.
