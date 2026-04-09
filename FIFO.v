From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
Require Import Base.
Require Import Schedule.
Require Import UniSchedulerInterface.
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

(* ===== Phase 4: Concrete Example ===== *)

(* Example: candidates = [j1; j2; j3], j1 not ready, j2 ready, j3 ready.
   choose_fifo returns j2 (first ready in order). *)
Section FIFOExample.

  (* Concrete jobs *)
  Let j1 : JobId := 0.
  Let j2 : JobId := 1.
  Let j3 : JobId := 2.

  (* job_map: all jobs have release=0, cost=1, deadline=10 *)
  Let jobs : JobId -> Job := fun _ =>
    mkJob 0 0 0 1 10.

  (* A schedule where j2 and j3 are ready but j1 is already completed:
     j1 has service >= cost (completed), so not eligible, hence not ready.
     We model this by a schedule that ran j1 at t=0: sched 0 0 = Some j1. *)
  Let sched : Schedule := fun t c =>
    if (t =? 0) && (c =? 0) then Some j1 else None.

  (* At t=1, j1 is completed (service_job 1 sched j1 1 = 1 >= cost 1).
     j2 and j3 have service 0 < cost 1, are released (release=0 <= 1),
     and not running (sched 1 _ = None for all c).
     Hence j2 and j3 are ready at t=1. *)

  Example choose_fifo_example :
      choose_fifo jobs 1 sched 1 [j1; j2; j3] = Some j2.
  Proof.
    unfold choose_fifo, readyb, j1, j2, j3, jobs, sched.
    simpl.
    reflexivity.
  Qed.

End FIFOExample.

(* ===== Phase 5: FIFO Scheduler Section ===== *)

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
