From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
Require Import Base.
Require Import Schedule.
Import ListNotations.

(* ===== EDF Dispatcher: Definitions ===== *)

(* Boolean version of ready: needed for filter.
   ready is a Prop; filter requires a bool-valued function. *)
Definition readyb (jobs : JobId -> Job) (m : nat) (sched : Schedule)
                   (j : JobId) (t : Time) : bool :=
  (job_release (jobs j) <=? t) &&
  negb (job_cost (jobs j) <=? service_job m sched j t).

(* Select the job with the minimum absolute deadline from a list.
   Returns None iff the list is empty.
   Tie-breaking: the earlier element in the list wins (<=? is not strict). *)
Fixpoint min_dl_job (jobs : JobId -> Job) (l : list JobId) : option JobId :=
  match l with
  | []       => None
  | j :: rest =>
    match min_dl_job jobs rest with
    | None    => Some j
    | Some j' => if job_abs_deadline (jobs j) <=? job_abs_deadline (jobs j')
                 then Some j
                 else Some j'
    end
  end.

(* EDF dispatch function:
   From candidates, filter to those that are ready, then select
   the one with the earliest (minimum) absolute deadline. *)
Definition choose_edf (jobs : JobId -> Job) (m : nat) (sched : Schedule)
                       (t : Time) (candidates : list JobId) : option JobId :=
  min_dl_job jobs (filter (fun j => readyb jobs m sched j t) candidates).

(* ===== Phase 1: Boolean / Propositional Bridge ===== *)

Lemma readyb_iff : forall jobs m sched j t,
    readyb jobs m sched j t = true <-> ready jobs m sched j t.
Proof.
  intros jobs m sched j t.
  unfold readyb, ready, pending, released, completed.
  rewrite Bool.andb_true_iff, Nat.leb_le, Bool.negb_true_iff.
  split; intros [H1 H2]; split; try exact H1.
  - intro Hge. apply Nat.leb_le in Hge. rewrite Hge in H2. discriminate.
  - apply Bool.not_true_iff_false. intro H. apply Nat.leb_le in H. exact (H2 H).
Qed.

(* ===== Phase 2: min_dl_job Structural Properties ===== *)

Lemma min_dl_job_none_iff : forall jobs l,
    min_dl_job jobs l = None <-> l = [].
Proof.
  intros jobs l. induction l as [| j rest IH]; simpl.
  - tauto.
  - split; [| discriminate].
    intro Hsome.
    destruct (min_dl_job jobs rest) as [j'|].
    + destruct (job_abs_deadline (jobs j) <=? job_abs_deadline (jobs j')); discriminate.
    + discriminate.
Qed.

Lemma min_dl_job_in : forall jobs l j,
    min_dl_job jobs l = Some j -> In j l.
Proof.
  intros jobs l. induction l as [| j0 rest IH]; simpl.
  - discriminate.
  - intros j Hsome.
    destruct (min_dl_job jobs rest) as [j'|] eqn:Erest.
    + destruct (job_abs_deadline (jobs j0) <=? job_abs_deadline (jobs j')) eqn:Ecmp.
      * injection Hsome as Heq. subst. left. reflexivity.
      * injection Hsome as Heq. subst. right. apply IH. reflexivity.
    + injection Hsome as Heq. subst. left. reflexivity.
Qed.

Lemma min_dl_job_min : forall jobs l j,
    min_dl_job jobs l = Some j ->
    forall j', In j' l ->
    job_abs_deadline (jobs j) <= job_abs_deadline (jobs j').
Proof.
  intros jobs l. induction l as [| j0 rest IH]; simpl.
  - discriminate.
  - intros j Hsome j' Hin.
    destruct (min_dl_job jobs rest) as [jmin|] eqn:Erest.
    + destruct (job_abs_deadline (jobs j0) <=? job_abs_deadline (jobs jmin)) eqn:Ecmp.
      * (* chosen = j0 *)
        injection Hsome as Heq. subst j.
        apply Nat.leb_le in Ecmp.
        destruct Hin as [-> | Hin'].
        -- lia.
        -- pose proof (IH jmin eq_refl j' Hin'). lia.
      * (* chosen = jmin; after subst jmin, j is the result *)
        injection Hsome as Heq. subst jmin.
        apply Bool.not_true_iff_false in Ecmp.
        rewrite Nat.leb_le in Ecmp.
        destruct Hin as [-> | Hin'].
        -- lia.
        -- apply IH. reflexivity. exact Hin'.
    + (* None branch: min_dl_job rest = None, so rest = [], j = j0 *)
      injection Hsome as Heq. subst j.
      destruct Hin as [-> | Hin'].
      * lia.
      * apply min_dl_job_none_iff in Erest. subst rest. contradiction.
Qed.

(* ===== Phase 3: EDF Dispatch Correctness ===== *)

(* Theorem 1: The chosen job is ready. *)
Theorem choose_edf_ready : forall jobs m sched t candidates j,
    choose_edf jobs m sched t candidates = Some j ->
    ready jobs m sched j t.
Proof.
  intros jobs m sched t candidates j Hchoose.
  unfold choose_edf in Hchoose.
  apply min_dl_job_in in Hchoose.
  apply filter_In in Hchoose.
  destruct Hchoose as [_ Hrb].
  apply readyb_iff. exact Hrb.
Qed.

(* Theorem 2: The chosen job has the minimum deadline among all ready candidates. *)
Theorem choose_edf_min_deadline : forall jobs m sched t candidates j,
    choose_edf jobs m sched t candidates = Some j ->
    forall j', In j' candidates ->
    ready jobs m sched j' t ->
    job_abs_deadline (jobs j) <= job_abs_deadline (jobs j').
Proof.
  intros jobs m sched t candidates j Hchoose j' Hin Hready.
  unfold choose_edf in Hchoose.
  apply (min_dl_job_min jobs _ j Hchoose).
  apply filter_In. split.
  - exact Hin.
  - apply readyb_iff. exact Hready.
Qed.

(* Theorem 3: A job is always chosen when a ready candidate exists. *)
Theorem choose_edf_some_if_exists : forall jobs m sched t candidates,
    (exists j, In j candidates /\ ready jobs m sched j t) ->
    exists j', choose_edf jobs m sched t candidates = Some j'.
Proof.
  intros jobs m sched t candidates [j [Hin Hready]].
  unfold choose_edf.
  assert (Hne : filter (fun j => readyb jobs m sched j t) candidates <> []).
  { intro Hempty.
    assert (Hin' : In j (filter (fun j => readyb jobs m sched j t) candidates)).
    { apply filter_In. split. exact Hin. apply readyb_iff. exact Hready. }
    rewrite Hempty in Hin'. contradiction. }
  destruct (min_dl_job jobs (filter (fun j => readyb jobs m sched j t) candidates))
      as [j'|] eqn:Hmin.
  - exists j'. reflexivity.
  - apply min_dl_job_none_iff in Hmin. contradiction.
Qed.
