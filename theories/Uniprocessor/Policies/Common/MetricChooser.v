(* Fully constructive: no Classical import. *)
From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia ZArith.
From SchedulingTheory Require Import Foundation.Base.
From SchedulingTheory Require Import Semantics.Schedule.
From SchedulingTheory Require Import Semantics.ScheduleLemmas.ScheduleFacts.
From SchedulingTheory Require Import Semantics.ScheduleLemmas.SchedulePrefix.
Import ListNotations.

(* Generic minimum-metric chooser over JobId lists.
   metric : JobId -> Z  assigns a Z-valued priority to each job.
   The job with the smallest metric wins (ties: earlier in list). *)

Fixpoint min_metric_job
    (metric : JobId -> Z) (l : list JobId) : option JobId :=
  match l with
  | [] => None
  | j :: rest =>
    match min_metric_job metric rest with
    | None    => Some j
    | Some j' =>
        if Z.leb (metric j) (metric j') then Some j else Some j'
    end
  end.

(* Choose the eligible candidate with the minimum metric. *)
Definition choose_min_metric
    (metric : JobId -> Z)
    (jobs : JobId -> Job) (m : nat) (sched : Schedule)
    (t : Time) (candidates : list JobId) : option JobId :=
  min_metric_job metric
    (filter (fun j => eligibleb jobs m sched j t) candidates).

(* ===== Structural Properties of min_metric_job ===== *)

Lemma min_metric_job_none_iff : forall metric l,
    min_metric_job metric l = None <-> l = [].
Proof.
  intros metric l. induction l as [| j rest IH]; simpl.
  - tauto.
  - split; [| discriminate].
    intro H.
    destruct (min_metric_job metric rest) as [j'|].
    + destruct (Z.leb (metric j) (metric j')); discriminate.
    + discriminate.
Qed.

Lemma min_metric_job_in : forall metric l j,
    min_metric_job metric l = Some j -> In j l.
Proof.
  intros metric l. induction l as [| j0 rest IH]; simpl.
  - discriminate.
  - intros j Hsome.
    destruct (min_metric_job metric rest) as [j'|] eqn:Erest.
    + destruct (Z.leb (metric j0) (metric j')) eqn:Ecmp.
      * injection Hsome as Heq. subst. left. reflexivity.
      * injection Hsome as Heq. subst. right. apply IH. reflexivity.
    + injection Hsome as Heq. subst. left. reflexivity.
Qed.

Lemma min_metric_job_min : forall metric l j,
    min_metric_job metric l = Some j ->
    forall j', In j' l ->
    (metric j <= metric j')%Z.
Proof.
  intros metric l. induction l as [| j0 rest IH]; simpl.
  - discriminate.
  - intros j Hsome j' Hin.
    destruct (min_metric_job metric rest) as [jmin|] eqn:Erest.
    + destruct (Z.leb (metric j0) (metric jmin)) eqn:Ecmp.
      * injection Hsome as Heq. subst j.
        apply Z.leb_le in Ecmp.
        destruct Hin as [-> | Hin'].
        -- lia.
        -- pose proof (IH jmin eq_refl j' Hin'). lia.
      * injection Hsome as Heq. subst jmin.
        apply Z.leb_nle in Ecmp.
        destruct Hin as [-> | Hin'].
        -- lia.
        -- apply IH. reflexivity. exact Hin'.
    + injection Hsome as Heq. subst j.
      destruct Hin as [-> | Hin'].
      * lia.
      * apply min_metric_job_none_iff in Erest. subst rest. contradiction.
Qed.

(* ===== choose_min_metric Correctness Lemmas ===== *)

(* The chosen job is eligible. *)
Lemma choose_min_metric_eligible : forall metric jobs m sched t candidates j,
    choose_min_metric metric jobs m sched t candidates = Some j ->
    eligible jobs m sched j t.
Proof.
  intros metric jobs m sched t candidates j Hchoose.
  unfold choose_min_metric in Hchoose.
  apply min_metric_job_in in Hchoose.
  apply filter_In in Hchoose.
  destruct Hchoose as [_ Hrb].
  apply eligibleb_iff. exact Hrb.
Qed.

(* If no candidate is eligible, returns None. *)
Lemma choose_min_metric_none_if_no_eligible : forall metric jobs m sched t candidates,
    (forall j, In j candidates -> ~eligible jobs m sched j t) ->
    choose_min_metric metric jobs m sched t candidates = None.
Proof.
  intros metric jobs m sched t candidates Hnone.
  unfold choose_min_metric.
  apply min_metric_job_none_iff.
  induction candidates as [| j0 rest IH].
  - reflexivity.
  - simpl. destruct (eligibleb jobs m sched j0 t) eqn:Erb.
    + exfalso. apply (Hnone j0 (or_introl eq_refl)).
      apply eligibleb_iff. exact Erb.
    + apply IH. intros j Hin. apply Hnone. right. exact Hin.
Qed.

(* If an eligible candidate exists, returns Some. *)
Lemma choose_min_metric_some_if_exists : forall metric jobs m sched t candidates,
    (exists j, In j candidates /\ eligible jobs m sched j t) ->
    exists j', choose_min_metric metric jobs m sched t candidates = Some j'.
Proof.
  intros metric jobs m sched t candidates [j [Hin Helig]].
  unfold choose_min_metric.
  assert (Hne : filter (fun j => eligibleb jobs m sched j t) candidates <> []).
  { intro Hempty.
    assert (Hin' : In j (filter (fun j => eligibleb jobs m sched j t) candidates)).
    { apply filter_In. split. exact Hin. apply eligibleb_iff. exact Helig. }
    rewrite Hempty in Hin'. contradiction. }
  destruct (min_metric_job metric (filter (fun j => eligibleb jobs m sched j t) candidates))
      as [j'|] eqn:Hmin.
  - exists j'. reflexivity.
  - apply min_metric_job_none_iff in Hmin. contradiction.
Qed.

(* The chosen job is always a member of the candidate list. *)
Lemma choose_min_metric_in_candidates : forall metric jobs m sched t candidates j,
    choose_min_metric metric jobs m sched t candidates = Some j ->
    In j candidates.
Proof.
  intros metric jobs m sched t candidates j Hchoose.
  unfold choose_min_metric in Hchoose.
  apply min_metric_job_in in Hchoose.
  apply filter_In in Hchoose.
  exact (proj1 Hchoose).
Qed.

(* The chosen job has the minimum metric among all eligible candidates. *)
Lemma choose_min_metric_min : forall metric jobs m sched t candidates j,
    choose_min_metric metric jobs m sched t candidates = Some j ->
    forall j', In j' candidates ->
    eligible jobs m sched j' t ->
    (metric j <= metric j')%Z.
Proof.
  intros metric jobs m sched t candidates j Hchoose j' Hin Helig.
  unfold choose_min_metric in Hchoose.
  apply (min_metric_job_min metric _ j Hchoose).
  apply filter_In. split.
  - exact Hin.
  - apply eligibleb_iff. exact Helig.
Qed.

(* If candidates exactly covers the eligible set, choose_min_metric returns Some. *)
Lemma choose_min_metric_complete : forall metric jobs m sched t candidates,
    (forall j, eligible jobs m sched j t <-> In j candidates) ->
    (exists j, eligible jobs m sched j t) ->
    exists j', choose_min_metric metric jobs m sched t candidates = Some j'.
Proof.
  intros metric jobs m sched t candidates Href [j Helig].
  apply choose_min_metric_some_if_exists.
  exists j. split.
  - apply Href. exact Helig.
  - exact Helig.
Qed.

(* If candidates exactly covers the eligible set, the chosen job is optimal. *)
Lemma choose_min_metric_optimal : forall metric jobs m sched t candidates j,
    (forall j', eligible jobs m sched j' t <-> In j' candidates) ->
    choose_min_metric metric jobs m sched t candidates = Some j ->
    forall j', eligible jobs m sched j' t ->
    (metric j <= metric j')%Z.
Proof.
  intros metric jobs m sched t candidates j Href Hchoose j' Helig.
  apply (choose_min_metric_min metric jobs m sched t candidates j Hchoose).
  - apply Href. exact Helig.
  - exact Helig.
Qed.

(* If two schedules agree before time t, choose_min_metric gives the same result. *)
Lemma choose_min_metric_agrees_before :
  forall metric jobs m s1 s2 t candidates,
    agrees_before s1 s2 t ->
    choose_min_metric metric jobs m s1 t candidates =
    choose_min_metric metric jobs m s2 t candidates.
Proof.
  intros metric jobs m s1 s2 t candidates Hagree.
  unfold choose_min_metric.
  f_equal.
  apply List.filter_ext.
  intro j.
  apply eligibleb_agrees_before. exact Hagree.
Qed.

(* If job j has strictly minimum metric, choose_min_metric is forced to return j. *)
Lemma choose_min_metric_unique_min : forall metric jobs m sched t candidates j,
    In j candidates ->
    eligible jobs m sched j t ->
    (forall j', In j' candidates -> eligible jobs m sched j' t ->
                j' <> j ->
                (metric j < metric j')%Z) ->
    choose_min_metric metric jobs m sched t candidates = Some j.
Proof.
  intros metric jobs m sched t candidates j Hin Helig Hstrict.
  destruct (choose_min_metric_some_if_exists metric jobs m sched t candidates) as [j' Hchoose].
  { exists j. split. exact Hin. exact Helig. }
  assert (Hj'_elig : eligible jobs m sched j' t).
  { apply (choose_min_metric_eligible metric jobs m sched t candidates). exact Hchoose. }
  assert (Hj'_in : In j' candidates).
  { apply (choose_min_metric_in_candidates metric jobs m sched t candidates). exact Hchoose. }
  assert (Hle : (metric j' <= metric j)%Z).
  { apply (choose_min_metric_min metric jobs m sched t candidates j' Hchoose j Hin Helig). }
  destruct (Nat.eq_dec j' j) as [Heq | Hneq].
  - rewrite Heq in Hchoose. exact Hchoose.
  - exfalso.
    pose proof (Hstrict j' Hj'_in Hj'_elig Hneq) as Hlt.
    lia.
Qed.
