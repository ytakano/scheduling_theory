From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia ZArith.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Semantics.ScheduleLemmas.ScheduleFacts.
From RocqSched Require Import Semantics.ScheduleLemmas.SchedulePrefix.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.Common.MetricChooser.
Import ListNotations.

(* Common lemmas for metric-based scheduling algorithms (EDF, LLF, ...). *)

Lemma min_metric_job_ext :
  forall metric1 metric2 l,
    (forall j, In j l -> metric1 j = metric2 j) ->
    min_metric_job metric1 l = min_metric_job metric2 l.
Proof.
  intros metric1 metric2 l.
  induction l as [|j rest IH]; intros Hext; simpl.
  - reflexivity.
  - rewrite IH.
    2:{
      intros j' Hin.
      apply Hext.
      right. exact Hin.
    }
    destruct (min_metric_job metric2 rest) as [j'|] eqn:Hrest.
    + rewrite <- (Hext j (or_introl eq_refl)).
      rewrite <- (Hext j' (or_intror (min_metric_job_in metric2 rest j' Hrest))).
      reflexivity.
    + reflexivity.
Qed.

Lemma min_metric_job_map_ext :
  forall metric_src metric_tgt f l,
    (forall j, In j l -> metric_tgt (f j) = metric_src j) ->
    min_metric_job metric_tgt (map f l) =
    match min_metric_job metric_src l with
    | Some j => Some (f j)
    | None => None
    end.
Proof.
  intros metric_src metric_tgt f l.
  induction l as [|j rest IH]; intros Hmetric; simpl.
  - reflexivity.
  - rewrite IH.
    2:{
      intros j' Hin.
      apply Hmetric.
      right; exact Hin.
    }
    destruct (min_metric_job metric_src rest) as [j'|] eqn:Hrest.
    + rewrite (Hmetric j (or_introl eq_refl)).
      rewrite (Hmetric j' (or_intror (min_metric_job_in metric_src rest j' Hrest))).
      destruct (metric_src j <=? metric_src j')%Z;
        reflexivity.
    + reflexivity.
Qed.

Lemma min_metric_job_map_cmp :
  forall metric_src metric_tgt f l,
    (forall j1 j2,
       In j1 l ->
       In j2 l ->
       (metric_tgt (f j1) <=? metric_tgt (f j2))%Z =
       (metric_src j1 <=? metric_src j2)%Z) ->
    min_metric_job metric_tgt (map f l) =
    match min_metric_job metric_src l with
    | Some j => Some (f j)
    | None => None
    end.
Proof.
  intros metric_src metric_tgt f l.
  induction l as [|j rest IH]; intros Hcmp; simpl.
  - reflexivity.
  - rewrite IH.
    2:{
      intros j1 j2 Hin1 Hin2.
      apply Hcmp; right; assumption.
    }
    destruct (min_metric_job metric_src rest) as [j'|] eqn:Hrest.
    + rewrite
        (Hcmp j j'
           (or_introl eq_refl)
           (or_intror (min_metric_job_in metric_src rest j' Hrest))).
      destruct (metric_src j <=? metric_src j')%Z;
        reflexivity.
    + reflexivity.
Qed.

Lemma filter_map_ext :
  forall (f : JobId -> JobId) keep_src keep_tgt l,
    (forall j, In j l -> keep_tgt (f j) = keep_src j) ->
    filter keep_tgt (map f l) =
    map f (filter keep_src l).
Proof.
  intros f keep_src keep_tgt l Hkeep.
  induction l as [|j rest IH]; simpl.
  - reflexivity.
  - rewrite (Hkeep j (or_introl eq_refl)).
    destruct (keep_src j); simpl.
    + f_equal.
      apply IH.
      intros j' Hin.
      apply Hkeep.
      right; exact Hin.
    + apply IH.
      intros j' Hin.
      apply Hkeep.
      right; exact Hin.
Qed.

Lemma choose_min_metric_map_ext :
  forall metric_src metric_tgt jobs_src jobs_tgt m sched_src sched_tgt
         t_src t_tgt f candidates,
    (forall j, In j candidates ->
       eligibleb jobs_tgt m sched_tgt (f j) t_tgt =
       eligibleb jobs_src m sched_src j t_src) ->
    (forall j,
       In j candidates ->
       eligibleb jobs_src m sched_src j t_src = true ->
       metric_tgt (f j) = metric_src j) ->
    choose_min_metric metric_tgt jobs_tgt m sched_tgt t_tgt
      (map f candidates) =
    match choose_min_metric metric_src jobs_src m sched_src t_src candidates with
    | Some j => Some (f j)
    | None => None
    end.
Proof.
  intros metric_src metric_tgt jobs_src jobs_tgt m sched_src sched_tgt
         t_src t_tgt f candidates Helig Hmetric.
  unfold choose_min_metric.
  rewrite
    (filter_map_ext
       f
       (fun j => eligibleb jobs_src m sched_src j t_src)
       (fun j => eligibleb jobs_tgt m sched_tgt j t_tgt)
       candidates Helig).
  rewrite
    (min_metric_job_map_ext
       metric_src metric_tgt f
       (filter (fun j => eligibleb jobs_src m sched_src j t_src)
          candidates)).
  - reflexivity.
  - intros j Hin.
    apply filter_In in Hin as [Hin Heligj].
    exact (Hmetric j Hin Heligj).
Qed.

Lemma choose_min_metric_map_cmp :
  forall metric_src metric_tgt jobs_src jobs_tgt m sched_src sched_tgt
         t_src t_tgt f candidates,
    (forall j, In j candidates ->
       eligibleb jobs_tgt m sched_tgt (f j) t_tgt =
       eligibleb jobs_src m sched_src j t_src) ->
    (forall j1 j2,
       In j1 candidates ->
       In j2 candidates ->
       eligibleb jobs_src m sched_src j1 t_src = true ->
       eligibleb jobs_src m sched_src j2 t_src = true ->
       (metric_tgt (f j1) <=? metric_tgt (f j2))%Z =
       (metric_src j1 <=? metric_src j2)%Z) ->
    choose_min_metric metric_tgt jobs_tgt m sched_tgt t_tgt
      (map f candidates) =
    match choose_min_metric metric_src jobs_src m sched_src t_src candidates with
    | Some j => Some (f j)
    | None => None
    end.
Proof.
  intros metric_src metric_tgt jobs_src jobs_tgt m sched_src sched_tgt
         t_src t_tgt f candidates Helig Hcmp.
  unfold choose_min_metric.
  rewrite
    (filter_map_ext
       f
       (fun j => eligibleb jobs_src m sched_src j t_src)
       (fun j => eligibleb jobs_tgt m sched_tgt j t_tgt)
       candidates Helig).
  rewrite
    (min_metric_job_map_cmp
       metric_src metric_tgt f
       (filter (fun j => eligibleb jobs_src m sched_src j t_src)
          candidates)).
  - reflexivity.
  - intros j1 j2 Hin1 Hin2.
    apply filter_In in Hin1 as [Hin1 Helig1].
    apply filter_In in Hin2 as [Hin2 Helig2].
    exact (Hcmp j1 j2 Hin1 Hin2 Helig1 Helig2).
Qed.

Lemma candidates_of_agrees_before :
  forall J candidates_of
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs s1 s2 t,
    agrees_before s1 s2 t ->
    candidates_of jobs 1 s1 t = candidates_of jobs 1 s2 t.
Proof.
  intros J candidates_of cand_spec jobs s1 s2 t Hagree.
  destruct cand_spec as [_ _ Hpx].
  exact (Hpx jobs 1 s1 s2 t Hagree).
Qed.
