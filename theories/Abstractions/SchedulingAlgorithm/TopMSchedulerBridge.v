(* TopMSchedulerBridge.v
   Lifts a GenericTopMSchedulingAlgorithm into a Scheduler record.

   The bridge assigns CPU c the c-th job chosen by the algorithm (via
   nth_error), so CPUs beyond the chosen list are idle.

   Main results
   ------------
   top_m_algorithm_eq_cpu            : scheduler_rel unfolds to nth_error lookup
   top_m_algorithm_valid             : scheduler_rel -> valid_schedule
   top_m_algorithm_idle_outside_range: CPUs >= m are always idle
   top_m_algorithm_no_duplication    : scheduler_rel -> no_duplication
*)

From Stdlib Require Import List Arith Arith.PeanoNat Lia.
From SchedulingTheory Require Import Foundation.Base.
From SchedulingTheory Require Import Semantics.Schedule.
From SchedulingTheory Require Import Multicore.Common.MultiCoreBase.
From SchedulingTheory Require Import Abstractions.Scheduler.Interface.
From SchedulingTheory Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From SchedulingTheory Require Import Abstractions.SchedulingAlgorithm.TopMInterface.
Import ListNotations.

(* ===== Bridge definition ===== *)

(** Lift a top-m algorithm to a Scheduler.
    CPU c runs the c-th job from the algorithm's chosen list (0-indexed).
    CPUs outside [0, m) are always idle. *)
Definition top_m_algorithm_schedule
    (spec : GenericTopMSchedulingAlgorithm)
    (candidates_of : CandidateSource)
    : Scheduler :=
  mkScheduler (fun jobs m sched =>
    forall t c,
      sched t c =
        if c <? m then
          nth_error (choose_top_m spec jobs m sched t
                       (candidates_of jobs m sched t)) c
        else
          None).

(* ===== Helper lemma ===== *)

Lemma nth_error_some_in :
  forall (l : list JobId) n j,
    nth_error l n = Some j ->
    In j l.
Proof.
  intros l n j H.
  exact (@nth_error_In JobId l n j H).
Qed.

(* ===== Scheduler relation unfolding ===== *)

Lemma top_m_algorithm_eq_cpu :
  forall spec candidates_of jobs m sched t c,
    scheduler_rel (top_m_algorithm_schedule spec candidates_of) jobs m sched ->
    sched t c =
      if c <? m then
        nth_error (choose_top_m spec jobs m sched t
                     (candidates_of jobs m sched t)) c
      else None.
Proof.
  intros spec candidates_of jobs m sched t c Hrel.
  exact (Hrel t c).
Qed.

(* ===== Main validity theorem ===== *)

Lemma top_m_algorithm_valid :
  forall spec candidates_of jobs m sched,
    scheduler_rel (top_m_algorithm_schedule spec candidates_of) jobs m sched ->
    valid_schedule jobs m sched.
Proof.
  intros spec cands jobs m sched Hrel.
  unfold valid_schedule.
  intros j t c Hlt Hrun.
  pose proof (Hrel t c) as Heq.
  apply Nat.ltb_lt in Hlt.
  rewrite Hlt in Heq. simpl in Heq.
  rewrite Hrun in Heq.
  symmetry in Heq.
  apply nth_error_some_in in Heq.
  exact (choose_top_m_eligible spec jobs m sched t (cands jobs m sched t) j Heq).
Qed.

(* ===== Idle outside CPU range ===== *)

Lemma top_m_algorithm_idle_outside_range :
  forall spec candidates_of jobs m sched t c,
    scheduler_rel (top_m_algorithm_schedule spec candidates_of) jobs m sched ->
    m <= c ->
    sched t c = None.
Proof.
  intros spec cands jobs m sched t c Hrel Hge.
  pose proof (Hrel t c) as Heq.
  apply Nat.ltb_ge in Hge.
  rewrite Hge in Heq. simpl in Heq.
  exact Heq.
Qed.

(* ===== No duplication ===== *)

(** Helper: in a NoDup list, two positions holding the same element are equal. *)
Lemma nth_error_nodup_inj :
  forall (l : list JobId) i j x,
    NoDup l ->
    nth_error l i = Some x ->
    nth_error l j = Some x ->
    i = j.
Proof.
  intros l i j x Hnd.
  rewrite NoDup_nth_error in Hnd.
  intros Hi Hj.
  apply Hnd.
  - apply nth_error_Some. rewrite Hi. discriminate.
  - rewrite Hi, Hj. reflexivity.
Qed.

(** If two CPUs run the same job, they must be the same CPU. *)
Lemma top_m_algorithm_no_duplication :
  forall spec candidates_of jobs m sched,
    scheduler_rel (top_m_algorithm_schedule spec candidates_of) jobs m sched ->
    no_duplication m sched.
Proof.
  intros spec cands jobs m sched Hrel.
  unfold no_duplication, sequential_jobs.
  intros j t c1 c2 Hlt1 Hlt2 Hsome1 Hsome2.
  pose proof (Hrel t c1) as Heq1.
  pose proof (Hrel t c2) as Heq2.
  apply Nat.ltb_lt in Hlt1.
  apply Nat.ltb_lt in Hlt2.
  rewrite Hlt1 in Heq1. simpl in Heq1.
  rewrite Hlt2 in Heq2. simpl in Heq2.
  rewrite Hsome1 in Heq1.
  rewrite Hsome2 in Heq2.
  set (chosen := choose_top_m spec jobs m sched t (cands jobs m sched t)) in *.
  symmetry in Heq1, Heq2.
  pose proof (choose_top_m_nodup spec jobs m sched t (cands jobs m sched t)) as Hnodup.
  fold chosen in Hnodup.
  exact (nth_error_nodup_inj chosen c1 c2 j Hnodup Heq1 Heq2).
Qed.
