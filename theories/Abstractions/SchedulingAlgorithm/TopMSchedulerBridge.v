(* TopMSchedulerBridge.v
   Lifts a GenericTopMSchedulingAlgorithm into a Scheduler record.

   This file keeps the bridge definition and abstraction-level consequences.
   Multicore-specific facts are separated into
   Multicore/Common/TopMSchedulerBridgeFacts.v.
*)

From Stdlib Require Import List Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.TopMInterface.
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

Definition top_m_algorithm_scheduler_on
    (J : JobId -> Prop)
    (spec : GenericTopMSchedulingAlgorithm)
    (candidates_of : CandidateSource)
    (_ : CandidateSourceSpec J candidates_of)
    : Scheduler :=
  top_m_algorithm_schedule spec candidates_of.

(* ===== Helper lemma ===== *)

Lemma nth_error_some_in :
  forall (l : list JobId) n j,
    nth_error l n = Some j ->
    In j l.
Proof.
  intros l n j H.
  exact (@nth_error_In JobId l n j H).
Qed.

Lemma in_nth_error_exists :
  forall (l : list JobId) j,
    In j l ->
    exists n, nth_error l n = Some j.
Proof.
  intros l j Hin.
  apply In_nth_error in Hin.
  destruct Hin as [n Hnth].
  exists n. exact Hnth.
Qed.

Lemma nth_error_some_lt_length :
  forall (l : list JobId) n j,
    nth_error l n = Some j ->
    n < length l.
Proof.
  intros l n j Hnth.
  apply nth_error_Some.
  rewrite Hnth. discriminate.
Qed.

Lemma nth_error_none_of_idle_cpu :
  forall spec candidates_of jobs m sched t c,
    scheduler_rel (top_m_algorithm_schedule spec candidates_of) jobs m sched ->
    c < m ->
    sched t c = None ->
    nth_error (choose_top_m spec jobs m sched t (candidates_of jobs m sched t)) c = None.
Proof.
  intros spec candidates_of jobs m sched t c Hrel Hlt Hidle.
  pose proof (Hrel t c) as Heq.
  apply Nat.ltb_lt in Hlt.
  rewrite Hlt in Heq. simpl in Heq.
  rewrite Hidle in Heq.
  symmetry. exact Heq.
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

Lemma top_m_algorithm_in_subset :
  forall J spec candidates_of jobs m sched t c j,
    CandidateSourceSpec J candidates_of ->
    scheduler_rel (top_m_algorithm_schedule spec candidates_of) jobs m sched ->
    c < m ->
    sched t c = Some j ->
    J j.
Proof.
  intros J spec candidates_of jobs m sched t c j Hcand Hrel Hlt Hrun.
  destruct Hcand as [Hsound _ _].
  pose proof (top_m_algorithm_eq_cpu spec candidates_of jobs m sched t c Hrel) as Heq.
  apply Nat.ltb_lt in Hlt.
  rewrite Hlt in Heq. simpl in Heq.
  rewrite Hrun in Heq.
  symmetry in Heq.
  apply (Hsound jobs m sched t j).
  eapply choose_top_m_in_candidates.
  exact (nth_error_some_in _ _ _ Heq).
Qed.

Lemma top_m_algorithm_schedulable_by_on_intro :
  forall J spec candidates_of cand_spec jobs m sched,
    scheduler_rel
      (top_m_algorithm_scheduler_on J spec candidates_of cand_spec)
      jobs m sched ->
    feasible_schedule_on J jobs m sched ->
    schedulable_by_on
      J
      (top_m_algorithm_scheduler_on J spec candidates_of cand_spec)
      jobs m.
Proof.
  intros J spec candidates_of cand_spec jobs m sched Hrel Hfeas.
  apply (schedulable_by_on_intro
           J
           (top_m_algorithm_scheduler_on J spec candidates_of cand_spec)
           jobs m sched).
  - exact Hrel.
  - exact (top_m_algorithm_valid spec candidates_of jobs m sched Hrel).
  - exact Hfeas.
Qed.
