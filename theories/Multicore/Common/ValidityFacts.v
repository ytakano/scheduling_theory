From Stdlib Require Import Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.TopMInterface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.TopMSchedulerBridge.
From RocqSched Require Import Multicore.Common.MultiCoreBase.
From RocqSched Require Import Multicore.Common.AdmissibleCandidateSource.
From RocqSched Require Import Multicore.Common.TopMAdmissibilityBridge.

(** Public downstream theorem layer:
    - bundled semantic validity for multicore clients
    - generic top-`m` construction of the validity bundle
    - thin bridge from the bundle to the current set-level top-`m` boundary *)

Record multicore_semantic_validity
    (jobs : JobId -> Job) (m : nat) (sched : Schedule) : Prop := {
  msv_valid : valid_schedule jobs m sched;
  msv_no_duplication : no_duplication m sched;
  msv_idle_outside_range :
    forall t c, m <= c -> sched t c = None;
  msv_running_eligible :
    forall j t, running_set_at m sched t j -> eligible jobs m sched j t
}.

Lemma top_m_algorithm_semantic_validity :
  forall spec candidates_of jobs m sched,
    scheduler_rel (top_m_algorithm_schedule spec candidates_of) jobs m sched ->
    multicore_semantic_validity jobs m sched.
Proof.
  intros spec candidates_of jobs m sched Hrel.
  constructor.
  - apply (top_m_algorithm_valid spec candidates_of jobs m sched Hrel).
  - apply (top_m_algorithm_no_duplication spec candidates_of jobs m sched Hrel).
  - intros t c Hge.
    apply (top_m_algorithm_idle_outside_range spec candidates_of jobs m sched t c Hrel Hge).
  - intros j t [c [Hlt Hrun]].
    pose proof (top_m_algorithm_valid spec candidates_of jobs m sched Hrel) as Hvalid.
    exact (Hvalid j t c Hlt Hrun).
Qed.

Lemma top_m_algorithm_semantic_validity_selected_from_subset_eligible :
  forall J spec candidates_of jobs m sched t,
    CandidateSourceSpec J candidates_of ->
    scheduler_rel (top_m_algorithm_schedule spec candidates_of) jobs m sched ->
    multicore_semantic_validity jobs m sched /\
    top_m_selected_from (subset_eligible_at J jobs m sched t) m sched t.
Proof.
  intros J spec candidates_of jobs m sched t Hcand Hrel.
  split.
  - apply (top_m_algorithm_semantic_validity spec candidates_of jobs m sched Hrel).
  - apply (top_m_algorithm_selected_from_subset_eligible
             J spec candidates_of jobs m sched t Hcand Hrel).
Qed.
