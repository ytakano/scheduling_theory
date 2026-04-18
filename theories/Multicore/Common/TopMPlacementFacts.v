From Stdlib Require Import List Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.TopMInterface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.TopMSchedulerBridge.
From RocqSched Require Import Multicore.Common.MultiCoreBase.
From RocqSched Require Import Multicore.Common.Admissibility.
From RocqSched Require Import Multicore.Common.PlacementFacts.

Record TopMPlacementSpec
    (adm : admissible_cpu)
    (spec : GenericTopMSchedulingAlgorithm)
    (candidates_of : CandidateSource) : Prop := {
  top_m_position_admissible :
    forall jobs m sched t c j,
      c < m ->
      nth_error
        (choose_top_m spec jobs m sched t
           (candidates_of jobs m sched t)) c = Some j ->
      adm j c
}.

Lemma top_m_algorithm_respects_admissibility :
  forall adm spec candidates_of jobs m sched,
    TopMPlacementSpec adm spec candidates_of ->
    scheduler_rel (top_m_algorithm_schedule spec candidates_of) jobs m sched ->
    schedule_respects_admissibility adm m sched.
Proof.
  intros adm spec candidates_of jobs m sched Hplace Hrel j t c Hlt Hrun.
  destruct Hplace as [Hnth].
  pose proof Hlt as Hlt_bool.
  pose proof (top_m_algorithm_eq_cpu spec candidates_of jobs m sched t c Hrel) as Heq.
  apply Nat.ltb_lt in Hlt_bool.
  rewrite Hlt_bool in Heq. simpl in Heq.
  rewrite Hrun in Heq.
  symmetry in Heq.
  exact (Hnth jobs m sched t c j Hlt Heq).
Qed.

Lemma all_cpus_top_m_placement_spec :
  forall spec candidates_of,
    TopMPlacementSpec all_cpus_admissible spec candidates_of.
Proof.
  intros spec candidates_of.
  constructor.
  intros jobs m sched t c j _ _.
  exact I.
Qed.
