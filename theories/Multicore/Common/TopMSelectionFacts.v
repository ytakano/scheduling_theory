From Stdlib Require Import Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.TopMInterface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.TopMSchedulerBridge.
From RocqSched Require Import Multicore.Common.MultiCoreBase.
From RocqSched Require Import Multicore.Common.Admissibility.
From RocqSched Require Import Multicore.Common.AdmissibleCandidateSource.
From RocqSched Require Import Multicore.Common.ServiceFacts.
From RocqSched Require Import Multicore.Common.TopMAdmissibilityBridge.

(** Public downstream theorem layer:
    - generic consequences of `top_m_selected_from`
    - interval full-supply consequences for eligible/admissible clients
    - missing-job to busy-machine bridges at the set-level top-`m` boundary *)

Lemma top_m_selected_from_missing_implies_all_cpus_busy :
  forall S m sched t j,
    top_m_selected_from S m sched t ->
    S j ->
    ~ running m sched j t ->
    forall c, c < m -> cpu_busy sched t c.
Proof.
  intros S m sched t j Hsel HS Hnrun c Hc.
  exact (top_m_selected_missing_implies_machine_full _ _ _ _ Hsel j HS Hnrun c Hc).
Qed.

Lemma top_m_selected_from_interval_implies_full_supply :
  forall S m sched t1 t2 j,
    (forall t, t1 <= t < t2 -> S j /\ ~ running m sched j t) ->
    (forall t, t1 <= t < t2 -> top_m_selected_from S m sched t) ->
    total_cpu_service_between m sched t1 t2 = m * (t2 - t1).
Proof.
  intros S m sched t1 t2 j Hinterval Hsel.
  apply total_cpu_service_between_eq_capacity_if_all_cpus_busy.
  intros t Hrange c Hc.
  destruct (Hinterval t Hrange) as [HS Hnrun].
  eapply top_m_selected_from_missing_implies_all_cpus_busy; eauto.
Qed.

Lemma top_m_selected_from_subset_eligible_interval_implies_full_supply :
  forall J jobs m sched t1 t2 j,
    J j ->
    (forall t, t1 <= t < t2 ->
      eligible jobs m sched j t /\ ~ running m sched j t) ->
    (forall t, t1 <= t < t2 ->
      top_m_selected_from (subset_eligible_at J jobs m sched t) m sched t) ->
    total_cpu_service_between m sched t1 t2 = m * (t2 - t1).
Proof.
  intros J jobs m sched t1 t2 j HJ Hinterval Hsel.
  apply total_cpu_service_between_eq_capacity_if_all_cpus_busy.
  intros t Hrange c Hc.
  destruct (Hinterval t Hrange) as [Helig Hnrun].
  pose proof (Hsel t Hrange) as Hsel_t.
  exact
    (top_m_selected_from_missing_implies_all_cpus_busy
       _ _ _ _ _ Hsel_t (conj HJ Helig) Hnrun c Hc).
Qed.

Lemma top_m_selected_from_subset_admissible_somewhere_interval_implies_full_supply :
  forall adm J jobs m sched t1 t2 j,
    J j ->
    (forall t, t1 <= t < t2 ->
      admissible_somewhere adm jobs m sched j t /\ ~ running m sched j t) ->
    (forall t, t1 <= t < t2 ->
      top_m_selected_from
        (subset_admissible_somewhere_at adm J jobs m sched t) m sched t) ->
    total_cpu_service_between m sched t1 t2 = m * (t2 - t1).
Proof.
  intros adm J jobs m sched t1 t2 j HJ Hinterval Hsel.
  apply total_cpu_service_between_eq_capacity_if_all_cpus_busy.
  intros t Hrange c Hc.
  destruct (Hinterval t Hrange) as [Hadm Hnrun].
  pose proof (Hsel t Hrange) as Hsel_t.
  exact
    (top_m_selected_from_missing_implies_all_cpus_busy
       _ _ _ _ _ Hsel_t (conj HJ Hadm) Hnrun c Hc).
Qed.

Lemma top_m_algorithm_not_running_subset_eligible_interval_implies_full_supply :
  forall J spec candidates_of jobs m sched t1 t2 j,
    CandidateSourceSpec J candidates_of ->
    scheduler_rel (top_m_algorithm_schedule spec candidates_of) jobs m sched ->
    J j ->
    (forall t, t1 <= t < t2 ->
      eligible jobs m sched j t /\ ~ running m sched j t) ->
    total_cpu_service_between m sched t1 t2 = m * (t2 - t1).
Proof.
  intros J spec candidates_of jobs m sched t1 t2 j Hcand Hrel HJ Hinterval.
  eapply top_m_selected_from_subset_eligible_interval_implies_full_supply; eauto.
  intros t Hrange.
  eapply top_m_algorithm_selected_from_subset_eligible; eauto.
Qed.

Lemma top_m_algorithm_not_running_subset_admissible_somewhere_interval_implies_full_supply_gen :
  forall adm J spec candidates_of jobs m sched t1 t2 j,
    AdmissibleCandidateSourceSpec adm J candidates_of ->
    scheduler_rel (top_m_algorithm_schedule spec candidates_of) jobs m sched ->
    J j ->
    (forall t, t1 <= t < t2 ->
      admissible_somewhere adm jobs m sched j t /\ ~ running m sched j t) ->
    total_cpu_service_between m sched t1 t2 = m * (t2 - t1).
Proof.
  intros adm J spec candidates_of jobs m sched t1 t2 j
         Hcand Hrel HJ Hinterval.
  apply total_cpu_service_between_eq_capacity_if_all_cpus_busy.
  intros t Hrange c Hc.
  destruct (Hinterval t Hrange) as [Hadm Hnrun].
  eapply top_m_algorithm_not_running_subset_admissible_somewhere_implies_all_cpus_busy_gen;
    eauto.
Qed.
