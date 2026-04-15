From Stdlib Require Import Arith Arith.PeanoNat Lia List.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Semantics.ScheduleLemmas.ScheduleFacts.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Analysis.Common.WorkloadAggregation.
From RocqSched Require Import Analysis.Multicore.ProcessorSupply.
From RocqSched Require Import Analysis.Multicore.Interference.
From RocqSched Require Import Multicore.Common.Admissibility.
From RocqSched Require Import Multicore.Common.AdmissibleCandidateSource.
From RocqSched Require Import Multicore.Common.CompletionFacts.
From RocqSched Require Import Multicore.Common.MultiCoreBase.
From RocqSched Require Import Multicore.Common.ServiceFacts.
From RocqSched Require Import Multicore.Global.GlobalEntryPoints.

Import ListNotations.

(** Public downstream theorems in this file:
    - `total_service_between_list_le_total_job_cost`
    - `covering_list_full_supply_implies_total_service_eq_capacity`
    - workload-gap wrappers for global EDF / LLF

    The remaining lemmas normalize interval non-running and list structure so
    the public theorems stay at the analysis-facing abstraction layer. *)

Lemma eligible_implies_positive_cost :
  forall jobs m sched j t,
    eligible jobs m sched j t ->
    0 < job_cost (jobs j).
Proof.
  intros jobs m sched j t Helig.
  rewrite eligible_iff_released_and_service_sum_lt_cost in Helig.
  lia.
Qed.

Lemma service_between_zero_if_not_running :
  forall m sched j t1 t2,
    t1 <= t2 ->
    (forall t, t1 <= t < t2 -> ~ running m sched j t) ->
    service_between m sched j t1 t2 = 0.
Proof.
  intros m sched j t1 t2 Hle Hnotrun.
  remember (t2 - t1) as len eqn:Hlen.
  revert t1 t2 Hle Hlen Hnotrun.
  induction len as [|len IH]; intros t1 t2 Hle Hlen Hnotrun.
  - assert (t1 = t2) by lia.
    subst t2.
    apply service_between_refl.
  - assert (Ht1t2 : t1 < t2) by lia.
    destruct (Nat.eq_dec t2 (S t1)) as [-> | Hneq].
    + rewrite service_between_single_slot_eq_cpu_count.
      destruct (Nat.eq_dec (cpu_count m sched j t1) 0) as [Hzero | Hnz].
      * exact Hzero.
      * exfalso.
        apply (Hnotrun t1 ltac:(lia)).
        apply cpu_count_nonzero_iff_executed.
        exact Hnz.
    + assert (Hlen' : len = t2 - S t1) by lia.
      rewrite (service_between_split m sched j t1 (S t1) t2) by lia.
      rewrite service_between_single_slot_eq_cpu_count.
      assert (Hzero : cpu_count m sched j t1 = 0).
      { destruct (Nat.eq_dec (cpu_count m sched j t1) 0) as [Hzero | Hnz];
          [exact Hzero |].
        exfalso.
        apply (Hnotrun t1 ltac:(lia)).
        apply cpu_count_nonzero_iff_executed.
        exact Hnz.
      }
      rewrite Hzero.
      rewrite (IH (S t1) t2).
      lia.
      * lia.
      * exact Hlen'.
      * intros t Hrange.
        apply Hnotrun.
        lia.
Qed.

Lemma nodup_app_cons_implies_nodup_app :
  forall (l1 l2 : list JobId) (j : JobId),
    NoDup (l1 ++ j :: l2) ->
    NoDup (l1 ++ l2).
Proof.
  induction l1 as [|x l1 IH]; intros l2 j Hnodup.
  - simpl in *.
    inversion Hnodup; subst.
    exact H2.
  - simpl in Hnodup.
    inversion Hnodup as [|x' l' Hnotin Htail]; subst x' l'.
    simpl.
    constructor.
    + intro Hin.
      apply Hnotin.
      apply in_app_iff in Hin.
      apply in_app_iff.
      destruct Hin as [Hin | Hin].
      * left. exact Hin.
      * right. right. exact Hin.
    + apply (IH l2 j).
      exact Htail.
Qed.

Lemma total_service_between_list_le_total_job_cost :
  forall jobs m sched l t1 t2,
    valid_schedule jobs m sched ->
    no_duplication m sched ->
    t1 <= t2 ->
    total_service_between_list m sched l t1 t2 <= total_job_cost jobs l.
Proof.
  intros jobs m sched l t1 t2 Hvalid Hnd Hle.
  induction l as [|j l IH]; simpl.
  - lia.
  - pose proof
      (valid_no_duplication_service_between_le_cost jobs m sched j t1 t2 Hvalid Hnd Hle)
      as Hhead.
    lia.
Qed.

Lemma covering_list_full_supply_implies_total_service_eq_capacity :
  forall m sched l t1 t2,
    no_duplication m sched ->
    NoDup l ->
    t1 <= t2 ->
    (forall t, t1 <= t < t2 -> covers_running_jobs m sched l t) ->
    total_cpu_service_between m sched t1 t2 = m * (t2 - t1) ->
    total_service_between_list m sched l t1 t2 = m * (t2 - t1).
Proof.
  intros m sched l t1 t2 Hnd Hnodup Hle Hcover Hsupply.
  rewrite <- Hsupply.
  symmetry.
  apply total_service_between_list_covers_total_cpu_supply; assumption.
Qed.

Lemma covering_list_not_running_job_implies_strict_workload_gap :
  forall jobs m sched l1 l2 j t1 t2,
    valid_schedule jobs m sched ->
    no_duplication m sched ->
    NoDup (l1 ++ j :: l2) ->
    t1 < t2 ->
    (forall t, t1 <= t < t2 -> ~ running m sched j t) ->
    (forall t, t1 <= t < t2 -> covers_running_jobs m sched (l1 ++ l2) t) ->
    total_cpu_service_between m sched t1 t2 = m * (t2 - t1) ->
    eligible jobs m sched j t1 ->
    m * (t2 - t1) < total_job_cost jobs (l1 ++ j :: l2).
Proof.
  intros jobs m sched l1 l2 j t1 t2 Hvalid Hnd Hnodup Hlt Hnotrun Hcover
         Hsupply Helig.
  assert (Hnodup_cover : NoDup (l1 ++ l2)).
  { eapply nodup_app_cons_implies_nodup_app; eauto. }
  assert (Hcap :
    total_service_between_list m sched (l1 ++ l2) t1 t2 = m * (t2 - t1)).
  { eapply covering_list_full_supply_implies_total_service_eq_capacity; eauto.
    lia.
  }
  assert (Hmiss : service_between m sched j t1 t2 < job_cost (jobs j)).
  { rewrite service_between_zero_if_not_running by (lia || exact Hnotrun).
    apply (eligible_implies_positive_cost jobs m sched j t1).
    exact Helig.
  }
  assert (Hle1 :
    total_service_between_list m sched l1 t1 t2 <= total_job_cost jobs l1).
  { eapply total_service_between_list_le_total_job_cost; eauto. lia. }
  assert (Hle2 :
    total_service_between_list m sched l2 t1 t2 <= total_job_cost jobs l2).
  { eapply total_service_between_list_le_total_job_cost; eauto. lia. }
  assert (Hstrict :
    total_service_between_list m sched (l1 ++ j :: l2) t1 t2 <
    total_job_cost jobs (l1 ++ j :: l2)).
  { eapply total_service_between_list_lt_total_job_cost_if_one_job_misses; eauto.
    lia.
  }
  assert (Hsum :
    total_service_between_list m sched (l1 ++ j :: l2) t1 t2 =
    total_service_between_list m sched (l1 ++ l2) t1 t2 +
    service_between m sched j t1 t2).
  { rewrite (total_service_between_list_app m sched l1 (j :: l2) t1 t2).
    rewrite (total_service_between_list_app m sched l1 l2 t1 t2).
    simpl.
    lia.
  }
  rewrite Hsum in Hstrict.
  rewrite Hcap in Hstrict.
  lia.
Qed.

Lemma global_edf_not_running_admissible_job_interval_implies_workload_gap :
  forall adm J candidates_of jobs m sched t1 t2 j l1 l2,
    AdmissibleCandidateSourceSpec adm J candidates_of ->
    scheduler_rel (global_edf_scheduler candidates_of) jobs m sched ->
    J j ->
    NoDup (l1 ++ j :: l2) ->
    t1 < t2 ->
    (forall t, t1 <= t < t2 ->
      admissible_somewhere adm jobs m sched j t /\ ~ running m sched j t) ->
    (forall t, t1 <= t < t2 -> covers_running_jobs m sched (l1 ++ l2) t) ->
    m * (t2 - t1) < total_job_cost jobs (l1 ++ j :: l2).
Proof.
  intros adm J candidates_of jobs m sched t1 t2 j l1 l2
         Hcand Hrel Hj Hnodup Hlt Hinterval Hcover.
  eapply covering_list_not_running_job_implies_strict_workload_gap.
  - apply (global_edf_valid candidates_of jobs m sched Hrel).
  - apply (global_edf_no_duplication candidates_of jobs m sched Hrel).
  - exact Hnodup.
  - exact Hlt.
  - intros t Hrange.
    exact (proj2 (Hinterval t Hrange)).
  - exact Hcover.
  - eapply (global_edf_not_running_admissible_job_interval_implies_full_supply
              adm J candidates_of jobs m sched t1 t2 j); eauto.
  - apply (admissible_somewhere_implies_eligible adm jobs m sched j t1).
    exact (proj1 (Hinterval t1 ltac:(lia))).
Qed.

Lemma global_edf_not_running_eligible_job_interval_implies_workload_gap :
  forall J candidates_of jobs m sched t1 t2 j l1 l2,
    CandidateSourceSpec J candidates_of ->
    scheduler_rel (global_edf_scheduler candidates_of) jobs m sched ->
    J j ->
    NoDup (l1 ++ j :: l2) ->
    t1 < t2 ->
    (forall t, t1 <= t < t2 ->
      eligible jobs m sched j t /\ ~ running m sched j t) ->
    (forall t, t1 <= t < t2 -> covers_running_jobs m sched (l1 ++ l2) t) ->
    m * (t2 - t1) < total_job_cost jobs (l1 ++ j :: l2).
Proof.
  intros J candidates_of jobs m sched t1 t2 j l1 l2
         Hcand Hrel Hj Hnodup Hlt Hinterval Hcover.
  eapply covering_list_not_running_job_implies_strict_workload_gap.
  - apply (global_edf_valid candidates_of jobs m sched Hrel).
  - apply (global_edf_no_duplication candidates_of jobs m sched Hrel).
  - exact Hnodup.
  - exact Hlt.
  - intros t Hrange.
    exact (proj2 (Hinterval t Hrange)).
  - exact Hcover.
  - eapply (global_edf_not_running_eligible_job_interval_implies_full_supply
              J candidates_of jobs m sched t1 t2 j); eauto.
  - exact (proj1 (Hinterval t1 ltac:(lia))).
Qed.

Lemma global_llf_not_running_admissible_job_interval_implies_workload_gap :
  forall adm J candidates_of jobs m sched t1 t2 j l1 l2,
    AdmissibleCandidateSourceSpec adm J candidates_of ->
    scheduler_rel (global_llf_scheduler candidates_of) jobs m sched ->
    J j ->
    NoDup (l1 ++ j :: l2) ->
    t1 < t2 ->
    (forall t, t1 <= t < t2 ->
      admissible_somewhere adm jobs m sched j t /\ ~ running m sched j t) ->
    (forall t, t1 <= t < t2 -> covers_running_jobs m sched (l1 ++ l2) t) ->
    m * (t2 - t1) < total_job_cost jobs (l1 ++ j :: l2).
Proof.
  intros adm J candidates_of jobs m sched t1 t2 j l1 l2
         Hcand Hrel Hj Hnodup Hlt Hinterval Hcover.
  eapply covering_list_not_running_job_implies_strict_workload_gap.
  - apply (global_llf_valid candidates_of jobs m sched Hrel).
  - apply (global_llf_no_duplication candidates_of jobs m sched Hrel).
  - exact Hnodup.
  - exact Hlt.
  - intros t Hrange.
    exact (proj2 (Hinterval t Hrange)).
  - exact Hcover.
  - eapply (global_llf_not_running_admissible_job_interval_implies_full_supply
              adm J candidates_of jobs m sched t1 t2 j); eauto.
  - apply (admissible_somewhere_implies_eligible adm jobs m sched j t1).
    exact (proj1 (Hinterval t1 ltac:(lia))).
Qed.

Lemma global_llf_not_running_eligible_job_interval_implies_workload_gap :
  forall J candidates_of jobs m sched t1 t2 j l1 l2,
    CandidateSourceSpec J candidates_of ->
    scheduler_rel (global_llf_scheduler candidates_of) jobs m sched ->
    0 < m ->
    J j ->
    NoDup (l1 ++ j :: l2) ->
    t1 < t2 ->
    (forall t, t1 <= t < t2 ->
      eligible jobs m sched j t /\ ~ running m sched j t) ->
    (forall t, t1 <= t < t2 -> covers_running_jobs m sched (l1 ++ l2) t) ->
    m * (t2 - t1) < total_job_cost jobs (l1 ++ j :: l2).
Proof.
  intros J candidates_of jobs m sched t1 t2 j l1 l2
         Hcand Hrel Hm Hj Hnodup Hlt Hinterval Hcover.
  eapply covering_list_not_running_job_implies_strict_workload_gap.
  - apply (global_llf_valid candidates_of jobs m sched Hrel).
  - apply (global_llf_no_duplication candidates_of jobs m sched Hrel).
  - exact Hnodup.
  - exact Hlt.
  - intros t Hrange.
    exact (proj2 (Hinterval t Hrange)).
  - exact Hcover.
  - eapply (global_llf_not_running_eligible_job_interval_implies_full_supply
              J candidates_of jobs m sched t1 t2 j); eauto.
  - exact (proj1 (Hinterval t1 ltac:(lia))).
Qed.
