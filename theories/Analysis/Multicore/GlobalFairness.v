From Stdlib Require Import Arith Arith.PeanoNat Lia List.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Analysis.Common.WorkloadAggregation.
From RocqSched Require Import Analysis.Multicore.Interference.
From RocqSched Require Import Analysis.Multicore.GlobalWorkloadAbsorption.
From RocqSched Require Import Multicore.Common.Admissibility.
From RocqSched Require Import Multicore.Common.AdmissibleCandidateSource.
From RocqSched Require Import Multicore.Global.GlobalEDF.
From RocqSched Require Import Multicore.Global.GlobalLLF.

Import ListNotations.

(** Public downstream theorems in this file:
    - contradiction wrappers that close workload-gap hooks against an explicit
      workload upper bound
    - first fairness client corollaries that recover a concrete running witness

    This file deliberately stays above `GlobalWorkloadAbsorption.v`: it does
    not re-prove interval supply facts, but packages them into client-facing
    fairness consequences. *)

Lemma running_dec :
  forall m sched j t,
    {running m sched j t} + {~ running m sched j t}.
Proof.
  induction m as [|m IH]; intros sched j t.
  - right.
    intros [c [Hlt _]].
    lia.
  - destruct (sched t m) as [j'|] eqn:Hsched.
    + destruct (Nat.eq_dec j' j) as [<-|Hneq].
      * left.
        exists m.
        split; [lia|exact Hsched].
      * destruct (IH sched j t) as [Hrun|Hnotrun].
        -- left.
           destruct Hrun as [c [Hlt Hrun]].
           exists c.
           split; [lia|exact Hrun].
        -- right.
           intros [c [Hlt Hrun]].
           destruct (Nat.eq_dec c m) as [->|Hneqc].
           ++ rewrite Hsched in Hrun.
              inversion Hrun; subst.
              contradiction.
           ++ apply Hnotrun.
              exists c.
              split; [lia|exact Hrun].
    + destruct (IH sched j t) as [Hrun|Hnotrun].
      * left.
        destruct Hrun as [c [Hlt Hrun]].
        exists c.
        split; [lia|exact Hrun].
      * right.
        intros [c [Hlt Hrun]].
        destruct (Nat.eq_dec c m) as [->|Hneqc].
        -- rewrite Hsched in Hrun.
           discriminate.
        -- apply Hnotrun.
           exists c.
           split; [lia|exact Hrun].
Qed.

Lemma running_somewhere_in_interval_dec :
  forall m sched j t1 len,
    {exists t, t1 <= t < t1 + len /\ running m sched j t} +
    {forall t, t1 <= t < t1 + len -> ~ running m sched j t}.
Proof.
  intros m sched j t1 len.
  revert t1.
  induction len as [|len IH]; intros t1.
  - right.
    intros t Hrange.
    lia.
  - destruct (running_dec m sched j t1) as [Hrun|Hnotrun].
    + left.
      exists t1.
      split; [lia|exact Hrun].
    + destruct (IH (S t1)) as [Hex|Hall].
      * left.
        destruct Hex as [t [Hrange Hrun]].
        exists t.
        split; [lia|exact Hrun].
      * right.
        intros t Hrange.
        destruct (Nat.eq_dec t t1) as [->|Hneq].
        -- exact Hnotrun.
        -- apply Hall.
           lia.
Qed.

Lemma global_edf_not_running_admissible_job_interval_contradicts_workload_upper_bound :
  forall adm J candidates_of jobs m sched t1 t2 j l1 l2,
    AdmissibleCandidateSourceSpec adm J candidates_of ->
    scheduler_rel (global_edf_scheduler candidates_of) jobs m sched ->
    J j ->
    NoDup (l1 ++ j :: l2) ->
    t1 < t2 ->
    (forall t, t1 <= t < t2 ->
      admissible_somewhere adm jobs m sched j t /\ ~ running m sched j t) ->
    (forall t, t1 <= t < t2 -> covers_running_jobs m sched (l1 ++ l2) t) ->
    total_job_cost jobs (l1 ++ j :: l2) <= m * (t2 - t1) ->
    False.
Proof.
  intros adm J candidates_of jobs m sched t1 t2 j l1 l2
         Hcand Hrel Hj Hnodup Hlt Hinterval Hcover Hbound.
  pose proof
    (global_edf_not_running_admissible_job_interval_implies_workload_gap
       adm J candidates_of jobs m sched t1 t2 j l1 l2
       Hcand Hrel Hj Hnodup Hlt Hinterval Hcover) as Hgap.
  lia.
Qed.

Lemma global_edf_not_running_eligible_job_interval_contradicts_workload_upper_bound :
  forall J candidates_of jobs m sched t1 t2 j l1 l2,
    CandidateSourceSpec J candidates_of ->
    scheduler_rel (global_edf_scheduler candidates_of) jobs m sched ->
    J j ->
    NoDup (l1 ++ j :: l2) ->
    t1 < t2 ->
    (forall t, t1 <= t < t2 ->
      eligible jobs m sched j t /\ ~ running m sched j t) ->
    (forall t, t1 <= t < t2 -> covers_running_jobs m sched (l1 ++ l2) t) ->
    total_job_cost jobs (l1 ++ j :: l2) <= m * (t2 - t1) ->
    False.
Proof.
  intros J candidates_of jobs m sched t1 t2 j l1 l2
         Hcand Hrel Hj Hnodup Hlt Hinterval Hcover Hbound.
  pose proof
    (global_edf_not_running_eligible_job_interval_implies_workload_gap
       J candidates_of jobs m sched t1 t2 j l1 l2
       Hcand Hrel Hj Hnodup Hlt Hinterval Hcover) as Hgap.
  lia.
Qed.

Lemma global_llf_not_running_admissible_job_interval_contradicts_workload_upper_bound :
  forall adm J candidates_of jobs m sched t1 t2 j l1 l2,
    AdmissibleCandidateSourceSpec adm J candidates_of ->
    scheduler_rel (global_llf_scheduler candidates_of) jobs m sched ->
    0 < m ->
    J j ->
    NoDup (l1 ++ j :: l2) ->
    t1 < t2 ->
    (forall t, t1 <= t < t2 ->
      admissible_somewhere adm jobs m sched j t /\ ~ running m sched j t) ->
    (forall t, t1 <= t < t2 -> covers_running_jobs m sched (l1 ++ l2) t) ->
    total_job_cost jobs (l1 ++ j :: l2) <= m * (t2 - t1) ->
    False.
Proof.
  intros adm J candidates_of jobs m sched t1 t2 j l1 l2
         Hcand Hrel Hm Hj Hnodup Hlt Hinterval Hcover Hbound.
  pose proof
    (global_llf_not_running_admissible_job_interval_implies_workload_gap
       adm J candidates_of jobs m sched t1 t2 j l1 l2
       Hcand Hrel Hj Hnodup Hlt Hinterval Hcover) as Hgap.
  lia.
Qed.

Lemma global_llf_not_running_eligible_job_interval_contradicts_workload_upper_bound :
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
    total_job_cost jobs (l1 ++ j :: l2) <= m * (t2 - t1) ->
    False.
Proof.
  intros J candidates_of jobs m sched t1 t2 j l1 l2
         Hcand Hrel Hm Hj Hnodup Hlt Hinterval Hcover Hbound.
  pose proof
    (global_llf_not_running_eligible_job_interval_implies_workload_gap
       J candidates_of jobs m sched t1 t2 j l1 l2
       Hcand Hrel Hm Hj Hnodup Hlt Hinterval Hcover) as Hgap.
  lia.
Qed.

Lemma global_edf_persistently_admissible_job_must_run_in_interval :
  forall adm J candidates_of jobs m sched t1 t2 j l1 l2,
    AdmissibleCandidateSourceSpec adm J candidates_of ->
    scheduler_rel (global_edf_scheduler candidates_of) jobs m sched ->
    J j ->
    NoDup (l1 ++ j :: l2) ->
    t1 < t2 ->
    (forall t, t1 <= t < t2 -> admissible_somewhere adm jobs m sched j t) ->
    (forall t, t1 <= t < t2 ->
      ~ running m sched j t -> covers_running_jobs m sched (l1 ++ l2) t) ->
    total_job_cost jobs (l1 ++ j :: l2) <= m * (t2 - t1) ->
    exists t, t1 <= t < t2 /\ running m sched j t.
Proof.
  intros adm J candidates_of jobs m sched t1 t2 j l1 l2
         Hcand Hrel Hj Hnodup Hlt Hadm Hcover Hbound.
  destruct (running_somewhere_in_interval_dec m sched j t1 (t2 - t1))
    as [Hex|Hall].
  - destruct Hex as [t [Hrange Hrun]].
    exists t.
    assert (Heq : t1 + (t2 - t1) = t2) by lia.
    split.
    + rewrite <- Heq.
      exact Hrange.
    + exact Hrun.
  - assert (Hinterval :
        forall t, t1 <= t < t2 ->
          admissible_somewhere adm jobs m sched j t /\ ~ running m sched j t).
    { intros t Hrange.
      split.
      - apply Hadm.
        exact Hrange.
      - apply Hall.
        assert (t1 + (t2 - t1) = t2) by lia.
        lia.
    }
    assert (Hcover_interval :
      forall t, t1 <= t < t2 -> covers_running_jobs m sched (l1 ++ l2) t).
    { intros t Hrange.
      apply Hcover.
      - exact Hrange.
      - apply Hall.
        assert (t1 + (t2 - t1) = t2) by lia.
        lia.
    }
    exfalso.
    eapply global_edf_not_running_admissible_job_interval_contradicts_workload_upper_bound; eauto.
Qed.

Lemma global_edf_persistently_eligible_job_must_run_in_interval :
  forall J candidates_of jobs m sched t1 t2 j l1 l2,
    CandidateSourceSpec J candidates_of ->
    scheduler_rel (global_edf_scheduler candidates_of) jobs m sched ->
    J j ->
    NoDup (l1 ++ j :: l2) ->
    t1 < t2 ->
    (forall t, t1 <= t < t2 -> eligible jobs m sched j t) ->
    (forall t, t1 <= t < t2 ->
      ~ running m sched j t -> covers_running_jobs m sched (l1 ++ l2) t) ->
    total_job_cost jobs (l1 ++ j :: l2) <= m * (t2 - t1) ->
    exists t, t1 <= t < t2 /\ running m sched j t.
Proof.
  intros J candidates_of jobs m sched t1 t2 j l1 l2
         Hcand Hrel Hj Hnodup Hlt Helig Hcover Hbound.
  destruct (running_somewhere_in_interval_dec m sched j t1 (t2 - t1))
    as [Hex|Hall].
  - destruct Hex as [t [Hrange Hrun]].
    exists t.
    assert (Heq : t1 + (t2 - t1) = t2) by lia.
    split.
    + rewrite <- Heq.
      exact Hrange.
    + exact Hrun.
  - assert (Hinterval :
        forall t, t1 <= t < t2 ->
          eligible jobs m sched j t /\ ~ running m sched j t).
    { intros t Hrange.
      split.
      - apply Helig.
        exact Hrange.
      - apply Hall.
        assert (t1 + (t2 - t1) = t2) by lia.
        lia.
    }
    assert (Hcover_interval :
      forall t, t1 <= t < t2 -> covers_running_jobs m sched (l1 ++ l2) t).
    { intros t Hrange.
      apply Hcover.
      - exact Hrange.
      - apply Hall.
        assert (t1 + (t2 - t1) = t2) by lia.
        lia.
    }
    exfalso.
    eapply global_edf_not_running_eligible_job_interval_contradicts_workload_upper_bound; eauto.
Qed.

Lemma global_llf_persistently_admissible_job_must_run_in_interval :
  forall adm J candidates_of jobs m sched t1 t2 j l1 l2,
    AdmissibleCandidateSourceSpec adm J candidates_of ->
    scheduler_rel (global_llf_scheduler candidates_of) jobs m sched ->
    0 < m ->
    J j ->
    NoDup (l1 ++ j :: l2) ->
    t1 < t2 ->
    (forall t, t1 <= t < t2 -> admissible_somewhere adm jobs m sched j t) ->
    (forall t, t1 <= t < t2 ->
      ~ running m sched j t -> covers_running_jobs m sched (l1 ++ l2) t) ->
    total_job_cost jobs (l1 ++ j :: l2) <= m * (t2 - t1) ->
    exists t, t1 <= t < t2 /\ running m sched j t.
Proof.
  intros adm J candidates_of jobs m sched t1 t2 j l1 l2
         Hcand Hrel Hm Hj Hnodup Hlt Hadm Hcover Hbound.
  destruct (running_somewhere_in_interval_dec m sched j t1 (t2 - t1))
    as [Hex|Hall].
  - destruct Hex as [t [Hrange Hrun]].
    exists t.
    assert (Heq : t1 + (t2 - t1) = t2) by lia.
    split.
    + rewrite <- Heq.
      exact Hrange.
    + exact Hrun.
  - assert (Hinterval :
        forall t, t1 <= t < t2 ->
          admissible_somewhere adm jobs m sched j t /\ ~ running m sched j t).
    { intros t Hrange.
      split.
      - apply Hadm.
        exact Hrange.
      - apply Hall.
        assert (t1 + (t2 - t1) = t2) by lia.
        lia.
    }
    assert (Hcover_interval :
      forall t, t1 <= t < t2 -> covers_running_jobs m sched (l1 ++ l2) t).
    { intros t Hrange.
      apply Hcover.
      - exact Hrange.
      - apply Hall.
        assert (t1 + (t2 - t1) = t2) by lia.
        lia.
    }
    exfalso.
    eapply global_llf_not_running_admissible_job_interval_contradicts_workload_upper_bound; eauto.
Qed.

Lemma global_llf_persistently_eligible_job_must_run_in_interval :
  forall J candidates_of jobs m sched t1 t2 j l1 l2,
    CandidateSourceSpec J candidates_of ->
    scheduler_rel (global_llf_scheduler candidates_of) jobs m sched ->
    0 < m ->
    J j ->
    NoDup (l1 ++ j :: l2) ->
    t1 < t2 ->
    (forall t, t1 <= t < t2 -> eligible jobs m sched j t) ->
    (forall t, t1 <= t < t2 ->
      ~ running m sched j t -> covers_running_jobs m sched (l1 ++ l2) t) ->
    total_job_cost jobs (l1 ++ j :: l2) <= m * (t2 - t1) ->
    exists t, t1 <= t < t2 /\ running m sched j t.
Proof.
  intros J candidates_of jobs m sched t1 t2 j l1 l2
         Hcand Hrel Hm Hj Hnodup Hlt Helig Hcover Hbound.
  destruct (running_somewhere_in_interval_dec m sched j t1 (t2 - t1))
    as [Hex|Hall].
  - destruct Hex as [t [Hrange Hrun]].
    exists t.
    assert (Heq : t1 + (t2 - t1) = t2) by lia.
    split.
    + rewrite <- Heq.
      exact Hrange.
    + exact Hrun.
  - assert (Hinterval :
        forall t, t1 <= t < t2 ->
          eligible jobs m sched j t /\ ~ running m sched j t).
    { intros t Hrange.
      split.
      - apply Helig.
        exact Hrange.
      - apply Hall.
        assert (t1 + (t2 - t1) = t2) by lia.
        lia.
    }
    assert (Hcover_interval :
      forall t, t1 <= t < t2 -> covers_running_jobs m sched (l1 ++ l2) t).
    { intros t Hrange.
      apply Hcover.
      - exact Hrange.
      - apply Hall.
        assert (t1 + (t2 - t1) = t2) by lia.
        lia.
    }
    exfalso.
    eapply global_llf_not_running_eligible_job_interval_contradicts_workload_upper_bound; eauto.
Qed.
