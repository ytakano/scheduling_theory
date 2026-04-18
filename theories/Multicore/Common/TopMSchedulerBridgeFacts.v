From Stdlib Require Import List Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.TopMInterface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.TopMSchedulerBridge.
From RocqSched Require Import Multicore.Common.MultiCoreBase.
Import ListNotations.

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

Lemma top_m_algorithm_all_cpus_idle_if_no_subset_eligible :
  forall J spec candidates_of jobs m sched t,
    CandidateSourceSpec J candidates_of ->
    scheduler_rel (top_m_algorithm_schedule spec candidates_of) jobs m sched ->
    (forall j, J j -> ~ eligible jobs m sched j t) ->
    all_cpus_idle m sched t.
Proof.
  intros J spec candidates_of jobs m sched t Hcand Hrel Hnone.
  unfold all_cpus_idle, cpu_idle.
  intros c Hlt.
  destruct (sched t c) as [j|] eqn:Hcpu.
  - exfalso.
    pose proof (top_m_algorithm_in_subset J spec candidates_of jobs m sched t c j
                  Hcand Hrel Hlt Hcpu) as Hj.
    pose proof (top_m_algorithm_valid spec candidates_of jobs m sched Hrel) as Hvalid.
    pose proof (Hvalid j t c Hlt Hcpu) as Helig.
    exact (Hnone j Hj Helig).
  - reflexivity.
Qed.

Lemma top_m_algorithm_some_cpu_busy_if_subset_eligible :
  forall J spec candidates_of jobs m sched t,
    CandidateSourceSpec J candidates_of ->
    scheduler_rel (top_m_algorithm_schedule spec candidates_of) jobs m sched ->
    0 < m ->
    (exists j, J j /\ eligible jobs m sched j t) ->
    exists c, c < m /\ cpu_busy sched t c.
Proof.
  intros J spec candidates_of jobs m sched t Hcand Hrel Hm [j [HJ Helig]].
  destruct Hcand as [_ Hcomplete _].
  set (chosen := choose_top_m spec jobs m sched t (candidates_of jobs m sched t)).
  assert (Hincand : In j (candidates_of jobs m sched t)).
  { apply (Hcomplete jobs m sched t j HJ Helig). }
  destruct (in_dec Nat.eq_dec j chosen) as [Hin|Hnotin].
  - destruct (in_nth_error_exists chosen j Hin) as [c Hnth].
    exists c. split.
    + pose proof (nth_error_some_lt_length chosen c j Hnth) as Hclt.
      pose proof (choose_top_m_length_le_m spec jobs m sched t (candidates_of jobs m sched t))
        as Hlen.
      unfold chosen in Hclt.
      lia.
    + exists j.
      pose proof (top_m_algorithm_eq_cpu spec candidates_of jobs m sched t c Hrel) as Heq.
      assert (Hlt : c < m).
      { pose proof (nth_error_some_lt_length chosen c j Hnth) as Hclt.
        pose proof (choose_top_m_length_le_m spec jobs m sched t (candidates_of jobs m sched t))
          as Hlen.
        unfold chosen in Hclt.
        lia. }
      apply Nat.ltb_lt in Hlt.
      rewrite Hlt in Heq. simpl in Heq.
      fold chosen in Heq.
      rewrite Hnth in Heq.
      exact Heq.
  - assert (Hfull : length chosen = m).
    { unfold chosen.
      eapply choose_top_m_complete_if_room; eauto. }
    destruct chosen as [|j0 chosen'] eqn:Hchosen.
    + simpl in Hfull. lia.
    + exists 0. split.
      * exact Hm.
      * exists j0.
        pose proof (top_m_algorithm_eq_cpu spec candidates_of jobs m sched t 0 Hrel) as Heq.
        apply Nat.ltb_lt in Hm.
        rewrite Hm in Heq. simpl in Heq.
        fold chosen in Heq.
        rewrite Hchosen in Heq. simpl in Heq.
        exact Heq.
Qed.

Lemma top_m_algorithm_running_if_some_cpu_idle_and_subset_eligible :
  forall J spec candidates_of jobs m sched t j,
    CandidateSourceSpec J candidates_of ->
    scheduler_rel (top_m_algorithm_schedule spec candidates_of) jobs m sched ->
    some_cpu_idle m sched t ->
    J j ->
    eligible jobs m sched j t ->
    running m sched j t.
Proof.
  intros J spec candidates_of jobs m sched t j Hcand Hrel [c [Hclt Hidle]] HJ Helig.
  destruct Hcand as [_ Hcomplete _].
  set (chosen := choose_top_m spec jobs m sched t (candidates_of jobs m sched t)).
  assert (Hincand : In j (candidates_of jobs m sched t)).
  { apply (Hcomplete jobs m sched t j HJ Helig). }
  assert (Hin : In j chosen).
  { destruct (in_dec Nat.eq_dec j chosen) as [Hin|Hnotin].
    - exact Hin.
    - assert (Hfull : length chosen = m).
      { unfold chosen.
        eapply choose_top_m_complete_if_room; eauto. }
      pose proof (nth_error_none_of_idle_cpu spec candidates_of jobs m sched t c Hrel Hclt Hidle)
        as Hnthnone.
      fold chosen in Hnthnone.
      rewrite nth_error_None in Hnthnone.
      rewrite Hfull in Hnthnone.
      lia. }
  destruct (in_nth_error_exists chosen j Hin) as [c' Hnth].
  exists c'. split.
  - pose proof (nth_error_some_lt_length chosen c' j Hnth) as Hlt.
    pose proof (choose_top_m_length_le_m spec jobs m sched t (candidates_of jobs m sched t))
      as Hlen.
    unfold chosen in Hlt.
    lia.
  - pose proof (top_m_algorithm_eq_cpu spec candidates_of jobs m sched t c' Hrel) as Heq.
    assert (Hlt : c' < m).
      { pose proof (nth_error_some_lt_length chosen c' j Hnth) as Hlen'.
        pose proof (choose_top_m_length_le_m spec jobs m sched t (candidates_of jobs m sched t))
          as Hchosenlen.
        unfold chosen in Hlen'.
        lia. }
    apply Nat.ltb_lt in Hlt.
    rewrite Hlt in Heq. simpl in Heq.
    fold chosen in Heq.
    rewrite Hnth in Heq.
    exact Heq.
Qed.

Lemma top_m_algorithm_not_running_subset_eligible_implies_all_cpus_busy :
  forall J spec candidates_of jobs m sched t j,
    CandidateSourceSpec J candidates_of ->
    scheduler_rel (top_m_algorithm_schedule spec candidates_of) jobs m sched ->
    J j ->
    eligible jobs m sched j t ->
    ~ running m sched j t ->
    forall c, c < m -> cpu_busy sched t c.
Proof.
  intros J spec candidates_of jobs m sched t j
         Hcand Hrel HJ Helig Hnrun c Hc.
  destruct (sched t c) as [j_run|] eqn:Hcpu.
  - exists j_run. exact Hcpu.
  - exfalso.
    apply Hnrun.
    eapply top_m_algorithm_running_if_some_cpu_idle_and_subset_eligible; eauto.
    exists c. split; assumption.
Qed.
