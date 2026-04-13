(* TopMAdmissibilityBridge.v
   Policy-independent multicore busy/idle/running lemmas for
   all_cpus_admissible.

   The three "admissible_somewhere" variants of the work-conserving
   lemmas were previously duplicated verbatim in GlobalEDF.v and
   GlobalLLF.v.  This file extracts them once, parameterised by
   spec : GenericTopMSchedulingAlgorithm, following the same naming
   convention as TopMSchedulerBridge.v.

   GlobalEDF and GlobalLLF now delegate to these lemmas and provide
   thin EDF-/LLF-specific wrappers that preserve the old public names.

   Contents
   --------
   top_m_algorithm_all_cpus_idle_if_no_subset_admissible_somewhere
   top_m_algorithm_some_cpu_busy_if_subset_admissible_somewhere
   top_m_algorithm_running_if_some_cpu_idle_and_subset_admissible_somewhere
*)

From Stdlib Require Import List Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.TopMInterface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.TopMSchedulerBridge.
From RocqSched Require Import Multicore.Common.MultiCoreBase.
From RocqSched Require Import Multicore.Common.Admissibility.
From RocqSched Require Import Multicore.Common.AdmissibleCandidateSource.

(* ===== Helper lemmas ===== *)

(** H-1. If a job is running on some CPU c < m, it was in the candidate list.

    Connects scheduler_rel (top_m_algorithm_schedule) with choose_top_m_in_candidates
    so that downstream lemmas can reason about candidates from a running job. *)
Lemma top_m_algorithm_scheduled_job_in_candidates :
  forall spec candidates_of jobs m sched t c j,
    scheduler_rel (top_m_algorithm_schedule spec candidates_of) jobs m sched ->
    c < m ->
    sched t c = Some j ->
    In j (candidates_of jobs m sched t).
Proof.
  intros spec candidates_of jobs m sched t c j Hrel Hlt Hrun.
  pose proof (top_m_algorithm_eq_cpu spec candidates_of jobs m sched t c Hrel) as Heq.
  apply Nat.ltb_lt in Hlt.
  rewrite Hlt in Heq. simpl in Heq.
  rewrite Hrun in Heq.
  symmetry in Heq.
  eapply choose_top_m_in_candidates.
  exact (nth_error_some_in _ _ _ Heq).
Qed.

(** H-2. If a job is running, it belongs to the subset J.

    Uses AdmissibleCandidateSourceSpec soundness (weaker than CandidateSourceSpec). *)
Lemma top_m_algorithm_in_admissible_subset :
  forall adm J spec candidates_of jobs m sched t c j,
    AdmissibleCandidateSourceSpec adm J candidates_of ->
    scheduler_rel (top_m_algorithm_schedule spec candidates_of) jobs m sched ->
    c < m ->
    sched t c = Some j ->
    J j.
Proof.
  intros adm J spec candidates_of jobs m sched t c j Hcand Hrel Hlt Hrun.
  destruct Hcand as [Hsound _ _].
  eapply Hsound.
  eapply top_m_algorithm_scheduled_job_in_candidates; eauto.
Qed.

(** D-1. If every J-job lacks admissibility somewhere (under all_cpus_admissible),
    then all CPUs are idle.

    Reduces to top_m_algorithm_all_cpus_idle_if_no_subset_eligible via
    admissible_somewhere_of_all_cpus_admissible. *)
Lemma top_m_algorithm_all_cpus_idle_if_no_subset_admissible_somewhere :
  forall J spec candidates_of jobs m sched t,
    CandidateSourceSpec J candidates_of ->
    scheduler_rel (top_m_algorithm_schedule spec candidates_of) jobs m sched ->
    0 < m ->
    (forall j, J j -> ~ admissible_somewhere all_cpus_admissible jobs m sched j t) ->
    all_cpus_idle m sched t.
Proof.
  intros J spec candidates_of jobs m sched t Hcand Hrel Hm Hnone.
  apply (top_m_algorithm_all_cpus_idle_if_no_subset_eligible
           J spec candidates_of jobs m sched t Hcand Hrel).
  intros j Hj Helig.
  apply (Hnone j Hj).
  exact (admissible_somewhere_of_all_cpus_admissible jobs m sched j t Hm Helig).
Qed.

(** D-2. If some J-job is admissible somewhere (under all_cpus_admissible),
    then at least one CPU is busy.

    Reduces via eligible_on_cpu_implies_eligible. *)
Lemma top_m_algorithm_some_cpu_busy_if_subset_admissible_somewhere :
  forall J spec candidates_of jobs m sched t,
    CandidateSourceSpec J candidates_of ->
    scheduler_rel (top_m_algorithm_schedule spec candidates_of) jobs m sched ->
    0 < m ->
    (exists j, J j /\ admissible_somewhere all_cpus_admissible jobs m sched j t) ->
    exists c, c < m /\ cpu_busy sched t c.
Proof.
  intros J spec candidates_of jobs m sched t Hcand Hrel Hm [j [HJ Hadm]].
  apply (top_m_algorithm_some_cpu_busy_if_subset_eligible
           J spec candidates_of jobs m sched t Hcand Hrel Hm).
  exists j. split; [exact HJ |].
  destruct Hadm as [c Helig].
  exact (eligible_on_cpu_implies_eligible all_cpus_admissible jobs m sched j t c Helig).
Qed.

(** D-3. If some CPU is idle and a J-job is admissible somewhere (under
    all_cpus_admissible), then that job is running.

    Reduces via eligible_on_cpu_implies_eligible. *)
Lemma top_m_algorithm_running_if_some_cpu_idle_and_subset_admissible_somewhere :
  forall J spec candidates_of jobs m sched t j,
    CandidateSourceSpec J candidates_of ->
    scheduler_rel (top_m_algorithm_schedule spec candidates_of) jobs m sched ->
    0 < m ->
    some_cpu_idle m sched t ->
    J j ->
    admissible_somewhere all_cpus_admissible jobs m sched j t ->
    running m sched j t.
Proof.
  intros J spec candidates_of jobs m sched t j Hcand Hrel Hm Hidle HJ Hadm.
  apply (top_m_algorithm_running_if_some_cpu_idle_and_subset_eligible
           J spec candidates_of jobs m sched t j Hcand Hrel Hidle HJ).
  destruct Hadm as [c Helig].
  exact (eligible_on_cpu_implies_eligible all_cpus_admissible jobs m sched j t c Helig).
Qed.

(* ===== General _gen lemmas (arbitrary adm) ===== *)

(** D-4. General version of D-2: if some J-job is admissible somewhere under
    an arbitrary adm, then at least one CPU is busy.

    Uses AdmissibleCandidateSourceSpec (weaker than CandidateSourceSpec). *)
Lemma top_m_algorithm_some_cpu_busy_if_subset_admissible_somewhere_gen :
  forall adm J spec candidates_of jobs m sched t,
    AdmissibleCandidateSourceSpec adm J candidates_of ->
    scheduler_rel (top_m_algorithm_schedule spec candidates_of) jobs m sched ->
    0 < m ->
    (exists j, J j /\ admissible_somewhere adm jobs m sched j t) ->
    exists c, c < m /\ cpu_busy sched t c.
Proof.
  intros adm J spec candidates_of jobs m sched t Hcand Hrel Hm [j [HJ Hadm]].
  destruct Hcand as [_ Hcomplete _].
  set (chosen := choose_top_m spec jobs m sched t (candidates_of jobs m sched t)).
  assert (Helig : eligible jobs m sched j t).
  { exact (admissible_somewhere_implies_eligible adm jobs m sched j t Hadm). }
  assert (Hincand : In j (candidates_of jobs m sched t)).
  { apply (Hcomplete jobs m sched t j HJ Helig Hadm). }
  destruct (in_dec Nat.eq_dec j chosen) as [Hin|Hnotin].
  - destruct (in_nth_error_exists chosen j Hin) as [c Hnth].
    exists c. split.
    + pose proof (nth_error_some_lt_length chosen c j Hnth) as Hclt.
      pose proof (choose_top_m_length_le_m spec jobs m sched t
                   (candidates_of jobs m sched t)) as Hlen.
      unfold chosen in Hclt. lia.
    + exists j.
      pose proof (top_m_algorithm_eq_cpu spec candidates_of jobs m sched t c Hrel) as Heq.
      assert (Hlt : c < m).
      { pose proof (nth_error_some_lt_length chosen c j Hnth) as Hclt.
        pose proof (choose_top_m_length_le_m spec jobs m sched t
                     (candidates_of jobs m sched t)) as Hlen.
        unfold chosen in Hclt. lia. }
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

(** D-5. General version of D-3: if some CPU is idle and a J-job is admissible
    somewhere under an arbitrary adm, then that job is running.

    Uses AdmissibleCandidateSourceSpec.  Does not require 0 < m. *)
Lemma top_m_algorithm_running_if_some_cpu_idle_and_subset_admissible_somewhere_gen :
  forall adm J spec candidates_of jobs m sched t j,
    AdmissibleCandidateSourceSpec adm J candidates_of ->
    scheduler_rel (top_m_algorithm_schedule spec candidates_of) jobs m sched ->
    some_cpu_idle m sched t ->
    J j ->
    admissible_somewhere adm jobs m sched j t ->
    running m sched j t.
Proof.
  intros adm J spec candidates_of jobs m sched t j
         Hcand Hrel [c [Hclt Hidle]] HJ Hadm.
  destruct Hcand as [_ Hcomplete _].
  set (chosen := choose_top_m spec jobs m sched t (candidates_of jobs m sched t)).
  assert (Helig : eligible jobs m sched j t).
  { exact (admissible_somewhere_implies_eligible adm jobs m sched j t Hadm). }
  assert (Hincand : In j (candidates_of jobs m sched t)).
  { apply (Hcomplete jobs m sched t j HJ Helig Hadm). }
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
    pose proof (choose_top_m_length_le_m spec jobs m sched t
                 (candidates_of jobs m sched t)) as Hlen.
    unfold chosen in Hlt. lia.
  - pose proof (top_m_algorithm_eq_cpu spec candidates_of jobs m sched t c' Hrel) as Heq.
    assert (Hlt : c' < m).
    { pose proof (nth_error_some_lt_length chosen c' j Hnth) as Hlen'.
      pose proof (choose_top_m_length_le_m spec jobs m sched t
                   (candidates_of jobs m sched t)) as Hchosenlen.
      unfold chosen in Hlen'. lia. }
    apply Nat.ltb_lt in Hlt.
    rewrite Hlt in Heq. simpl in Heq.
    fold chosen in Heq.
    rewrite Hnth in Heq.
    exact Heq.
Qed.

(** D-6. General version of D-1: if no J-job is admissible somewhere under an
    arbitrary adm, then all CPUs are idle.

    Requires StrongAdmissibleCandidateSourceSpec, which guarantees every
    candidate is admissible somewhere.  Does not require 0 < m. *)
Lemma top_m_algorithm_all_cpus_idle_if_no_subset_admissible_somewhere_gen :
  forall adm J spec candidates_of jobs m sched t,
    StrongAdmissibleCandidateSourceSpec adm J candidates_of ->
    scheduler_rel (top_m_algorithm_schedule spec candidates_of) jobs m sched ->
    (forall j, J j -> ~ admissible_somewhere adm jobs m sched j t) ->
    all_cpus_idle m sched t.
Proof.
  intros adm J spec candidates_of jobs m sched t Hcand Hrel Hnone.
  destruct Hcand as [Hbase Hcandadm].
  unfold all_cpus_idle, cpu_idle.
  intros c Hlt.
  destruct (sched t c) as [j|] eqn:Hcpu.
  - exfalso.
    pose proof
      (top_m_algorithm_in_admissible_subset
         adm J spec candidates_of jobs m sched t c j
         Hbase Hrel Hlt Hcpu) as Hj.
    pose proof
      (top_m_algorithm_scheduled_job_in_candidates
         spec candidates_of jobs m sched t c j
         Hrel Hlt Hcpu) as Hincand.
    pose proof (Hcandadm jobs m sched t j Hincand) as Hadm.
    exact (Hnone j Hj Hadm).
  - reflexivity.
Qed.
