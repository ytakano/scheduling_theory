(* TopMAdmissibilityBridge.v
   Policy-independent multicore admissibility theorem layer.

   This file provides the generic busy/idle/running lemmas for top-m
   schedulers, parameterised by an admissibility predicate adm and a
   CandidateSourceSpec variant.  It has two tiers:

   Tier 1 — all_cpus_admissible specialisations
     For the standard case where every CPU is admissible for every job.
     These lemmas use the plain CandidateSourceSpec and require 0 < m.
     They are essentially special cases of the Tier 2 lemmas (see Note).

   Tier 2 — generic adm lemmas (_gen suffix)
     For arbitrary adm.  These lemmas use AdmissibleCandidateSourceSpec
     (for busy/running) or StrongAdmissibleCandidateSourceSpec (for idle).
     They do not require 0 < m.

   Note: all_cpus_admissible is a special case of generic adm.
   For all_cpus_admissible, every eligible job is already admissible
   somewhere (given 0 < m), so AdmissibleCandidateSourceSpec collapses
   to the standard CandidateSourceSpec.  The Tier 1 lemmas exist as
   backward-compatible entry points that accept CandidateSourceSpec
   directly and carry an explicit 0 < m premise.

   GlobalEDF and GlobalLLF delegate to these lemmas and provide thin
   policy-specific wrappers that preserve their public names.

   Contents
   --------
   Helper lemmas:
     top_m_algorithm_scheduled_job_in_candidates
     top_m_algorithm_in_admissible_subset

   Tier 1 — all_cpus_admissible (CandidateSourceSpec, requires 0 < m):
     top_m_algorithm_all_cpus_idle_if_no_subset_admissible_somewhere
     top_m_algorithm_some_cpu_busy_if_subset_admissible_somewhere
     top_m_algorithm_running_if_some_cpu_idle_and_subset_admissible_somewhere

   Tier 2 — generic adm (AdmissibleCandidateSourceSpec /
             StrongAdmissibleCandidateSourceSpec; does not require 0 < m):
     top_m_algorithm_some_cpu_busy_if_subset_admissible_somewhere_gen
     top_m_algorithm_running_if_some_cpu_idle_and_subset_admissible_somewhere_gen
     top_m_algorithm_all_cpus_idle_if_no_subset_admissible_somewhere_gen
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

(* ===== Tier 1: all_cpus_admissible specialisations =====
   The three lemmas below are the all_cpus_admissible-specific entry points.
   They accept the plain CandidateSourceSpec and carry an explicit 0 < m
   premise.  Use the _gen variants (Tier 2, below) when working with a
   restricted affinity or any adm other than all_cpus_admissible. *)

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

Lemma top_m_algorithm_not_running_subset_admissible_somewhere_implies_all_cpus_busy :
  forall J spec candidates_of jobs m sched t j,
    CandidateSourceSpec J candidates_of ->
    scheduler_rel (top_m_algorithm_schedule spec candidates_of) jobs m sched ->
    0 < m ->
    J j ->
    admissible_somewhere all_cpus_admissible jobs m sched j t ->
    ~ running m sched j t ->
    forall c, c < m -> cpu_busy sched t c.
Proof.
  intros J spec candidates_of jobs m sched t j
         Hcand Hrel Hm HJ Hadm Hnrun c Hc.
  destruct (sched t c) as [j_run|] eqn:Hcpu.
  - exists j_run. exact Hcpu.
  - exfalso.
    apply Hnrun.
    eapply top_m_algorithm_running_if_some_cpu_idle_and_subset_admissible_somewhere; eauto.
    exists c. split; assumption.
Qed.

(* ===== Tier 2: generic adm (_gen lemmas) =====
   These lemmas work for any admissibility predicate adm.
   - busy/running lemmas use AdmissibleCandidateSourceSpec (weaker spec).
   - idle lemma uses StrongAdmissibleCandidateSourceSpec, which additionally
     requires every candidate to be admissible somewhere — this is the
     extra obligation that makes the idle proof go through without 0 < m.
   None of these lemmas require 0 < m. *)

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

Lemma top_m_algorithm_not_running_subset_admissible_somewhere_implies_all_cpus_busy_gen :
  forall adm J spec candidates_of jobs m sched t j,
    AdmissibleCandidateSourceSpec adm J candidates_of ->
    scheduler_rel (top_m_algorithm_schedule spec candidates_of) jobs m sched ->
    J j ->
    admissible_somewhere adm jobs m sched j t ->
    ~ running m sched j t ->
    forall c, c < m -> cpu_busy sched t c.
Proof.
  intros adm J spec candidates_of jobs m sched t j
         Hcand Hrel HJ Hadm Hnrun c Hc.
  destruct (sched t c) as [j_run|] eqn:Hcpu.
  - exists j_run. exact Hcpu.
  - exfalso.
    apply Hnrun.
    eapply top_m_algorithm_running_if_some_cpu_idle_and_subset_admissible_somewhere_gen; eauto.
    exists c. split; assumption.
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
