From Stdlib Require Import Arith Arith.PeanoNat Lia Bool List.
Require Import Base.
Require Import ScheduleModel.
Require Import SchedulerInterface.
Require Import SchedulingAlgorithmInterface.
Import ListNotations.

(* Bridge between GenericSchedulingAlgorithm and the Scheduler abstraction.
   This file provides the standard route from a single-CPU choose policy
   to `schedulable_by_on` for a designated job set J.

   Reading order:
     1. CandidateSource / CandidateSourceSpec — how job candidates are supplied
     2. single_cpu_algorithm_schedule — wraps a choose policy into a Scheduler
     3. single_cpu_algorithm_valid — the produced schedule is valid
     4. single_cpu_algorithm_scheduler_on — subset-aware wrapper
     5. Inspection lemmas (eq_cpu0, idle_on_other_cpus, in_subset, …)
     6. single_cpu_algorithm_schedulable_by_on_intro — standard entry point      *)

(* ===== 1. Candidate Source Abstraction ===== *)

(* CandidateSource: a function that supplies the candidate job list at each
   time step.  The candidates do NOT need to all be eligible; the scheduling algorithm
   skips ineligible ones (see GenericSchedulingAlgorithm.choose_eligible). *)
Definition CandidateSource :=
  (JobId -> Job) -> nat -> Schedule -> Time -> list JobId.

(* CandidateSourceSpec: contract that a candidate source must satisfy with
   respect to a job set J.

   - candidates_sound: every candidate belongs to J (no stray jobs)
   - candidates_complete: every eligible job in J appears in the candidate list
     (ensures progress: a ready job will eventually be considered)
   - candidates_prefix_extensional: the candidate list at time t depends only
     on the schedule history strictly before t.  This prevents circular
     reasoning when constructing a schedule by induction on time.
     (Forward-compatible condition for global/refinement reasoning.) *)
Record CandidateSourceSpec
    (J : JobId -> Prop)
    (candidates_of : CandidateSource) : Prop := mkCandidateSourceSpec {
  candidates_sound :
    forall jobs m sched t j,
      In j (candidates_of jobs m sched t) -> J j;
  candidates_complete :
    forall jobs m sched t j,
      J j -> eligible jobs m sched j t ->
      In j (candidates_of jobs m sched t);
  candidates_prefix_extensional :
    forall jobs m s1 s2 t,
      (forall t' c, t' < t -> s1 t' c = s2 t' c) ->
      candidates_of jobs m s1 t = candidates_of jobs m s2 t
}.

(* ===== 2. single_cpu_algorithm_schedule ===== *)

(* Wrap a choose policy into a Scheduler relation for the single-CPU
   (m = 1) case.  The relation holds for a schedule sched when:
     - CPU 0 follows the choose policy at every time step
     - All other CPUs are idle                                            *)
Definition single_cpu_algorithm_schedule
    (spec : GenericSchedulingAlgorithm)
    (candidates_of : (JobId -> Job) -> nat -> Schedule -> Time -> list JobId)
    : Scheduler :=
  mkScheduler (fun jobs m sched =>
    m = 1 /\
    forall t,
      sched t 0 = spec.(choose) jobs 1 sched t (candidates_of jobs 1 sched t) /\
      forall c, 0 < c -> sched t c = None).

(* ===== 3. single_cpu_algorithm_valid ===== *)

(* A schedule produced by single_cpu_algorithm_schedule is valid (on 1 CPU),
   because choose_eligible guarantees every chosen job is eligible,
   and idle CPUs carry no job. *)
Lemma single_cpu_algorithm_valid :
    forall spec candidates_of jobs sched,
      scheduler_rel (single_cpu_algorithm_schedule spec candidates_of) jobs 1 sched ->
      valid_schedule jobs 1 sched.
Proof.
  intros spec cands jobs sched Hrel.
  destruct Hrel as [_ Hrel].
  unfold valid_schedule.
  intros j t c Hc Hsched.
  assert (c = 0) by lia. subst c.
  destruct (Hrel t) as [Heq _].
  rewrite Heq in Hsched.
  exact (spec.(choose_eligible) jobs 1 sched t _ j Hsched).
Qed.

(* ===== 4. single_cpu_algorithm_scheduler_on ===== *)

(* Subset-aware wrapper.  The CandidateSourceSpec proof is threaded through
   so that callers can use it in subset-schedulability lemmas. *)
Definition single_cpu_algorithm_scheduler_on
    (J : JobId -> Prop)
    (spec : GenericSchedulingAlgorithm)
    (candidates_of : CandidateSource)
    (_ : CandidateSourceSpec J candidates_of)
    : Scheduler :=
  single_cpu_algorithm_schedule spec candidates_of.

(* ===== 5. Inspection lemmas ===== *)

(* CPU 0 carries exactly the choose result. *)
Lemma single_cpu_algorithm_eq_cpu0 :
    forall spec candidates_of jobs sched t,
      scheduler_rel (single_cpu_algorithm_schedule spec candidates_of) jobs 1 sched ->
      sched t 0 = spec.(choose) jobs 1 sched t (candidates_of jobs 1 sched t).
Proof.
  intros spec candidates_of jobs sched t Hrel.
  destruct Hrel as [_ Hrel].
  exact (proj1 (Hrel t)).
Qed.

(* Every CPU other than 0 is permanently idle. *)
Lemma single_cpu_algorithm_idle_on_other_cpus :
    forall spec candidates_of jobs sched t c,
      scheduler_rel (single_cpu_algorithm_schedule spec candidates_of) jobs 1 sched ->
      0 < c -> sched t c = None.
Proof.
  intros spec candidates_of jobs sched t c Hrel Hc.
  destruct Hrel as [_ Hrel].
  exact (proj2 (Hrel t) c Hc).
Qed.

(* The scheduled job always belongs to J. *)
Lemma single_cpu_algorithm_in_subset :
    forall J spec candidates_of jobs sched t j,
      CandidateSourceSpec J candidates_of ->
      scheduler_rel (single_cpu_algorithm_schedule spec candidates_of) jobs 1 sched ->
      sched t 0 = Some j ->
      J j.
Proof.
  intros J spec candidates_of jobs sched t j Hcand Hrel Hrun.
  destruct Hcand as [Hsound _ _].
  destruct Hrel as [_ Hrel].
  destruct (Hrel t) as [Heq _].
  apply (Hsound jobs 1 sched t j).
  eapply spec.(choose_in_candidates).
  rewrite <- Heq.
  exact Hrun.
Qed.

(* If some job in J is eligible, CPU 0 is non-idle. *)
Lemma single_cpu_algorithm_some_if_subset_eligible :
    forall J spec candidates_of jobs sched t,
      CandidateSourceSpec J candidates_of ->
      scheduler_rel (single_cpu_algorithm_schedule spec candidates_of) jobs 1 sched ->
      (exists j, J j /\ eligible jobs 1 sched j t) ->
      exists j', sched t 0 = Some j'.
Proof.
  intros J spec candidates_of jobs sched t Hcand Hrel [j [HJ Helig]].
  destruct Hcand as [_ Hcomplete _].
  destruct Hrel as [_ Hrel].
  destruct (Hrel t) as [Heq _].
  destruct (spec.(choose_some_if_eligible_candidate)
              jobs 1 sched t (candidates_of jobs 1 sched t))
      as [j' Hchoose_agree].
  - exists j.
    split.
    + apply (Hcomplete jobs 1 sched t j HJ Helig).
    + exact Helig.
  - exists j'.
    rewrite Heq.
    exact Hchoose_agree.
Qed.

(* If no job in J is eligible, CPU 0 is idle. *)
Lemma single_cpu_algorithm_none_if_no_subset_eligible :
    forall J spec candidates_of jobs sched t,
      CandidateSourceSpec J candidates_of ->
      scheduler_rel (single_cpu_algorithm_schedule spec candidates_of) jobs 1 sched ->
      (forall j, J j -> ~ eligible jobs 1 sched j t) ->
      sched t 0 = None.
Proof.
  intros J spec candidates_of jobs sched t Hcand Hrel Hnone.
  destruct Hcand as [Hsound _ _].
  destruct Hrel as [_ Hrel].
  destruct (Hrel t) as [Heq _].
  rewrite Heq.
  apply spec.(choose_none_if_no_eligible_candidate).
  intros j Hin Helig.
  exact (Hnone j (Hsound jobs 1 sched t j Hin) Helig).
Qed.

(* ===== 6. schedulable_by_on intro ===== *)

(* Standard entry point: given a witness schedule that is feasible on J,
   conclude schedulable_by_on. *)
Lemma single_cpu_algorithm_schedulable_by_on_intro :
    forall J spec candidates_of cand_spec jobs sched,
      scheduler_rel
        (single_cpu_algorithm_scheduler_on J spec candidates_of cand_spec)
        jobs 1 sched ->
      feasible_schedule_on J jobs 1 sched ->
      schedulable_by_on
        J
        (single_cpu_algorithm_scheduler_on J spec candidates_of cand_spec)
        jobs 1.
Proof.
  intros J spec candidates_of cand_spec jobs sched Hrel Hfeas.
  apply (schedulable_by_on_intro
           J
           (single_cpu_algorithm_scheduler_on J spec candidates_of cand_spec)
           jobs 1 sched).
  - exact Hrel.
  - exact (single_cpu_algorithm_valid spec candidates_of jobs sched Hrel).
  - exact Hfeas.
Qed.

(* Backward-compatible alias for single_cpu_algorithm_schedulable_by_on_intro. *)
Abbreviation single_cpu_algorithm_schedulable_by_on :=
  single_cpu_algorithm_schedulable_by_on_intro.
