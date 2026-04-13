(* GlobalLLF.v
   Global Least-Laxity-First multiprocessor scheduler.
   Policy-specific wrapper layer over TopMAdmissibilityBridge.

   The scheduler selects the m eligible jobs with least laxity and assigns
   them to CPUs 0 .. m-1 via nth_error (see TopMSchedulerBridge).

   This file is the LLF policy-specific wrapper layer.  Its structure mirrors
   GlobalEDF.v exactly; the only EDF/LLF differences are:
     - the priority metric (laxity vs absolute deadline), and
     - the top-m spec construction: LLF uses a dynamic metric (laxity depends
       on the current schedule), so the spec is built directly with
       mkGenericTopMSchedulingAlgorithm rather than make_metric_top_m_algorithm.

   The admissibility reasoning lives in TopMAdmissibilityBridge.v; the lemmas
   here merely instantiate it with global_llf_top_m_spec.

   Contents
   --------
   global_llf_metric_of_jobs : (JobId -> Job) -> nat -> Schedule -> Time -> JobId -> Z
     LLF priority: laxity as Z (smaller = higher priority).

   global_llf_top_m_spec : GenericTopMSchedulingAlgorithm
     Instance via mkGenericTopMSchedulingAlgorithm (dynamic metric).

   global_llf_scheduler : CandidateSource -> Scheduler
     Lift to a Scheduler via top_m_algorithm_schedule.

   global_llf_valid : scheduler_rel global_llf_scheduler -> valid_schedule
     The scheduler only runs eligible jobs.

   Admissibility wrappers — all_cpus_admissible (Tier 1):
     global_llf_all_cpus_idle_if_no_subset_admissible_somewhere
     global_llf_some_cpu_busy_if_subset_admissible_somewhere
     global_llf_running_if_some_cpu_idle_and_subset_admissible_somewhere

   Admissibility wrappers — generic adm (Tier 2, _gen suffix):
     global_llf_some_cpu_busy_if_subset_admissible_somewhere_gen
     global_llf_running_if_some_cpu_idle_and_subset_admissible_somewhere_gen
     global_llf_all_cpus_idle_if_no_subset_admissible_somewhere_gen
*)

From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia ZArith.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.TopMInterface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.TopMSchedulerBridge.
From RocqSched Require Import Multicore.Common.MultiCoreBase.
From RocqSched Require Import Multicore.Common.Admissibility.
From RocqSched Require Import Multicore.Common.TopMMetricChooser.
From RocqSched Require Import Multicore.Common.TopMAdmissibilityBridge.
From RocqSched Require Import Multicore.Common.AdmissibleCandidateSource.
Import ListNotations.

(* ===== LLF metric ===== *)

(** Smaller laxity = higher priority (least laxity first). *)
Definition global_llf_metric_of_jobs
    (jobs : JobId -> Job) (m : nat) (sched : Schedule) (t : Time)
    (j : JobId) : Z :=
  laxity jobs m sched j t.

(* ===== Top-m algorithm instance ===== *)

Definition global_llf_top_m_spec : GenericTopMSchedulingAlgorithm :=
  mkGenericTopMSchedulingAlgorithm
    (fun jobs m sched t cands =>
       choose_top_m_by_metric m (global_llf_metric_of_jobs jobs m sched t)
         jobs m sched t cands)
    (fun jobs m sched t cands =>
       choose_top_m_by_metric_nodup m (global_llf_metric_of_jobs jobs m sched t)
         jobs m sched t cands)
    (fun jobs m sched t cands j H =>
       choose_top_m_by_metric_in_candidates
         m (global_llf_metric_of_jobs jobs m sched t) jobs m sched t cands j H)
    (fun jobs m sched t cands j H =>
       choose_top_m_by_metric_eligible
         m (global_llf_metric_of_jobs jobs m sched t) jobs m sched t cands j H)
    (fun jobs m sched t cands =>
       choose_top_m_by_metric_length_le
         m (global_llf_metric_of_jobs jobs m sched t) jobs m sched t cands)
    (fun jobs m sched t cands j Hin Helig Hnotin =>
       choose_top_m_by_metric_complete_if_room
         m (global_llf_metric_of_jobs jobs m sched t) jobs m sched t cands j Hin Helig Hnotin).

(* ===== Scheduler ===== *)

Definition global_llf_scheduler
    (candidates_of : CandidateSource) : Scheduler :=
  top_m_algorithm_schedule global_llf_top_m_spec candidates_of.

Definition global_llf_scheduler_on
    (J : JobId -> Prop)
    (candidates_of : CandidateSource)
    (_ : CandidateSourceSpec J candidates_of)
    : Scheduler :=
  global_llf_scheduler candidates_of.

Lemma global_llf_eq_cpu :
  forall candidates_of jobs m sched t c,
    scheduler_rel (global_llf_scheduler candidates_of) jobs m sched ->
    sched t c =
      if c <? m then
        nth_error (choose_top_m global_llf_top_m_spec jobs m sched t
                     (candidates_of jobs m sched t)) c
      else None.
Proof.
  intros candidates_of jobs m sched t c Hrel.
  exact (top_m_algorithm_eq_cpu global_llf_top_m_spec candidates_of jobs m sched t c Hrel).
Qed.

(* ===== Main theorem: validity ===== *)

(** Any schedule produced by the global LLF scheduler only runs eligible jobs. *)
Lemma global_llf_valid :
  forall candidates_of jobs m sched,
    scheduler_rel (global_llf_scheduler candidates_of) jobs m sched ->
    valid_schedule jobs m sched.
Proof.
  intros candidates_of jobs m sched H.
  exact (top_m_algorithm_valid global_llf_top_m_spec candidates_of jobs m sched H).
Qed.

(** CPUs beyond the CPU count are always idle. *)
Lemma global_llf_idle_outside_range :
  forall candidates_of jobs m sched t c,
    scheduler_rel (global_llf_scheduler candidates_of) jobs m sched ->
    m <= c ->
    sched t c = None.
Proof.
  intros candidates_of jobs m sched t c H Hge.
  exact (top_m_algorithm_idle_outside_range
           global_llf_top_m_spec candidates_of jobs m sched t c H Hge).
Qed.

(** The scheduler never assigns the same job to two distinct CPUs. *)
Lemma global_llf_no_duplication :
  forall candidates_of jobs m sched,
    scheduler_rel (global_llf_scheduler candidates_of) jobs m sched ->
    no_duplication m sched.
Proof.
  intros candidates_of jobs m sched H.
  exact (top_m_algorithm_no_duplication
           global_llf_top_m_spec candidates_of jobs m sched H).
Qed.

Lemma global_llf_in_subset :
  forall J candidates_of jobs m sched t c j,
    CandidateSourceSpec J candidates_of ->
    scheduler_rel (global_llf_scheduler candidates_of) jobs m sched ->
    c < m ->
    sched t c = Some j ->
    J j.
Proof.
  intros J candidates_of jobs m sched t c j Hcand Hrel Hlt Hrun.
  exact (top_m_algorithm_in_subset
           J global_llf_top_m_spec candidates_of jobs m sched t c j
           Hcand Hrel Hlt Hrun).
Qed.

(* ===== Work-conserving lemmas: eligible (LLF wrappers over TopMSchedulerBridge) ===== *)

Lemma global_llf_all_cpus_idle_if_no_subset_eligible :
  forall J candidates_of jobs m sched t,
    CandidateSourceSpec J candidates_of ->
    scheduler_rel (global_llf_scheduler candidates_of) jobs m sched ->
    (forall j, J j -> ~ eligible jobs m sched j t) ->
    all_cpus_idle m sched t.
Proof.
  intros J candidates_of jobs m sched t Hcand Hrel Hnone.
  exact (top_m_algorithm_all_cpus_idle_if_no_subset_eligible
           J global_llf_top_m_spec candidates_of jobs m sched t
           Hcand Hrel Hnone).
Qed.

Lemma global_llf_some_cpu_busy_if_subset_eligible :
  forall J candidates_of jobs m sched t,
    CandidateSourceSpec J candidates_of ->
    scheduler_rel (global_llf_scheduler candidates_of) jobs m sched ->
    0 < m ->
    (exists j, J j /\ eligible jobs m sched j t) ->
    exists c, c < m /\ cpu_busy sched t c.
Proof.
  intros J candidates_of jobs m sched t Hcand Hrel Hm Hex.
  exact (top_m_algorithm_some_cpu_busy_if_subset_eligible
           J global_llf_top_m_spec candidates_of jobs m sched t
           Hcand Hrel Hm Hex).
Qed.

Lemma global_llf_running_if_some_cpu_idle_and_subset_eligible :
  forall J candidates_of jobs m sched t j,
    CandidateSourceSpec J candidates_of ->
    scheduler_rel (global_llf_scheduler candidates_of) jobs m sched ->
    some_cpu_idle m sched t ->
    J j ->
    eligible jobs m sched j t ->
    running m sched j t.
Proof.
  intros J candidates_of jobs m sched t j Hcand Hrel Hidle HJ Helig.
  exact (top_m_algorithm_running_if_some_cpu_idle_and_subset_eligible
           J global_llf_top_m_spec candidates_of jobs m sched t j
           Hcand Hrel Hidle HJ Helig).
Qed.

(* ===== Admissibility wrappers: all_cpus_admissible
   (LLF thin wrappers over TopMAdmissibilityBridge Tier 1)
   LLF-specific: instantiates the bridge with global_llf_top_m_spec. ===== *)

Lemma global_llf_all_cpus_idle_if_no_subset_admissible_somewhere :
  forall J candidates_of jobs m sched t,
    CandidateSourceSpec J candidates_of ->
    scheduler_rel (global_llf_scheduler candidates_of) jobs m sched ->
    0 < m ->
    (forall j, J j ->
       ~ admissible_somewhere all_cpus_admissible jobs m sched j t) ->
    all_cpus_idle m sched t.
Proof.
  intros J candidates_of jobs m sched t Hcand Hrel Hm Hnone.
  exact (top_m_algorithm_all_cpus_idle_if_no_subset_admissible_somewhere
           J global_llf_top_m_spec candidates_of jobs m sched t
           Hcand Hrel Hm Hnone).
Qed.

Lemma global_llf_some_cpu_busy_if_subset_admissible_somewhere :
  forall J candidates_of jobs m sched t,
    CandidateSourceSpec J candidates_of ->
    scheduler_rel (global_llf_scheduler candidates_of) jobs m sched ->
    0 < m ->
    (exists j, J j /\
       admissible_somewhere all_cpus_admissible jobs m sched j t) ->
    exists c, c < m /\ cpu_busy sched t c.
Proof.
  intros J candidates_of jobs m sched t Hcand Hrel Hm Hex.
  exact (top_m_algorithm_some_cpu_busy_if_subset_admissible_somewhere
           J global_llf_top_m_spec candidates_of jobs m sched t
           Hcand Hrel Hm Hex).
Qed.

Lemma global_llf_running_if_some_cpu_idle_and_subset_admissible_somewhere :
  forall J candidates_of jobs m sched t j,
    CandidateSourceSpec J candidates_of ->
    scheduler_rel (global_llf_scheduler candidates_of) jobs m sched ->
    0 < m ->
    some_cpu_idle m sched t ->
    J j ->
    admissible_somewhere all_cpus_admissible jobs m sched j t ->
    running m sched j t.
Proof.
  intros J candidates_of jobs m sched t j Hcand Hrel Hm Hidle HJ Hadm.
  exact (top_m_algorithm_running_if_some_cpu_idle_and_subset_admissible_somewhere
           J global_llf_top_m_spec candidates_of jobs m sched t j
           Hcand Hrel Hm Hidle HJ Hadm).
Qed.

(* ===== Admissibility wrappers: generic adm
   (LLF thin wrappers over TopMAdmissibilityBridge Tier 2)
   These lemmas work for any adm; the idle variant requires
   StrongAdmissibleCandidateSourceSpec. ===== *)

(** LLF wrapper for the generic busy-if-exists lemma.
    Delegates to top_m_algorithm_some_cpu_busy_if_subset_admissible_somewhere_gen. *)
Lemma global_llf_some_cpu_busy_if_subset_admissible_somewhere_gen :
  forall adm J candidates_of jobs m sched t,
    AdmissibleCandidateSourceSpec adm J candidates_of ->
    scheduler_rel (global_llf_scheduler candidates_of) jobs m sched ->
    0 < m ->
    (exists j, J j /\ admissible_somewhere adm jobs m sched j t) ->
    exists c, c < m /\ cpu_busy sched t c.
Proof.
  intros adm J candidates_of jobs m sched t Hcand Hrel Hm Hex.
  exact
    (top_m_algorithm_some_cpu_busy_if_subset_admissible_somewhere_gen
       adm J global_llf_top_m_spec candidates_of jobs m sched t
       Hcand Hrel Hm Hex).
Qed.

(** LLF wrapper for the generic running-if-idle-and-admissible lemma.
    Delegates to top_m_algorithm_running_if_some_cpu_idle_and_subset_admissible_somewhere_gen. *)
Lemma global_llf_running_if_some_cpu_idle_and_subset_admissible_somewhere_gen :
  forall adm J candidates_of jobs m sched t j,
    AdmissibleCandidateSourceSpec adm J candidates_of ->
    scheduler_rel (global_llf_scheduler candidates_of) jobs m sched ->
    some_cpu_idle m sched t ->
    J j ->
    admissible_somewhere adm jobs m sched j t ->
    running m sched j t.
Proof.
  intros adm J candidates_of jobs m sched t j Hcand Hrel Hidle HJ Hadm.
  exact
    (top_m_algorithm_running_if_some_cpu_idle_and_subset_admissible_somewhere_gen
       adm J global_llf_top_m_spec candidates_of jobs m sched t j
       Hcand Hrel Hidle HJ Hadm).
Qed.

(** LLF wrapper for the generic idle-if-none lemma.
    Requires StrongAdmissibleCandidateSourceSpec (candidates must be admissible somewhere).
    Delegates to top_m_algorithm_all_cpus_idle_if_no_subset_admissible_somewhere_gen. *)
Lemma global_llf_all_cpus_idle_if_no_subset_admissible_somewhere_gen :
  forall adm J candidates_of jobs m sched t,
    StrongAdmissibleCandidateSourceSpec adm J candidates_of ->
    scheduler_rel (global_llf_scheduler candidates_of) jobs m sched ->
    (forall j, J j -> ~ admissible_somewhere adm jobs m sched j t) ->
    all_cpus_idle m sched t.
Proof.
  intros adm J candidates_of jobs m sched t Hcand Hrel Hnone.
  exact
    (top_m_algorithm_all_cpus_idle_if_no_subset_admissible_somewhere_gen
       adm J global_llf_top_m_spec candidates_of jobs m sched t
       Hcand Hrel Hnone).
Qed.

(* ===== Schedulability introduction ===== *)

Lemma global_llf_schedulable_by_on_intro :
  forall J candidates_of cand_spec jobs m sched,
    scheduler_rel
      (global_llf_scheduler_on J candidates_of cand_spec)
      jobs m sched ->
    feasible_schedule_on J jobs m sched ->
    schedulable_by_on
      J
      (global_llf_scheduler_on J candidates_of cand_spec)
      jobs m.
Proof.
  intros J candidates_of cand_spec jobs m sched Hrel Hfeas.
  exact (top_m_algorithm_schedulable_by_on_intro
           J global_llf_top_m_spec candidates_of cand_spec jobs m sched
           Hrel Hfeas).
Qed.
