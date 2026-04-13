(* GlobalEDF.v
   Global Earliest-Deadline-First multiprocessor scheduler.

   The scheduler selects the m eligible jobs with earliest absolute deadlines
   and assigns them to CPUs 0 .. m-1 via nth_error (see TopMSchedulerBridge).

   Contents
   --------
   global_edf_metric_of_jobs : (JobId -> Job) -> JobId -> Z
     EDF priority: absolute deadline as Z.

   global_edf_top_m_spec : GenericTopMSchedulingAlgorithm
     Instance via make_metric_top_m_algorithm.

   global_edf_scheduler : CandidateSource -> Scheduler
     Lift to a Scheduler via top_m_algorithm_schedule.

   global_edf_valid : scheduler_rel global_edf_scheduler -> valid_schedule
     First main theorem: the scheduler only runs eligible jobs.
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

(* ===== EDF metric ===== *)

(** Assign each job its absolute deadline as a Z-valued priority.
    Smaller value = higher priority (earliest deadline first). *)
Definition global_edf_metric_of_jobs
    (jobs : JobId -> Job) (j : JobId) : Z :=
  Z.of_nat (job_abs_deadline (jobs j)).

(* ===== Top-m algorithm instance ===== *)

Definition global_edf_top_m_spec : GenericTopMSchedulingAlgorithm :=
  make_metric_top_m_algorithm global_edf_metric_of_jobs.

(* ===== Scheduler ===== *)

(** Global EDF scheduler: for a given candidate source, lift the EDF top-m
    algorithm to a Scheduler using the nth_error bridge. *)
Definition global_edf_scheduler
    (candidates_of : CandidateSource) : Scheduler :=
  top_m_algorithm_schedule global_edf_top_m_spec candidates_of.

Definition global_edf_scheduler_on
    (J : JobId -> Prop)
    (candidates_of : CandidateSource)
    (_ : CandidateSourceSpec J candidates_of)
    : Scheduler :=
  global_edf_scheduler candidates_of.

Lemma global_edf_eq_cpu :
  forall candidates_of jobs m sched t c,
    scheduler_rel (global_edf_scheduler candidates_of) jobs m sched ->
    sched t c =
      if c <? m then
        nth_error (choose_top_m global_edf_top_m_spec jobs m sched t
                     (candidates_of jobs m sched t)) c
      else None.
Proof.
  intros candidates_of jobs m sched t c Hrel.
  exact (top_m_algorithm_eq_cpu global_edf_top_m_spec candidates_of jobs m sched t c Hrel).
Qed.

(* ===== Main theorem: validity ===== *)

(** Any schedule produced by the global EDF scheduler only runs eligible jobs. *)
Lemma global_edf_valid :
  forall candidates_of jobs m sched,
    scheduler_rel (global_edf_scheduler candidates_of) jobs m sched ->
    valid_schedule jobs m sched.
Proof.
  intros candidates_of jobs m sched H.
  exact (top_m_algorithm_valid global_edf_top_m_spec candidates_of jobs m sched H).
Qed.

(** CPUs beyond the CPU count are always idle. *)
Lemma global_edf_idle_outside_range :
  forall candidates_of jobs m sched t c,
    scheduler_rel (global_edf_scheduler candidates_of) jobs m sched ->
    m <= c ->
    sched t c = None.
Proof.
  intros candidates_of jobs m sched t c H Hge.
  exact (top_m_algorithm_idle_outside_range
           global_edf_top_m_spec candidates_of jobs m sched t c H Hge).
Qed.

(** The scheduler never assigns the same job to two distinct CPUs. *)
Lemma global_edf_no_duplication :
  forall candidates_of jobs m sched,
    scheduler_rel (global_edf_scheduler candidates_of) jobs m sched ->
    no_duplication m sched.
Proof.
  intros candidates_of jobs m sched H.
  exact (top_m_algorithm_no_duplication
           global_edf_top_m_spec candidates_of jobs m sched H).
Qed.

Lemma global_edf_in_subset :
  forall J candidates_of jobs m sched t c j,
    CandidateSourceSpec J candidates_of ->
    scheduler_rel (global_edf_scheduler candidates_of) jobs m sched ->
    c < m ->
    sched t c = Some j ->
    J j.
Proof.
  intros J candidates_of jobs m sched t c j Hcand Hrel Hlt Hrun.
  exact (top_m_algorithm_in_subset
           J global_edf_top_m_spec candidates_of jobs m sched t c j
           Hcand Hrel Hlt Hrun).
Qed.

Lemma global_edf_all_cpus_idle_if_no_subset_eligible :
  forall J candidates_of jobs m sched t,
    CandidateSourceSpec J candidates_of ->
    scheduler_rel (global_edf_scheduler candidates_of) jobs m sched ->
    (forall j, J j -> ~ eligible jobs m sched j t) ->
    all_cpus_idle m sched t.
Proof.
  intros J candidates_of jobs m sched t Hcand Hrel Hnone.
  exact (top_m_algorithm_all_cpus_idle_if_no_subset_eligible
           J global_edf_top_m_spec candidates_of jobs m sched t
           Hcand Hrel Hnone).
Qed.

Lemma global_edf_some_cpu_busy_if_subset_eligible :
  forall J candidates_of jobs m sched t,
    CandidateSourceSpec J candidates_of ->
    scheduler_rel (global_edf_scheduler candidates_of) jobs m sched ->
    0 < m ->
    (exists j, J j /\ eligible jobs m sched j t) ->
    exists c, c < m /\ cpu_busy sched t c.
Proof.
  intros J candidates_of jobs m sched t Hcand Hrel Hm Hex.
  exact (top_m_algorithm_some_cpu_busy_if_subset_eligible
           J global_edf_top_m_spec candidates_of jobs m sched t
           Hcand Hrel Hm Hex).
Qed.

Lemma global_edf_running_if_some_cpu_idle_and_subset_eligible :
  forall J candidates_of jobs m sched t j,
    CandidateSourceSpec J candidates_of ->
    scheduler_rel (global_edf_scheduler candidates_of) jobs m sched ->
    some_cpu_idle m sched t ->
    J j ->
    eligible jobs m sched j t ->
    running m sched j t.
Proof.
  intros J candidates_of jobs m sched t j Hcand Hrel Hidle HJ Helig.
  exact (top_m_algorithm_running_if_some_cpu_idle_and_subset_eligible
           J global_edf_top_m_spec candidates_of jobs m sched t j
           Hcand Hrel Hidle HJ Helig).
Qed.

Lemma global_edf_all_cpus_idle_if_no_subset_admissible_somewhere :
  forall J candidates_of jobs m sched t,
    CandidateSourceSpec J candidates_of ->
    scheduler_rel (global_edf_scheduler candidates_of) jobs m sched ->
    0 < m ->
    (forall j, J j ->
       ~ admissible_somewhere all_cpus_admissible jobs m sched j t) ->
    all_cpus_idle m sched t.
Proof.
  intros J candidates_of jobs m sched t Hcand Hrel Hm Hnone.
  exact (top_m_algorithm_all_cpus_idle_if_no_subset_admissible_somewhere
           J global_edf_top_m_spec candidates_of jobs m sched t
           Hcand Hrel Hm Hnone).
Qed.

Lemma global_edf_some_cpu_busy_if_subset_admissible_somewhere :
  forall J candidates_of jobs m sched t,
    CandidateSourceSpec J candidates_of ->
    scheduler_rel (global_edf_scheduler candidates_of) jobs m sched ->
    0 < m ->
    (exists j, J j /\
       admissible_somewhere all_cpus_admissible jobs m sched j t) ->
    exists c, c < m /\ cpu_busy sched t c.
Proof.
  intros J candidates_of jobs m sched t Hcand Hrel Hm Hex.
  exact (top_m_algorithm_some_cpu_busy_if_subset_admissible_somewhere
           J global_edf_top_m_spec candidates_of jobs m sched t
           Hcand Hrel Hm Hex).
Qed.

Lemma global_edf_running_if_some_cpu_idle_and_subset_admissible_somewhere :
  forall J candidates_of jobs m sched t j,
    CandidateSourceSpec J candidates_of ->
    scheduler_rel (global_edf_scheduler candidates_of) jobs m sched ->
    0 < m ->
    some_cpu_idle m sched t ->
    J j ->
    admissible_somewhere all_cpus_admissible jobs m sched j t ->
    running m sched j t.
Proof.
  intros J candidates_of jobs m sched t j Hcand Hrel Hm Hidle HJ Hadm.
  exact (top_m_algorithm_running_if_some_cpu_idle_and_subset_admissible_somewhere
           J global_edf_top_m_spec candidates_of jobs m sched t j
           Hcand Hrel Hm Hidle HJ Hadm).
Qed.

Lemma global_edf_some_cpu_busy_if_subset_admissible_somewhere_gen :
  forall adm J candidates_of jobs m sched t,
    AdmissibleCandidateSourceSpec adm J candidates_of ->
    scheduler_rel (global_edf_scheduler candidates_of) jobs m sched ->
    0 < m ->
    (exists j, J j /\ admissible_somewhere adm jobs m sched j t) ->
    exists c, c < m /\ cpu_busy sched t c.
Proof.
  intros adm J candidates_of jobs m sched t Hcand Hrel Hm Hex.
  exact
    (top_m_algorithm_some_cpu_busy_if_subset_admissible_somewhere_gen
       adm J global_edf_top_m_spec candidates_of jobs m sched t
       Hcand Hrel Hm Hex).
Qed.

Lemma global_edf_running_if_some_cpu_idle_and_subset_admissible_somewhere_gen :
  forall adm J candidates_of jobs m sched t j,
    AdmissibleCandidateSourceSpec adm J candidates_of ->
    scheduler_rel (global_edf_scheduler candidates_of) jobs m sched ->
    some_cpu_idle m sched t ->
    J j ->
    admissible_somewhere adm jobs m sched j t ->
    running m sched j t.
Proof.
  intros adm J candidates_of jobs m sched t j Hcand Hrel Hidle HJ Hadm.
  exact
    (top_m_algorithm_running_if_some_cpu_idle_and_subset_admissible_somewhere_gen
       adm J global_edf_top_m_spec candidates_of jobs m sched t j
       Hcand Hrel Hidle HJ Hadm).
Qed.

Lemma global_edf_all_cpus_idle_if_no_subset_admissible_somewhere_gen :
  forall adm J candidates_of jobs m sched t,
    StrongAdmissibleCandidateSourceSpec adm J candidates_of ->
    scheduler_rel (global_edf_scheduler candidates_of) jobs m sched ->
    (forall j, J j -> ~ admissible_somewhere adm jobs m sched j t) ->
    all_cpus_idle m sched t.
Proof.
  intros adm J candidates_of jobs m sched t Hcand Hrel Hnone.
  exact
    (top_m_algorithm_all_cpus_idle_if_no_subset_admissible_somewhere_gen
       adm J global_edf_top_m_spec candidates_of jobs m sched t
       Hcand Hrel Hnone).
Qed.

Lemma global_edf_schedulable_by_on_intro :
  forall J candidates_of cand_spec jobs m sched,
    scheduler_rel
      (global_edf_scheduler_on J candidates_of cand_spec)
      jobs m sched ->
    feasible_schedule_on J jobs m sched ->
    schedulable_by_on
      J
      (global_edf_scheduler_on J candidates_of cand_spec)
      jobs m.
Proof.
  intros J candidates_of cand_spec jobs m sched Hrel Hfeas.
  exact (top_m_algorithm_schedulable_by_on_intro
           J global_edf_top_m_spec candidates_of cand_spec jobs m sched
           Hrel Hfeas).
Qed.
