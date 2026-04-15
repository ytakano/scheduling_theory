(* GlobalEDF.v
   Global Earliest-Deadline-First multiprocessor scheduler.
   Policy-specific wrapper layer over TopMAdmissibilityBridge.

   The scheduler selects the m eligible jobs with earliest absolute deadlines
   and assigns them to CPUs 0 .. m-1 via nth_error (see TopMSchedulerBridge).

   This file is the EDF policy-specific wrapper layer.  Its structure is:
     1. EDF metric and top-m spec (EDF-specific)
     2. Scheduler definition (EDF-specific)
     3. Validity / structural lemmas (thin wrappers over TopMSchedulerBridge)
     4. Admissibility wrappers: all_cpus_admissible (thin wrappers over
          TopMAdmissibilityBridge Tier 1)
     5. Admissibility wrappers: generic adm (thin wrappers over
          TopMAdmissibilityBridge Tier 2)
     6. Schedulability introduction (thin wrapper over TopMSchedulerBridge)

   The admissibility reasoning itself lives in TopMAdmissibilityBridge.v;
   the lemmas here merely instantiate it with global_edf_top_m_spec.

   Contents
   --------
   global_edf_metric_of_jobs : (JobId -> Job) -> JobId -> Z
     EDF priority: absolute deadline as Z.

   global_edf_top_m_spec : GenericTopMSchedulingAlgorithm
     Instance via make_metric_top_m_algorithm.

   global_edf_scheduler : CandidateSource -> Scheduler
     Lift to a Scheduler via top_m_algorithm_schedule.

   global_edf_valid : scheduler_rel global_edf_scheduler -> valid_schedule
     The scheduler only runs eligible jobs.

   Admissibility wrappers — all_cpus_admissible (Tier 1):
     global_edf_all_cpus_idle_if_no_subset_admissible_somewhere
     global_edf_some_cpu_busy_if_subset_admissible_somewhere
     global_edf_running_if_some_cpu_idle_and_subset_admissible_somewhere

   Admissibility wrappers — generic adm (Tier 2, _gen suffix):
     global_edf_some_cpu_busy_if_subset_admissible_somewhere_gen
     global_edf_running_if_some_cpu_idle_and_subset_admissible_somewhere_gen
     global_edf_all_cpus_idle_if_no_subset_admissible_somewhere_gen
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
From RocqSched Require Import Analysis.Multicore.ProcessorSupply.
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

(* ===== Work-conserving lemmas: eligible (EDF wrappers over TopMSchedulerBridge) ===== *)

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

(* ===== Admissibility wrappers: all_cpus_admissible
   (EDF thin wrappers over TopMAdmissibilityBridge Tier 1)
   EDF-specific: instantiates the bridge with global_edf_top_m_spec. ===== *)

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

(* ===== Admissibility wrappers: generic adm
   (EDF thin wrappers over TopMAdmissibilityBridge Tier 2)
   These lemmas work for any adm; the idle variant requires
   StrongAdmissibleCandidateSourceSpec. ===== *)

(** EDF wrapper for the generic busy-if-exists lemma.
    Delegates to top_m_algorithm_some_cpu_busy_if_subset_admissible_somewhere_gen. *)
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

(** EDF wrapper for the generic running-if-idle-and-admissible lemma.
    Delegates to top_m_algorithm_running_if_some_cpu_idle_and_subset_admissible_somewhere_gen. *)
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

(** EDF wrapper for the generic idle-if-none lemma.
    Requires StrongAdmissibleCandidateSourceSpec (candidates must be admissible somewhere).
    Delegates to top_m_algorithm_all_cpus_idle_if_no_subset_admissible_somewhere_gen. *)
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

Lemma global_edf_not_running_admissible_job_implies_all_cpus_busy :
  forall adm J candidates_of jobs m sched t j,
    AdmissibleCandidateSourceSpec adm J candidates_of ->
    scheduler_rel (global_edf_scheduler candidates_of) jobs m sched ->
    J j ->
    admissible_somewhere adm jobs m sched j t ->
    ~ running m sched j t ->
    forall c, c < m -> cpu_busy sched t c.
Proof.
  intros adm J candidates_of jobs m sched t j
         Hcand Hrel HJ Hadm Hnrun c Hc.
  exact
    (top_m_algorithm_not_running_subset_admissible_somewhere_implies_all_cpus_busy_gen
       adm J global_edf_top_m_spec candidates_of jobs m sched t j
       Hcand Hrel HJ Hadm Hnrun c Hc).
Qed.

Lemma global_edf_not_running_eligible_job_implies_all_cpus_busy :
  forall J candidates_of jobs m sched t j,
    CandidateSourceSpec J candidates_of ->
    scheduler_rel (global_edf_scheduler candidates_of) jobs m sched ->
    J j ->
    eligible jobs m sched j t ->
    ~ running m sched j t ->
    forall c, c < m -> cpu_busy sched t c.
Proof.
  intros J candidates_of jobs m sched t j
         Hcand Hrel HJ Helig Hnrun c Hc.
  exact
    (top_m_algorithm_not_running_subset_eligible_implies_all_cpus_busy
       J global_edf_top_m_spec candidates_of jobs m sched t j
       Hcand Hrel HJ Helig Hnrun c Hc).
Qed.

Lemma global_edf_not_running_admissible_job_interval_implies_full_supply :
  forall adm J candidates_of jobs m sched t1 t2 j,
    AdmissibleCandidateSourceSpec adm J candidates_of ->
    scheduler_rel (global_edf_scheduler candidates_of) jobs m sched ->
    J j ->
    (forall t, t1 <= t < t2 ->
      admissible_somewhere adm jobs m sched j t /\
      ~ running m sched j t) ->
    total_cpu_service_between m sched t1 t2 = m * (t2 - t1).
Proof.
  intros adm J candidates_of jobs m sched t1 t2 j Hcand Hrel HJ Hinterval.
  apply total_cpu_service_between_eq_capacity_if_all_cpus_busy.
  intros t Hrange c Hc.
  destruct (Hinterval t Hrange) as [Hadm Hnrun].
  eapply global_edf_not_running_admissible_job_implies_all_cpus_busy; eauto.
Qed.

Lemma global_edf_not_running_eligible_job_interval_implies_full_supply :
  forall J candidates_of jobs m sched t1 t2 j,
    CandidateSourceSpec J candidates_of ->
    scheduler_rel (global_edf_scheduler candidates_of) jobs m sched ->
    J j ->
    (forall t, t1 <= t < t2 ->
      eligible jobs m sched j t /\
      ~ running m sched j t) ->
    total_cpu_service_between m sched t1 t2 = m * (t2 - t1).
Proof.
  intros J candidates_of jobs m sched t1 t2 j Hcand Hrel HJ Hinterval.
  apply total_cpu_service_between_eq_capacity_if_all_cpus_busy.
  intros t Hrange c Hc.
  destruct (Hinterval t Hrange) as [Helig Hnrun].
  eapply global_edf_not_running_eligible_job_implies_all_cpus_busy; eauto.
Qed.

(* ===== Schedulability introduction ===== *)

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
