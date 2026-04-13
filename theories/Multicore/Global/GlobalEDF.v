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
From SchedulingTheory Require Import Foundation.Base.
From SchedulingTheory Require Import Semantics.Schedule.
From SchedulingTheory Require Import Abstractions.Scheduler.Interface.
From SchedulingTheory Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From SchedulingTheory Require Import Abstractions.SchedulingAlgorithm.TopMInterface.
From SchedulingTheory Require Import Abstractions.SchedulingAlgorithm.TopMSchedulerBridge.
From SchedulingTheory Require Import Multicore.Common.MultiCoreBase.
From SchedulingTheory Require Import Multicore.Common.TopMMetricChooser.
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
