From Stdlib Require Import Arith Arith.PeanoNat Lia List.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Analysis.Common.WorkloadAggregation.
From RocqSched Require Import Analysis.Uniprocessor.BusyInterval.
From RocqSched Require Import Analysis.Uniprocessor.BusyWindowSearch.
From RocqSched Require Import Analysis.Uniprocessor.ProcessorDemand.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Periodic.PeriodicFiniteHorizon.
From RocqSched Require Import TaskModels.Periodic.PeriodicWindowDemandBound.

Import ListNotations.

Lemma edf_deadline_miss_implies_busy_window_covering_deadline :
  forall (jobs : JobId -> Job) sched j t1 t2,
    missed_deadline jobs 1 sched j ->
    busy_window_candidate sched t1 t2 ->
    t1 <= job_abs_deadline (jobs j) ->
    job_abs_deadline (jobs j) <= t2 ->
    busy_window_witness sched (job_abs_deadline (jobs j)) t1 t2.
Proof.
  intros jobs sched j t1 t2 Hmiss Hbusy Hleft Hright.
  exact (deadline_miss_inside_busy_window_candidate jobs sched j t1 t2
           Hmiss Hbusy Hleft Hright).
Qed.

Lemma periodic_window_overload_contradiction :
  forall T tasks offset jobs enumT sched t1 t2 l,
    well_formed_periodic_tasks_on T tasks ->
    busy_window_candidate sched t1 t2 ->
    NoDup enumT ->
    NoDup (map (fun j => (job_task (jobs j), job_index (jobs j))) l) ->
    (forall x, In x l ->
       periodic_jobset_deadline_between T tasks offset jobs t1 t2 x /\
       In (job_task (jobs x)) enumT) ->
    taskset_periodic_dbf_window tasks offset enumT t1 t2 <= t2 - t1 ->
    cpu_service_between sched t1 t2 < total_job_cost jobs l ->
    False.
Proof.
  intros T tasks offset jobs enumT sched t1 t2 l
         Hwf Hbusy HnodupT HnodupL Hl Hdbf Hover.
  pose proof (periodic_total_window_demand_le_taskset_dbf_window
                T tasks offset jobs t1 t2 enumT l
                Hwf HnodupT HnodupL Hl) as Hdemand.
  rewrite busy_window_candidate_cpu_supply_eq_length in Hover by exact Hbusy.
  lia.
Qed.

Lemma window_dbf_bound_implies_no_window_overload :
  forall T tasks offset jobs enumT sched t1 t2 l,
    well_formed_periodic_tasks_on T tasks ->
    busy_window_candidate sched t1 t2 ->
    NoDup enumT ->
    NoDup (map (fun j => (job_task (jobs j), job_index (jobs j))) l) ->
    (forall x, In x l ->
       periodic_jobset_deadline_between T tasks offset jobs t1 t2 x /\
       In (job_task (jobs x)) enumT) ->
    taskset_periodic_dbf_window tasks offset enumT t1 t2 <= t2 - t1 ->
    total_job_cost jobs l <= cpu_service_between sched t1 t2.
Proof.
  intros T tasks offset jobs enumT sched t1 t2 l
         Hwf Hbusy HnodupT HnodupL Hl Hdbf.
  destruct (le_gt_dec (total_job_cost jobs l) (cpu_service_between sched t1 t2))
    as [Hle | Hgt].
  - exact Hle.
  - exfalso.
    eapply periodic_window_overload_contradiction; eauto.
Qed.

(* ===== EDF feasibility from window-DBF ===== *)

(*
 * Proof sketch for future completion of periodic_window_dbf_implies_no_deadline_miss:
 *
 * Assume missed_deadline jobs 1 sched j in the EDF schedule.
 * Since EDF is work-conserving (runs whenever an eligible job exists,
 * by CandidateSourceSpec completeness + choose_edf_some_if_exists)
 * and j is eligible throughout [job_release(j), job_abs_deadline(j)),
 * the interval [job_release(j), job_abs_deadline(j)) is entirely busy.
 * Construct the maximal busy interval [t1, t2] with t2 >= job_abs_deadline(j)
 * and t2 <= H (first idle slot; exists because H is a finite bound).
 * In this interval:
 *   - busy_window_candidate sched t1 t2 holds.
 *   - EDF priority (respects_edf_priority_at_on from EDFLemmas.v): every
 *     job scheduled in [t1, t2) has deadline <= job_abs_deadline(j) <= t2.
 *   - So the running jobs form a subset of periodic_jobset_deadline_between t1 t2.
 *   - Apply window_dbf_bound_implies_no_window_overload: demand <= supply.
 *   - j's unfinished cost is positive (missed_deadline), so demand > supply.
 *     Contradiction.
 *
 * Missing infrastructure needed to close this proof:
 *   1. EDF work-conserving lemma: if sched is an EDF schedule (uses edf_scheduler)
 *      and there exists an eligible job in J, the processor is busy at that slot.
 *      (Needs CandidateSourceSpec completeness + choose_edf_some_if_exists.)
 *   2. Busy-interval existence: for any busy time point t in a discrete schedule,
 *      there exists a maximal busy interval [t1, t2] with t1 <= t < t2.
 *      (Constructible from last-idle-slot argument over finite horizon.)
 *   3. EDF-in-window-has-early-deadline: every job scheduled by EDF in [t1, t2)
 *      has deadline <= t2.
 *      (Follows from respects_edf_priority_at_on in EDFLemmas.v.)
 *   4. Running-jobs membership: connects jobs actually scheduled in [t1, t2)
 *      to periodic_jobset_deadline_between T tasks offset jobs t1 t2.
 *)
Theorem periodic_window_dbf_implies_no_deadline_miss :
  forall T tasks offset H enumT jobs sched j,
    well_formed_periodic_tasks_on T tasks ->
    valid_schedule jobs 1 sched ->
    periodic_jobset_upto T tasks offset jobs H j ->
    (forall t1 t2,
      t1 <= t2 ->
      t2 <= H ->
      taskset_periodic_dbf_window tasks offset enumT t1 t2 <= t2 - t1) ->
    ~ missed_deadline jobs 1 sched j.
Proof.
  Admitted.

(*
 * Proof sketch for future completion of
 * periodic_window_dbf_implies_edf_feasible_on_finite_horizon:
 *
 * Witness: the EDF schedule sched_edf = edf_scheduler (...) jobs 1.
 * (1) valid_schedule jobs 1 sched_edf follows from the EDF scheduler producing
 *     only eligible jobs (scheduler validity guarantee).
 * (2) feasible_schedule_on (periodic_jobset_upto ...) jobs 1 sched_edf follows
 *     from periodic_window_dbf_implies_no_deadline_miss applied to each j in
 *     periodic_jobset_upto, once the EDF-specific conditions in that lemma
 *     (work-conservation, window existence) are established.
 *)
Theorem periodic_window_dbf_implies_edf_feasible_on_finite_horizon :
  forall T tasks offset H enumT jobs,
    well_formed_periodic_tasks_on T tasks ->
    (forall t1 t2,
      t1 <= t2 ->
      t2 <= H ->
      taskset_periodic_dbf_window tasks offset enumT t1 t2 <= t2 - t1) ->
    feasible_on (periodic_jobset_upto T tasks offset jobs H) jobs 1.
Proof.
  Admitted.
