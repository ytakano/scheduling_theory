From Stdlib Require Import Arith Arith.PeanoNat Lia List.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.EnumCandidates.
From RocqSched Require Import Analysis.Common.WorkloadAggregation.
From RocqSched Require Import Analysis.Uniprocessor.BusyInterval.
From RocqSched Require Import Analysis.Uniprocessor.BusyWindowSearch.
From RocqSched Require Import Analysis.Uniprocessor.ProcessorDemand.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Periodic.PeriodicFiniteHorizon.
From RocqSched Require Import TaskModels.Periodic.PeriodicWindowDemandBound.
From RocqSched Require Import Uniprocessor.Policies.EDF.

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

(* The processor-demand argument is EDF-specific: the schedule must come from
   the EDF scheduler instantiated with a finite horizon enumeration that is
   sound and complete for the periodic jobset. *)
Axiom periodic_window_dbf_implies_no_deadline_miss_under_edf :
  forall T tasks offset H enumT enumJ jobs sched j,
    well_formed_periodic_tasks_on T tasks ->
    NoDup enumT ->
    (forall x, periodic_jobset_upto T tasks offset jobs H x -> In x enumJ) ->
    (forall x, In x enumJ -> periodic_jobset_upto T tasks offset jobs H x) ->
    scheduler_rel (edf_scheduler (enum_candidates_of enumJ)) jobs 1 sched ->
    periodic_jobset_upto T tasks offset jobs H j ->
    (forall t1 t2,
      t1 <= t2 ->
      t2 <= H ->
      taskset_periodic_dbf_window tasks offset enumT t1 t2 <= t2 - t1) ->
    ~ missed_deadline jobs 1 sched j.

(* The finite-horizon theorem packages the EDF witness schedule and the
   schedule-local no-miss property above. *)
Axiom periodic_window_dbf_implies_edf_feasible_on_finite_horizon :
  forall T tasks offset H enumT enumJ jobs,
    well_formed_periodic_tasks_on T tasks ->
    NoDup enumT ->
    (forall x, periodic_jobset_upto T tasks offset jobs H x -> In x enumJ) ->
    (forall x, In x enumJ -> periodic_jobset_upto T tasks offset jobs H x) ->
    (forall t1 t2,
      t1 <= t2 ->
      t2 <= H ->
      taskset_periodic_dbf_window tasks offset enumT t1 t2 <= t2 - t1) ->
    feasible_on (periodic_jobset_upto T tasks offset jobs H) jobs 1.
