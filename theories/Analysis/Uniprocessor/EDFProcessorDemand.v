From Stdlib Require Import Arith Arith.PeanoNat Lia List.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Analysis.Common.WorkloadAggregation.
From RocqSched Require Import Analysis.Uniprocessor.BusyInterval.
From RocqSched Require Import Analysis.Uniprocessor.BusyWindowSearch.
From RocqSched Require Import Analysis.Uniprocessor.ProcessorDemand.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
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
