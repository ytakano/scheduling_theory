From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.EnumCandidates.
From RocqSched Require Import Analysis.Uniprocessor.BusyWindowSearch.
From RocqSched Require Import Analysis.Uniprocessor.EDFProcessorDemand.
From RocqSched Require Import Analysis.Uniprocessor.LLFLaxityFeasibility.
From RocqSched Require Import Uniprocessor.Policies.EDF.
From RocqSched Require Import Uniprocessor.Policies.LLF.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Periodic.PeriodicFiniteHorizon.
From RocqSched Require Import TaskModels.Periodic.PeriodicEnumeration.
From RocqSched Require Import TaskModels.Periodic.PeriodicWindowDemandBound.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFBridge.
From RocqSched Require Import TaskModels.Periodic.PeriodicLLFBridge.

Import ListNotations.

Theorem periodic_llf_schedulable_by_window_dbf_on_finite_horizon_auto_with_busy_prefix_bridge :
  forall T tasks offset H enumT jobs
         (codec : PeriodicFiniteHorizonCodec T tasks offset jobs H)
         sched,
    well_formed_periodic_tasks_on T tasks ->
    NoDup enumT ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    scheduler_rel
      (edf_scheduler
         (enum_candidates_of
            (enum_periodic_jobs_upto T tasks offset jobs H enumT codec)))
      jobs 1 sched ->
    (forall j,
      periodic_jobset_upto T tasks offset jobs H j ->
      job_abs_deadline (jobs j) <= H /\
      exists t1 t2,
        busy_prefix_witness sched (job_abs_deadline (jobs j)) t1 t2 /\
        periodic_edf_busy_prefix_bridge T tasks offset jobs H sched j) ->
    (forall t1 t2,
      t1 <= t2 ->
      t2 <= H ->
      taskset_periodic_dbf_window tasks offset enumT t1 t2 <= t2 - t1) ->
    schedulable_by_on
      (periodic_jobset_upto T tasks offset jobs H)
      (llf_scheduler
         (enum_candidates_of
            (enum_periodic_jobs_upto T tasks offset jobs H enumT codec)))
      jobs 1.
Proof.
  intros T tasks offset H enumT jobs codec sched
         Hwf HnodupT HenumT_complete HenumT_sound
         Hsched Hjob_bridge Hdbf.
  eapply periodic_llf_optimality_on_finite_horizon_auto; eauto.
  eapply periodic_window_dbf_implies_edf_feasible_on_finite_horizon_with_busy_prefix_bridge; eauto.
Qed.
