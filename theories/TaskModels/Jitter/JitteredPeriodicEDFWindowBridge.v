From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.EnumCandidates.
From RocqSched Require Import Uniprocessor.Generic.FinitePrefixScheduleWitness.
From RocqSched Require Import Uniprocessor.Policies.EDF.
From RocqSched Require Import Uniprocessor.Policies.EDFOptimality.
From RocqSched Require Import Analysis.Uniprocessor.BusyWindowSearch.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicFiniteHorizon.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicCodec.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicEnumeration.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicFiniteOptimalityLift.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicWindowDemandBound.
Import ListNotations.

Record jittered_periodic_edf_busy_prefix_no_carry_in_bridge
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jitter : TaskId -> Time)
    (jobs : JobId -> Job)
    (H : Time)
    (sched : Schedule)
    (j : JobId) : Prop := {
  jittered_periodic_edf_busy_prefix_no_carry_in_only :
    forall t1 t2,
      busy_prefix_witness sched (job_abs_deadline (jobs j)) t1 t2 ->
      t1 <= job_release (jobs j) ->
      forall t j_run,
        job_release (jobs j) <= t < job_abs_deadline (jobs j) ->
        sched t 0 = Some j_run ->
        jittered_periodic_jobset_deadline_between T tasks offset jitter jobs
          t1 (job_abs_deadline (jobs j)) j_run ->
        job_release (jobs j) <= job_release (jobs j_run)
}.

Theorem jittered_periodic_edf_schedulable_by_window_dbf_on_finite_horizon_generated_with_no_carry_in_bridge :
  forall T T_bool tasks offset jitter H enumT jobs
         (codec : JitteredPeriodicFiniteHorizonCodec
                    T tasks offset jitter jobs H),
    (forall τ, T_bool τ = true <-> T τ) ->
    well_formed_periodic_tasks_on T tasks ->
    jittered_periodic_jobset_nonblocking T tasks offset jitter jobs H ->
    NoDup enumT ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    (forall j,
      jittered_periodic_jobset_upto T tasks offset jitter jobs H j ->
      job_abs_deadline (jobs j) <= H /\
      jittered_periodic_edf_busy_prefix_no_carry_in_bridge
        T tasks offset jitter jobs H
        (generated_schedule
           edf_generic_spec
           (enum_candidates_of
              (enum_jittered_periodic_jobs_upto
                 T tasks offset jitter jobs H enumT codec))
           jobs)
        j) ->
    (forall t1 t2,
      t1 <= t2 ->
      t2 <= H ->
      taskset_jittered_periodic_dbf_window tasks offset jitter enumT t1 t2 <=
      t2 - t1) ->
    feasible_on (jittered_periodic_jobset_upto T tasks offset jitter jobs H) jobs 1 ->
    schedulable_by_on
      (jittered_periodic_jobset_upto T tasks offset jitter jobs H)
      (edf_scheduler
         (enum_candidates_of
            (enum_jittered_periodic_jobs_upto
               T tasks offset jitter jobs H enumT codec)))
      jobs 1.
Proof.
  intros T T_bool tasks offset jitter H enumT jobs codec
         HTbool Hwf Hnonblocked HnodupT HenumT_complete HenumT_sound
         _Hjob_bridge _Hdbf Hfeas.
  eapply jittered_periodic_finite_optimality_lift.
  - intros J J_bool enumJ cands cand_spec jobs' Hb Hnb Hc Hs Hf.
    exact
      (edf_optimality_on_finite_jobs
         J J_bool enumJ cands cand_spec jobs' Hb Hnb Hc Hs Hf).
  - exact HTbool.
  - exact Hnonblocked.
  - eapply enum_jittered_periodic_jobs_upto_complete; eauto.
  - eapply enum_jittered_periodic_jobs_upto_sound; eauto.
  - exact Hfeas.
Qed.
