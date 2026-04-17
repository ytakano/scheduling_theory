From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.EnumCandidates.
From RocqSched Require Import Analysis.Uniprocessor.ProcessorDemand.
From RocqSched Require Import Analysis.Uniprocessor.EDFProcessorDemand.
From RocqSched Require Import Uniprocessor.Generic.FinitePrefixScheduleWitness.
From RocqSched Require Import Uniprocessor.Policies.EDF.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Periodic.PeriodicFiniteHorizon.
From RocqSched Require Import TaskModels.Periodic.PeriodicEnumeration.
From RocqSched Require Import TaskModels.Periodic.PeriodicClassicDBF.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFBridge.

Import ListNotations.

(* Canonical bridge-first classical corollary. The finite-horizon generated
   statement remains the proof kernel; this alias is the public name for the
   current zero-offset / scalar-DBF closure. *)
Theorem periodic_classical_dbf_implies_generated_edf_no_deadline_miss_with_busy_prefix_bridge :
  forall T tasks offset H enumT jobs
         (codec : PeriodicFiniteHorizonCodec T tasks offset jobs H)
         j,
    well_formed_periodic_tasks_on T tasks ->
    NoDup enumT ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    (forall τ, offset τ = 0) ->
    periodic_jobset_upto T tasks offset jobs H j ->
    job_abs_deadline (jobs j) <= H ->
    periodic_edf_busy_prefix_bridge
      T tasks offset jobs H
      (generated_schedule
         edf_generic_spec
         (enum_candidates_of
            (enum_periodic_jobs_upto T tasks offset jobs H enumT codec))
         jobs)
      j ->
    (forall t, taskset_periodic_dbf tasks enumT t <= t) ->
    ~ missed_deadline jobs 1
        (generated_schedule
           edf_generic_spec
           (enum_candidates_of
              (enum_periodic_jobs_upto T tasks offset jobs H enumT codec))
           jobs)
        j.
Proof.
  intros T tasks offset H enumT jobs codec j
         Hwf HnodupT HenumT_complete HenumT_sound Hoff
         Hj Hj_H Hbridge Hdbf_classical.
  eapply periodic_window_dbf_implies_no_deadline_miss_under_generated_edf_with_busy_prefix_bridge; eauto.
  intros t1 t2 Hle12 HleH.
  eapply Nat.le_trans.
  - eapply zero_offset_taskset_window_dbf_le_classical_dbf.
    + intros τ Hin. apply Hoff.
    + intros τ Hin. apply Hwf. apply HenumT_sound. exact Hin.
  - apply Hdbf_classical.
Qed.

Theorem periodic_classical_dbf_implies_generated_edf_no_deadline_miss_on_finite_horizon_with_busy_prefix_bridge :
  forall T tasks offset H enumT jobs
         (codec : PeriodicFiniteHorizonCodec T tasks offset jobs H)
         j,
    well_formed_periodic_tasks_on T tasks ->
    NoDup enumT ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    (forall τ, In τ enumT -> offset τ = 0) ->
    (forall t, taskset_periodic_dbf tasks enumT t <= t) ->
    periodic_jobset_upto T tasks offset jobs H j ->
    job_abs_deadline (jobs j) <= H ->
    periodic_edf_busy_prefix_bridge
      T tasks offset jobs H
      (generated_schedule
         edf_generic_spec
         (enum_candidates_of
            (enum_periodic_jobs_upto T tasks offset jobs H enumT codec))
         jobs)
      j ->
    ~ missed_deadline jobs 1
        (generated_schedule
           edf_generic_spec
           (enum_candidates_of
              (enum_periodic_jobs_upto T tasks offset jobs H enumT codec))
           jobs)
        j.
Proof.
  intros T tasks offset H enumT jobs codec j
         Hwf HnodupT HenumT_complete HenumT_sound Hoff Hdbf_classical
         Hj Hj_H Hbridge.
  eapply periodic_window_dbf_implies_no_deadline_miss_under_generated_edf_with_busy_prefix_bridge; eauto.
  intros t1 t2 Hle12 HleH.
  eapply Nat.le_trans.
  - eapply zero_offset_taskset_window_dbf_le_classical_dbf.
    + intros τ Hin. apply Hoff. exact Hin.
    + intros τ Hin. apply Hwf. apply HenumT_sound. exact Hin.
  - apply Hdbf_classical.
Qed.

(* Canonical bridge-first schedulable corollary. *)
Theorem periodic_classical_dbf_implies_generated_edf_schedulable_with_busy_prefix_bridge :
  forall T tasks offset H enumT jobs
         (codec : PeriodicFiniteHorizonCodec T tasks offset jobs H),
    well_formed_periodic_tasks_on T tasks ->
    NoDup enumT ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    (forall τ, offset τ = 0) ->
    (forall t, taskset_periodic_dbf tasks enumT t <= t) ->
    (forall j,
      periodic_jobset_upto T tasks offset jobs H j ->
      job_abs_deadline (jobs j) <= H /\
      periodic_edf_busy_prefix_bridge
        T tasks offset jobs H
        (generated_schedule
           edf_generic_spec
           (enum_candidates_of
              (enum_periodic_jobs_upto T tasks offset jobs H enumT codec))
           jobs)
        j) ->
    schedulable_by_on
      (periodic_jobset_upto T tasks offset jobs H)
      (edf_scheduler
         (enum_candidates_of
            (enum_periodic_jobs_upto T tasks offset jobs H enumT codec)))
      jobs 1.
Proof.
  intros T tasks offset H enumT jobs codec
         Hwf HnodupT HenumT_complete HenumT_sound Hoff Hdbf_classical Hjob_bridge.
  eapply periodic_edf_schedulable_by_window_dbf_on_finite_horizon_generated_with_busy_prefix_bridge; eauto.
  intros t1 t2 Hle12 HleH.
  eapply Nat.le_trans.
  - eapply zero_offset_taskset_window_dbf_le_classical_dbf.
    + intros τ Hin. apply Hoff.
    + intros τ Hin. apply Hwf. apply HenumT_sound. exact Hin.
  - apply Hdbf_classical.
Qed.

Theorem periodic_classical_dbf_implies_generated_edf_schedulable_on_finite_horizon_with_busy_prefix_bridge :
  forall T tasks offset H enumT jobs
         (codec : PeriodicFiniteHorizonCodec T tasks offset jobs H),
    well_formed_periodic_tasks_on T tasks ->
    NoDup enumT ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    (forall τ, In τ enumT -> offset τ = 0) ->
    (forall t, taskset_periodic_dbf tasks enumT t <= t) ->
    (forall j,
      periodic_jobset_upto T tasks offset jobs H j ->
      job_abs_deadline (jobs j) <= H /\
      periodic_edf_busy_prefix_bridge
        T tasks offset jobs H
        (generated_schedule
           edf_generic_spec
           (enum_candidates_of
              (enum_periodic_jobs_upto T tasks offset jobs H enumT codec))
           jobs)
        j) ->
    schedulable_by_on
      (periodic_jobset_upto T tasks offset jobs H)
      (edf_scheduler
         (enum_candidates_of
            (enum_periodic_jobs_upto T tasks offset jobs H enumT codec)))
      jobs 1.
Proof.
  intros T tasks offset H enumT jobs codec
         Hwf HnodupT HenumT_complete HenumT_sound Hoff Hdbf_classical Hjob_bridge.
  eapply periodic_edf_schedulable_by_window_dbf_on_finite_horizon_generated_with_busy_prefix_bridge; eauto.
  intros t1 t2 Hle12 HleH.
  eapply Nat.le_trans.
  - eapply zero_offset_taskset_window_dbf_le_classical_dbf.
    + intros τ Hin. apply Hoff. exact Hin.
    + intros τ Hin. apply Hwf. apply HenumT_sound. exact Hin.
  - apply Hdbf_classical.
Qed.

Theorem periodic_classical_dbf_implies_generated_edf_schedulable_with_no_carry_in_bridge :
  forall T tasks offset H enumT jobs
         (codec : PeriodicFiniteHorizonCodec T tasks offset jobs H),
    well_formed_periodic_tasks_on T tasks ->
    NoDup enumT ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    (forall τ, In τ enumT -> offset τ = 0) ->
    (forall t, taskset_periodic_dbf tasks enumT t <= t) ->
    (forall j,
      periodic_jobset_upto T tasks offset jobs H j ->
      job_abs_deadline (jobs j) <= H /\
      periodic_edf_busy_prefix_no_carry_in_bridge
        T tasks offset jobs H
        (generated_schedule
           edf_generic_spec
           (enum_candidates_of
              (enum_periodic_jobs_upto T tasks offset jobs H enumT codec))
           jobs)
        j) ->
    schedulable_by_on
      (periodic_jobset_upto T tasks offset jobs H)
      (edf_scheduler
         (enum_candidates_of
            (enum_periodic_jobs_upto T tasks offset jobs H enumT codec)))
      jobs 1.
Proof.
  intros T tasks offset H enumT jobs codec
         Hwf HnodupT HenumT_complete HenumT_sound Hoff Hdbf_classical Hjob_bridge.
  eapply periodic_edf_schedulable_by_window_dbf_on_finite_horizon_generated_with_no_carry_in_bridge; eauto.
  intros t1 t2 Hle12 HleH.
  eapply Nat.le_trans.
  - eapply zero_offset_taskset_window_dbf_le_classical_dbf.
    + intros τ Hin. apply Hoff. exact Hin.
    + intros τ Hin. apply Hwf. apply HenumT_sound. exact Hin.
  - apply Hdbf_classical.
Qed.

Theorem periodic_classical_dbf_implies_generated_edf_schedulable_on_finite_horizon_with_no_carry_in_bridge :
  forall T tasks offset H enumT jobs
         (codec : PeriodicFiniteHorizonCodec T tasks offset jobs H),
    well_formed_periodic_tasks_on T tasks ->
    NoDup enumT ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    (forall τ, In τ enumT -> offset τ = 0) ->
    (forall t, taskset_periodic_dbf tasks enumT t <= t) ->
    (forall j,
      periodic_jobset_upto T tasks offset jobs H j ->
      job_abs_deadline (jobs j) <= H /\
      periodic_edf_busy_prefix_no_carry_in_bridge
        T tasks offset jobs H
        (generated_schedule
           edf_generic_spec
           (enum_candidates_of
              (enum_periodic_jobs_upto T tasks offset jobs H enumT codec))
           jobs)
        j) ->
    schedulable_by_on
      (periodic_jobset_upto T tasks offset jobs H)
      (edf_scheduler
         (enum_candidates_of
            (enum_periodic_jobs_upto T tasks offset jobs H enumT codec)))
      jobs 1.
Proof.
  intros T tasks offset H enumT jobs codec
         Hwf HnodupT HenumT_complete HenumT_sound Hoff Hdbf_classical Hjob_bridge.
  eapply periodic_classical_dbf_implies_generated_edf_schedulable_with_no_carry_in_bridge; eauto.
Qed.
