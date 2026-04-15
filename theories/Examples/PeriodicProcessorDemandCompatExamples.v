From Stdlib Require Import Arith Arith.PeanoNat Lia List Bool.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.EnumCandidates.
From RocqSched Require Import Uniprocessor.Generic.FinitePrefixScheduleWitness.
From RocqSched Require Import Uniprocessor.Policies.EDF.
From RocqSched Require Import Analysis.Uniprocessor.BusyWindowSearch.
From RocqSched Require Import Analysis.Uniprocessor.EDFProcessorDemand.
From RocqSched Require Import TaskModels.Periodic.PeriodicFiniteHorizon.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFBridge.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFBridgeCompat.
From RocqSched Require Import TaskModels.Periodic.PeriodicEnumeration.
From RocqSched Require Import TaskModels.Periodic.PeriodicWindowDemandBound.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Examples.PeriodicExamples.
From RocqSched Require Import Examples.PeriodicProcessorDemandExamples.

Import ListNotations.

Theorem periodic_example_edf_no_deadline_miss_by_window_dbf_auto_compat :
  forall sched j t1 t2,
    scheduler_rel
      (edf_scheduler
         (enum_candidates_of
            (enum_periodic_jobs_upto T_ex tasks_ex offset_ex jobs_ex H_ex enumT_ex codec_ex)))
      jobs_ex 1 sched ->
    periodic_jobset_upto T_ex tasks_ex offset_ex jobs_ex H_ex j ->
    busy_window_witness sched (job_abs_deadline (jobs_ex j)) t1 t2 ->
    t1 <= job_release (jobs_ex j) ->
    job_abs_deadline (jobs_ex j) <= H_ex ->
    (forall t j_run,
      job_release (jobs_ex j) <= t < job_abs_deadline (jobs_ex j) ->
      sched t 0 = Some j_run ->
      periodic_jobset_deadline_between T_ex tasks_ex offset_ex jobs_ex
        t1 (job_abs_deadline (jobs_ex j)) j_run ->
      job_release (jobs_ex j) <= job_release (jobs_ex j_run)) ->
    ~ missed_deadline jobs_ex 1 sched j.
Proof.
  intros sched j t1 t2 Hsched Hj Hwit Ht1rel Hj_H Hcarry_free.
  eapply periodic_edf_no_deadline_miss_from_window_dbf_on_finite_horizon_auto
    with (enumT := enumT_ex); eauto.
  - exact tasks_ex_well_formed.
  - exact enumT_ex_nodup.
  - intros τ Hτ.
    destruct Hτ as [Hτ | Hτ]; subst τ; simpl; tauto.
  - intros τ Hτ.
    simpl in Hτ.
    destruct Hτ as [Hτ | [Hτ | []]]; subst τ.
    + left. reflexivity.
    + right. reflexivity.
  - exact periodic_window_dbf_test.
Qed.

Theorem periodic_example_edf_no_deadline_miss_by_window_dbf_auto_with_busy_prefix_compat :
  forall sched j t1 t2,
    scheduler_rel
      (edf_scheduler
         (enum_candidates_of
            (enum_periodic_jobs_upto T_ex tasks_ex offset_ex jobs_ex H_ex enumT_ex codec_ex)))
      jobs_ex 1 sched ->
    periodic_jobset_upto T_ex tasks_ex offset_ex jobs_ex H_ex j ->
    busy_prefix_witness sched (job_abs_deadline (jobs_ex j)) t1 t2 ->
    job_abs_deadline (jobs_ex j) <= H_ex ->
    (forall t1' t2',
      busy_prefix_witness sched (job_abs_deadline (jobs_ex j)) t1' t2' ->
      t1' <= job_release (jobs_ex j)) ->
    (forall t1' t2',
      busy_prefix_witness sched (job_abs_deadline (jobs_ex j)) t1' t2' ->
      t1' <= job_release (jobs_ex j) ->
      forall t j_run,
        job_release (jobs_ex j) <= t < job_abs_deadline (jobs_ex j) ->
        sched t 0 = Some j_run ->
        periodic_jobset_deadline_between T_ex tasks_ex offset_ex jobs_ex
          t1' (job_abs_deadline (jobs_ex j)) j_run ->
        job_release (jobs_ex j) <= job_release (jobs_ex j_run)) ->
    ~ missed_deadline jobs_ex 1 sched j.
Proof.
  intros sched j t1 t2 Hsched Hj Hwit Hj_H Hstart Hcarry.
  eapply periodic_example_edf_no_deadline_miss_by_window_dbf_auto_with_busy_prefix_bridge; eauto.
  apply periodic_example_edf_busy_prefix_bridge; assumption.
Qed.

Theorem periodic_example_edf_schedulable_by_window_dbf_auto_compat :
  forall sched,
    scheduler_rel
      (edf_scheduler
         (enum_candidates_of
            (enum_periodic_jobs_upto T_ex tasks_ex offset_ex jobs_ex H_ex enumT_ex codec_ex)))
      jobs_ex 1 sched ->
    (forall j,
      periodic_jobset_upto T_ex tasks_ex offset_ex jobs_ex H_ex j ->
      job_abs_deadline (jobs_ex j) <= H_ex /\
      exists t1 t2,
        busy_window_witness sched (job_abs_deadline (jobs_ex j)) t1 t2 /\
        t1 <= job_release (jobs_ex j) /\
        (forall t j_run,
          job_release (jobs_ex j) <= t < job_abs_deadline (jobs_ex j) ->
          sched t 0 = Some j_run ->
          periodic_jobset_deadline_between T_ex tasks_ex offset_ex jobs_ex
            t1 (job_abs_deadline (jobs_ex j)) j_run ->
          job_release (jobs_ex j) <= job_release (jobs_ex j_run))) ->
    schedulable_by_on
      (periodic_jobset_upto T_ex tasks_ex offset_ex jobs_ex H_ex)
      (edf_scheduler
         (enum_candidates_of
            (enum_periodic_jobs_upto T_ex tasks_ex offset_ex jobs_ex H_ex enumT_ex codec_ex)))
      jobs_ex 1.
Proof.
  intros sched Hsched Hjob_bridge.
  eapply periodic_edf_schedulable_by_window_dbf_on_finite_horizon_auto
    with (sched := sched) (enumT := enumT_ex); eauto.
  - exact tasks_ex_well_formed.
  - exact enumT_ex_nodup.
  - intros τ Hτ.
    destruct Hτ as [Hτ | Hτ]; subst τ; simpl; tauto.
  - intros τ Hτ.
    simpl in Hτ.
    destruct Hτ as [Hτ | [Hτ | []]]; subst τ.
    + left. reflexivity.
    + right. reflexivity.
  - exact periodic_window_dbf_test.
Qed.

Theorem periodic_example_edf_schedulable_by_window_dbf_auto_with_busy_prefix_compat :
  forall sched,
    scheduler_rel
      (edf_scheduler
         (enum_candidates_of
            (enum_periodic_jobs_upto T_ex tasks_ex offset_ex jobs_ex H_ex enumT_ex codec_ex)))
      jobs_ex 1 sched ->
    (forall j,
      periodic_jobset_upto T_ex tasks_ex offset_ex jobs_ex H_ex j ->
      job_abs_deadline (jobs_ex j) <= H_ex /\
      exists t1 t2,
        busy_prefix_witness sched (job_abs_deadline (jobs_ex j)) t1 t2 /\
        (forall t1' t2',
          busy_prefix_witness sched (job_abs_deadline (jobs_ex j)) t1' t2' ->
          t1' <= job_release (jobs_ex j)) /\
        (forall t1' t2',
          busy_prefix_witness sched (job_abs_deadline (jobs_ex j)) t1' t2' ->
          t1' <= job_release (jobs_ex j) ->
          forall t j_run,
            job_release (jobs_ex j) <= t < job_abs_deadline (jobs_ex j) ->
            sched t 0 = Some j_run ->
            periodic_jobset_deadline_between T_ex tasks_ex offset_ex jobs_ex
              t1' (job_abs_deadline (jobs_ex j)) j_run ->
            job_release (jobs_ex j) <= job_release (jobs_ex j_run))) ->
    schedulable_by_on
      (periodic_jobset_upto T_ex tasks_ex offset_ex jobs_ex H_ex)
      (edf_scheduler
         (enum_candidates_of
            (enum_periodic_jobs_upto T_ex tasks_ex offset_ex jobs_ex H_ex enumT_ex codec_ex)))
      jobs_ex 1.
Proof.
  intros sched Hsched Hjob_bridge.
  eapply periodic_example_edf_schedulable_by_window_dbf_auto_with_busy_prefix_bridge; eauto.
  intros j Hj.
  destruct (Hjob_bridge j Hj) as [Hj_H [t1 [t2 [Hwit [Hstart Hcarry]]]]].
  split; [exact Hj_H |].
  exists t1, t2.
  split; [exact Hwit |].
  apply periodic_example_edf_busy_prefix_bridge; assumption.
Qed.
