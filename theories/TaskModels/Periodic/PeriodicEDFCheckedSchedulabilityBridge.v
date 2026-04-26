From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Analysis.Uniprocessor.EDFProcessorDemand.
From RocqSched Require Import Analysis.Uniprocessor.ProcessorDemand.
From RocqSched Require Import TaskModels.Periodic.PeriodicClassicDBF.
From RocqSched Require Import TaskModels.Periodic.PeriodicCodec.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFCertificate.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFCertificateSoundness.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFExtractionDecision.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFExtractionSoundness.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFExtractionTypes.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFInfiniteBridge.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFPrefixCoherence.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFTransportChecker.
From RocqSched Require Import TaskModels.Periodic.PeriodicInfinite.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import Uniprocessor.Policies.EDF.

Import ListNotations.

(** Schedulability wrappers that replace the public no-carry-in premise with
    checked transport-certificate obligations.

    This file is intentionally a composition layer: DBF soundness still comes
    from the existing DBF checker/theorems, while no-carry-in is supplied by the
    transport checker.  Transport witness construction remains outside this
    layer. *)

Theorem periodic_edf_schedulable_by_classical_dbf_with_checked_transport :
  forall T tasks offset enumT jobs
         (codec : PeriodicCodec T tasks offset jobs)
         transport_cert transported_jobs,
    well_formed_periodic_tasks_on T tasks ->
    (forall j t,
      periodic_jobset T tasks offset jobs j ->
      ~ blocked jobs j t) ->
    NoDup enumT ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    check_transport_cert transport_cert = true ->
    EDFTransportCertSemantics
      (transport_class_backlog_holds T tasks offset jobs enumT codec)
      transport_cert ->
    check_transport_jobs_witness transport_cert transported_jobs = true ->
    (forall j,
      periodic_jobset T tasks offset jobs j ->
      In j transported_jobs) ->
    (forall t, taskset_periodic_dbf tasks enumT t <= t) ->
    schedulable_by_on
      (periodic_jobset T tasks offset jobs)
      (edf_scheduler (periodic_candidates_before T tasks offset jobs enumT codec))
      jobs 1.
Proof.
  intros T tasks offset enumT jobs codec transport_cert transported_jobs
         Hwf Hnonblocked HnodupT HenumT_complete HenumT_sound
         Htransport_check Htransport_sem Htransport_jobs Htransport_cover Hdbf.
  eapply periodic_edf_schedulable_by_classical_dbf_any_offset_with_no_carry_in_bridge;
    eauto.
  intros j Hj.
  eapply checked_transport_no_carry_in_for_all_periodic_jobs_from_backlog;
    eauto.
Qed.

Theorem edf_schedulability_decide_schedulable_by_on_with_checked_transport
    (ts : list ExtractedPeriodicTask)
    (codec :
      PeriodicCodec
        (extracted_task_scope ts)
        (extracted_periodic_tasks ts)
        (fun _ => 0)
        (extracted_periodic_jobs ts))
    (transport_cert : EDFTransportCert JobId)
    (transported_jobs : list JobId) :
  extracted_taskset_wf ts = true ->
  check_transport_cert transport_cert = true ->
  EDFTransportCertSemantics
    (transport_class_backlog_holds
       (extracted_task_scope ts)
       (extracted_periodic_tasks ts)
       (fun _ => 0)
       (extracted_periodic_jobs ts)
       (enumT_of_extracted_list ts)
       codec)
    transport_cert ->
  check_transport_jobs_witness transport_cert transported_jobs = true ->
  (forall j,
    periodic_jobset
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      j ->
    In j transported_jobs) ->
  edf_schedulability_decide ts = true ->
  schedulable_by_on
    (periodic_jobset
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts))
    (edf_scheduler
       (periodic_candidates_before
          (extracted_task_scope ts)
          (extracted_periodic_tasks ts)
          (fun _ => 0)
          (extracted_periodic_jobs ts)
          (enumT_of_extracted_list ts)
          codec))
    (extracted_periodic_jobs ts)
    1.
Proof.
  intros Hwf Htransport_check Htransport_sem
         Htransport_jobs Htransport_cover Hdec.
  eapply periodic_edf_schedulable_by_classical_dbf_with_checked_transport.
  - apply extracted_tasks_well_formed_on_enum.
    exact Hwf.
  - apply extracted_periodic_nonblocking.
  - apply enumT_of_extracted_list_nodup.
  - apply extracted_enum_complete.
  - apply extracted_enum_sound.
  - exact Htransport_check.
  - exact Htransport_sem.
  - exact Htransport_jobs.
  - exact Htransport_cover.
  - apply edf_schedulability_decide_true_global_dbf_ok.
    exact Hdec.
Qed.

Theorem edf_schedulability_decide_schedulable_by_on_with_offsets_and_checked_transport
    (ts : list ExtractedPeriodicTask)
    (codec :
      PeriodicCodec
        (extracted_task_scope ts)
        (extracted_periodic_tasks ts)
        (extracted_periodic_offsets ts)
        (extracted_offset_periodic_jobs ts))
    (transport_cert : EDFTransportCert JobId)
    (transported_jobs : list JobId) :
  extracted_taskset_wf ts = true ->
  check_transport_cert transport_cert = true ->
  EDFTransportCertSemantics
    (transport_class_backlog_holds
       (extracted_task_scope ts)
       (extracted_periodic_tasks ts)
       (extracted_periodic_offsets ts)
       (extracted_offset_periodic_jobs ts)
       (enumT_of_extracted_list ts)
       codec)
    transport_cert ->
  check_transport_jobs_witness transport_cert transported_jobs = true ->
  (forall j,
    periodic_jobset
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (extracted_periodic_offsets ts)
      (extracted_offset_periodic_jobs ts)
      j ->
    In j transported_jobs) ->
  edf_schedulability_decide ts = true ->
  schedulable_by_on
    (periodic_jobset
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (extracted_periodic_offsets ts)
      (extracted_offset_periodic_jobs ts))
    (edf_scheduler
       (periodic_candidates_before
          (extracted_task_scope ts)
          (extracted_periodic_tasks ts)
          (extracted_periodic_offsets ts)
          (extracted_offset_periodic_jobs ts)
          (enumT_of_extracted_list ts)
          codec))
    (extracted_offset_periodic_jobs ts)
    1.
Proof.
  intros Hwf Htransport_check Htransport_sem
         Htransport_jobs Htransport_cover Hdec.
  eapply periodic_edf_schedulable_by_classical_dbf_with_checked_transport.
  - apply extracted_tasks_well_formed_on_enum.
    exact Hwf.
  - apply extracted_offset_periodic_nonblocking.
  - apply enumT_of_extracted_list_nodup.
  - apply extracted_enum_complete.
  - apply extracted_enum_sound.
  - exact Htransport_check.
  - exact Htransport_sem.
  - exact Htransport_jobs.
  - exact Htransport_cover.
  - apply edf_schedulability_decide_true_global_dbf_ok.
    exact Hdec.
Qed.
