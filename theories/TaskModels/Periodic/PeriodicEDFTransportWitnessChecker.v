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
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFBacklogBridgeChecker.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFExtractionDecision.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFExtractionSoundness.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFExtractionTypes.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFGeneratedPrefixChecker.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFInfiniteBridge.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFNoCarryInSupply.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFPrefixChecker.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFPrefixCoherence.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFTransportChecker.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFTransportCoverageChecker.
From RocqSched Require Import TaskModels.Periodic.PeriodicInfinite.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Periodic.PeriodicWindowDemandBound.
From RocqSched Require Import Uniprocessor.Policies.EDF.

Import ListNotations.

(** Boolean witness layer for transport classes.

    A transport class names a representative job.  This checker verifies that
    each class representative has a prefix backlog-free witness.  A separate
    algebra obligation states that such representative witnesses transport to
    the concrete shifted jobs referenced by the transport table. *)

Definition check_transport_class_rep_backlog
    (prefix_cert : EDFPrefixCert JobId)
    (cls : EDFTransportClass JobId)
    (relevant_jobs : list JobId) : bool :=
  check_prefix_backlog_free_before_release
    prefix_cert cls.(transport_rep_job) relevant_jobs.

Fixpoint check_transport_classes_rep_backlog
    (prefix_cert : EDFPrefixCert JobId)
    (classes : list (EDFTransportClass JobId))
    (class_relevant_jobs : list (list JobId)) : bool :=
  match classes, class_relevant_jobs with
  | [], [] => true
  | cls :: classes', relevant :: relevant' =>
      check_transport_class_rep_backlog prefix_cert cls relevant
      && check_transport_classes_rep_backlog prefix_cert classes' relevant'
  | _, _ => false
  end.

Record TransportClassRepresentativeObligation
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (enumT : list TaskId)
    (codec : PeriodicCodec T tasks offset jobs)
    (prefix_cert : EDFPrefixCert JobId)
    (classes : list (EDFTransportClass JobId))
    (class_relevant_jobs : list (list JobId)) : Prop := {
  transport_rep_prefix_valid :
    valid_schedule jobs 1
      (generated_periodic_edf_prefix T tasks offset jobs enumT codec prefix_cert);
  transport_rep_prefix_semantic_check :
    check_prefix_cert_semantic jobs prefix_cert = true;
  transport_rep_prefix_matches_generated :
    check_prefix_slots_match_generated_edf
      T tasks offset jobs enumT codec prefix_cert = true;
  transport_rep_periodic_job :
    forall i cls relevant,
      nth_error classes i = Some cls ->
      nth_error class_relevant_jobs i = Some relevant ->
      periodic_jobset T tasks offset jobs cls.(transport_rep_job);
  transport_rep_relevant_coverage :
    forall i cls relevant x,
      nth_error classes i = Some cls ->
      nth_error class_relevant_jobs i = Some relevant ->
      periodic_jobset_deadline_between
        T tasks offset jobs
        0 (job_abs_deadline (jobs cls.(transport_rep_job))) x ->
      job_release (jobs x) < job_release (jobs cls.(transport_rep_job)) ->
      In x relevant
}.

Record TransportClassAlgebraObligation
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (enumT : list TaskId)
    (codec : PeriodicCodec T tasks offset jobs)
    (prefix_cert : EDFPrefixCert JobId) : Prop := {
  transport_class_algebra_sound :
    forall j cls shift,
      periodic_edf_backlog_free_before_release
        T tasks offset jobs prefix_cert.(prefix_horizon)
        (generated_periodic_edf_prefix T tasks offset jobs enumT codec prefix_cert)
        cls.(transport_rep_job) ->
      transport_class_backlog_holds
        T tasks offset jobs enumT codec j cls shift
}.

Lemma check_transport_classes_rep_backlog_sound :
  forall prefix_cert classes class_relevant_jobs i cls,
    check_transport_classes_rep_backlog
      prefix_cert classes class_relevant_jobs = true ->
    nth_error classes i = Some cls ->
    exists relevant,
      nth_error class_relevant_jobs i = Some relevant /\
      check_transport_class_rep_backlog prefix_cert cls relevant = true.
Proof.
  intros prefix_cert classes.
  induction classes as [|cls0 classes IH];
    intros class_relevant_jobs i cls Hcheck Hcls.
  - destruct i; discriminate.
  - destruct class_relevant_jobs as [|relevant0 relevant_jobs]; [discriminate|].
    destruct i as [|i].
    + cbn in Hcheck, Hcls.
      inversion Hcls; subst.
      apply andb_true_iff in Hcheck.
      destruct Hcheck as [Hhead _].
      exists relevant0.
      split; [reflexivity|exact Hhead].
    + cbn in Hcheck, Hcls.
      apply andb_true_iff in Hcheck.
      destruct Hcheck as [_ Htail].
      cbn.
      eapply IH; eauto.
Qed.

Theorem checked_transport_class_rep_backlog_sound :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs)
         prefix_cert classes class_relevant_jobs i cls,
    TransportClassRepresentativeObligation
      T tasks offset jobs enumT codec
      prefix_cert classes class_relevant_jobs ->
    check_transport_classes_rep_backlog
      prefix_cert classes class_relevant_jobs = true ->
    nth_error classes i = Some cls ->
    periodic_edf_backlog_free_before_release
      T tasks offset jobs prefix_cert.(prefix_horizon)
      (generated_periodic_edf_prefix T tasks offset jobs enumT codec prefix_cert)
      cls.(transport_rep_job).
Proof.
  intros T tasks offset jobs enumT codec prefix_cert classes
         class_relevant_jobs i cls Hobligation Hcheck Hcls.
  destruct
    (check_transport_classes_rep_backlog_sound
       prefix_cert classes class_relevant_jobs i cls Hcheck Hcls)
    as [relevant [Hrelevant Hrep_check]].
  unfold check_transport_class_rep_backlog in Hrep_check.
  eapply checked_generated_prefix_backlog_free_before_release.
  - exact (transport_rep_prefix_valid
             T tasks offset jobs enumT codec
             prefix_cert classes class_relevant_jobs Hobligation).
  - eapply transport_rep_periodic_job; eauto.
  - exact (transport_rep_prefix_semantic_check
             T tasks offset jobs enumT codec
             prefix_cert classes class_relevant_jobs Hobligation).
  - exact (transport_rep_prefix_matches_generated
             T tasks offset jobs enumT codec
             prefix_cert classes class_relevant_jobs Hobligation).
  - exact Hrep_check.
  - intros x Hbetween Hrelease.
    eapply transport_rep_relevant_coverage; eauto.
Qed.

Theorem checked_transport_cert_semantics_from_rep_backlog :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs)
         prefix_cert transport_cert class_relevant_jobs,
    TransportClassRepresentativeObligation
      T tasks offset jobs enumT codec
      prefix_cert transport_cert.(transport_classes) class_relevant_jobs ->
    TransportClassAlgebraObligation
      T tasks offset jobs enumT codec prefix_cert ->
    check_transport_classes_rep_backlog
      prefix_cert transport_cert.(transport_classes) class_relevant_jobs = true ->
    EDFTransportCertSemantics
      (transport_class_backlog_holds T tasks offset jobs enumT codec)
      transport_cert.
Proof.
  intros T tasks offset jobs enumT codec prefix_cert transport_cert
         class_relevant_jobs Hrep Halgebra Hcheck.
  constructor.
  intros i j class_id shift cls Hjob Hclass Hshift Hcls.
  eapply transport_class_algebra_sound; eauto.
  eapply checked_transport_class_rep_backlog_sound; eauto.
Qed.

Theorem periodic_edf_schedulable_by_classical_dbf_with_checked_transport_witnesses :
  forall T tasks offset enumT jobs
         (codec : PeriodicCodec T tasks offset jobs)
         prefix_cert transport_cert candidate_jobs class_relevant_jobs,
    well_formed_periodic_tasks_on T tasks ->
    (forall j t,
      periodic_jobset T tasks offset jobs j ->
      ~ blocked jobs j t) ->
    NoDup enumT ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    (forall τ, In τ enumT -> offset τ = 0) ->
    check_transport_cert transport_cert = true ->
    TransportClassRepresentativeObligation
      T tasks offset jobs enumT codec
      prefix_cert transport_cert.(transport_classes) class_relevant_jobs ->
    TransportClassAlgebraObligation
      T tasks offset jobs enumT codec prefix_cert ->
    check_transport_classes_rep_backlog
      prefix_cert transport_cert.(transport_classes) class_relevant_jobs = true ->
    TransportCoverageObligation T tasks offset jobs candidate_jobs ->
    check_periodic_jobs_covered_by_transport
      transport_cert candidate_jobs = true ->
    (forall t, taskset_periodic_dbf tasks enumT t <= t) ->
    schedulable_by_on
      (periodic_jobset T tasks offset jobs)
      (edf_scheduler (periodic_candidates_before T tasks offset jobs enumT codec))
      jobs 1.
Proof.
  intros T tasks offset enumT jobs codec prefix_cert transport_cert
         candidate_jobs class_relevant_jobs
         Hwf Hnonblocked HnodupT HenumT_complete HenumT_sound Hoff
         Htransport_check Hrep Halgebra Hrep_check
         Hcoverage Hcoverage_check Hdbf.
  eapply periodic_edf_schedulable_by_classical_dbf_with_checked_transport_coverage.
  - exact Hwf.
  - exact Hnonblocked.
  - exact HnodupT.
  - exact HenumT_complete.
  - exact HenumT_sound.
  - exact Hoff.
  - exact Htransport_check.
  - eapply checked_transport_cert_semantics_from_rep_backlog; eauto.
  - exact Hcoverage.
  - exact Hcoverage_check.
  - exact Hdbf.
Qed.

Theorem edf_schedulability_decide_schedulable_by_on_with_checked_transport_witnesses
    (ts : list ExtractedPeriodicTask)
    (codec :
      PeriodicCodec
        (extracted_task_scope ts)
        (extracted_periodic_tasks ts)
        (fun _ => 0)
        (extracted_periodic_jobs ts))
    (prefix_cert : EDFPrefixCert JobId)
    (transport_cert : EDFTransportCert JobId)
    (candidate_jobs : list JobId)
    (class_relevant_jobs : list (list JobId)) :
  extracted_taskset_wf ts = true ->
  check_transport_cert transport_cert = true ->
  TransportClassRepresentativeObligation
    (extracted_task_scope ts)
    (extracted_periodic_tasks ts)
    (fun _ => 0)
    (extracted_periodic_jobs ts)
    (enumT_of_extracted_list ts)
    codec prefix_cert transport_cert.(transport_classes) class_relevant_jobs ->
  TransportClassAlgebraObligation
    (extracted_task_scope ts)
    (extracted_periodic_tasks ts)
    (fun _ => 0)
    (extracted_periodic_jobs ts)
    (enumT_of_extracted_list ts)
    codec prefix_cert ->
  check_transport_classes_rep_backlog
    prefix_cert transport_cert.(transport_classes) class_relevant_jobs = true ->
  TransportCoverageObligation
    (extracted_task_scope ts)
    (extracted_periodic_tasks ts)
    (fun _ => 0)
    (extracted_periodic_jobs ts)
    candidate_jobs ->
  check_periodic_jobs_covered_by_transport
    transport_cert candidate_jobs = true ->
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
  intros Hwf Htransport_check Hrep Halgebra Hrep_check
         Hcoverage Hcoverage_check Hdec.
  eapply periodic_edf_schedulable_by_classical_dbf_with_checked_transport_witnesses.
  - apply extracted_tasks_well_formed_on_enum.
    exact Hwf.
  - apply extracted_periodic_nonblocking.
  - apply enumT_of_extracted_list_nodup.
  - apply extracted_enum_complete.
  - apply extracted_enum_sound.
  - apply extracted_zero_offset.
  - exact Htransport_check.
  - exact Hrep.
  - exact Halgebra.
  - exact Hrep_check.
  - exact Hcoverage.
  - exact Hcoverage_check.
  - apply edf_schedulability_decide_true_global_dbf_ok.
    exact Hdec.
Qed.
