From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import TaskModels.Periodic.PeriodicCodec.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFCertificate.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFExtractionDecision.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFExtractionSoundness.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFExtractionTypes.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFGeneratedPrefixChecker.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFInfiniteBridge.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFPrefixChecker.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFPrefixCoherence.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFTransportCoverageChecker.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFTransportWitnessChecker.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFWindowTransportChecker.
From RocqSched Require Import TaskModels.Periodic.PeriodicInfinite.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import Uniprocessor.Policies.EDF.

Import ListNotations.

(** Top-level checked periodic EDF certificate wrapper.

    This file collects the boolean checkers that have been proved so far into a
    single extraction-facing entry point.  Coverage of all periodic jobs and the
    remaining schedule-level window transport facts are still explicit semantic
    obligations; the purpose here is to make the verified boolean frontier
    visible as one checker before exposing it to extraction. *)

Record PeriodicEDFCheckedSidecarCert := {
  checked_candidate_jobs : list JobId;
  checked_class_relevant_jobs : list (list JobId);
  checked_window_target_certs : list EDFWindowTransportTargetCert
}.

Definition check_periodic_edf_checked_sidecar
    (ts : list ExtractedPeriodicTask)
    (codec :
      PeriodicCodec
        (extracted_task_scope ts)
        (extracted_periodic_tasks ts)
        (fun _ => 0)
        (extracted_periodic_jobs ts))
    (cert : EDFInfiniteCert JobId)
    (sidecar : PeriodicEDFCheckedSidecarCert) : bool :=
  check_prefix_cert_semantic
    (extracted_periodic_jobs ts)
    cert.(cert_prefix)
  && check_prefix_slots_match_generated_edf
       (extracted_task_scope ts)
       (extracted_periodic_tasks ts)
       (fun _ => 0)
       (extracted_periodic_jobs ts)
       (enumT_of_extracted_list ts)
       codec
       cert.(cert_prefix)
  && check_transport_cert cert.(cert_transport)
  && check_transport_classes_rep_backlog
       cert.(cert_prefix)
       cert.(cert_transport).(transport_classes)
       sidecar.(checked_class_relevant_jobs)
  && check_periodic_jobs_covered_by_transport
       cert.(cert_transport)
       sidecar.(checked_candidate_jobs)
  && check_window_transport_targets
       (extracted_periodic_jobs ts)
       cert.(cert_transport)
       sidecar.(checked_window_target_certs)
  && edf_schedulability_decide ts.

Lemma check_periodic_edf_checked_sidecar_fields :
  forall ts
         (codec :
          PeriodicCodec
            (extracted_task_scope ts)
            (extracted_periodic_tasks ts)
            (fun _ => 0)
            (extracted_periodic_jobs ts))
         cert sidecar,
    check_periodic_edf_checked_sidecar ts codec cert sidecar = true ->
    check_prefix_cert_semantic
      (extracted_periodic_jobs ts)
      cert.(cert_prefix) = true
    /\
    check_prefix_slots_match_generated_edf
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      codec
      cert.(cert_prefix) = true
    /\
    check_transport_cert cert.(cert_transport) = true
    /\
    check_transport_classes_rep_backlog
      cert.(cert_prefix)
      cert.(cert_transport).(transport_classes)
      sidecar.(checked_class_relevant_jobs) = true
    /\
    check_periodic_jobs_covered_by_transport
      cert.(cert_transport)
      sidecar.(checked_candidate_jobs) = true
    /\
    check_window_transport_targets
      (extracted_periodic_jobs ts)
      cert.(cert_transport)
      sidecar.(checked_window_target_certs) = true
    /\
    edf_schedulability_decide ts = true.
Proof.
  intros ts codec cert sidecar Hcheck.
  unfold check_periodic_edf_checked_sidecar in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  tauto.
Qed.

Lemma check_periodic_edf_checked_sidecar_wf :
  forall ts
         (codec :
          PeriodicCodec
            (extracted_task_scope ts)
            (extracted_periodic_tasks ts)
            (fun _ => 0)
            (extracted_periodic_jobs ts))
         cert sidecar,
    check_periodic_edf_checked_sidecar ts codec cert sidecar = true ->
    extracted_taskset_wf ts = true.
Proof.
  intros ts codec cert sidecar Hcheck.
  destruct
    (check_periodic_edf_checked_sidecar_fields
       ts codec cert sidecar Hcheck)
    as [_ [_ [_ [_ [_ [_ Hdec]]]]]].
  unfold edf_schedulability_decide in Hdec.
  apply andb_true_iff in Hdec.
  exact (proj1 Hdec).
Qed.

Theorem check_periodic_edf_checked_sidecar_sound :
  forall ts
         (codec :
          PeriodicCodec
            (extracted_task_scope ts)
            (extracted_periodic_tasks ts)
            (fun _ => 0)
            (extracted_periodic_jobs ts))
         cert sidecar,
    check_periodic_edf_checked_sidecar ts codec cert sidecar = true ->
    TransportClassRepresentativeObligation
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      codec
      cert.(cert_prefix)
      cert.(cert_transport).(transport_classes)
      sidecar.(checked_class_relevant_jobs) ->
    TransportCoverageObligation
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      sidecar.(checked_candidate_jobs) ->
    WindowTransportTargetsObligation
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      codec
      cert.(cert_prefix)
      cert.(cert_transport)
      sidecar.(checked_window_target_certs) ->
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
  intros ts codec cert sidecar Hcheck Hrep Hcoverage Hwindow.
  destruct
    (check_periodic_edf_checked_sidecar_fields
       ts codec cert sidecar Hcheck)
    as [_ [_ [Htransport_check
        [Hrep_check [Hcoverage_check [Hwindow_check Hdec]]]]]].
  eapply edf_schedulability_decide_schedulable_by_on_with_checked_window_transport_witnesses.
  - eapply check_periodic_edf_checked_sidecar_wf; eauto.
  - exact Htransport_check.
  - exact Hrep.
  - exact Hrep_check.
  - exact Hcoverage.
  - exact Hcoverage_check.
  - exact Hwindow_check.
  - exact Hwindow.
  - exact Hdec.
Qed.
