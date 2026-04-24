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

Definition extracted_taskset_nonempty
    (ts : list ExtractedPeriodicTask) : bool :=
  Nat.ltb 0 (length ts).

Definition extracted_periodic_codec
    (ts : list ExtractedPeriodicTask) :
  PeriodicCodec
    (extracted_task_scope ts)
    (extracted_periodic_tasks ts)
    (fun _ => 0)
    (extracted_periodic_jobs ts).
Proof.
  destruct ts as [|τ ts'].
  - refine
      (mkPeriodicCodec
         (extracted_task_scope [])
         (extracted_periodic_tasks [])
         (fun _ => 0)
         (extracted_periodic_jobs [])
         (fun _ _ => 0)
         _ _).
    + intros τ k Hτ.
      unfold extracted_task_scope in Hτ.
      cbn in Hτ.
      lia.
    + intros j Hj.
      unfold periodic_jobset, extracted_task_scope in Hj.
      cbn in Hj.
      lia.
  - apply zero_offset_periodic_codec_of_tasks.
    + apply enumT_of_extracted_list_nodup.
    + apply extracted_enum_complete.
    + apply extracted_enum_sound.
    + unfold enumT_of_extracted_list.
      rewrite length_seq.
      cbn.
      lia.
Defined.

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
  && check_prefix_slots_match_generated_edf_fast
       (extracted_task_scope ts)
       (extracted_periodic_tasks ts)
       (fun _ => 0)
       (extracted_periodic_jobs ts)
       (enumT_of_extracted_list ts)
       codec
       cert.(cert_prefix)
  && check_transport_cert cert.(cert_transport)
  && check_transport_basis_nodup cert.(cert_transport)
  && check_transport_classes_rep_backlog
       cert.(cert_prefix)
       cert.(cert_transport).(transport_classes)
       sidecar.(checked_class_relevant_jobs)
  && check_transport_classes_rep_backlog_generated
       (extracted_task_scope ts)
       (extracted_periodic_tasks ts)
       (fun _ => 0)
       (extracted_periodic_jobs ts)
       (enumT_of_extracted_list ts)
       codec
       cert.(cert_prefix)
       cert.(cert_transport).(transport_classes)
  && check_transport_classes_rep_periodic_generated
       (extracted_task_scope ts)
       (extracted_periodic_tasks ts)
       (fun _ => 0)
       (extracted_periodic_jobs ts)
       (enumT_of_extracted_list ts)
       codec
       cert.(cert_transport).(transport_classes)
  && check_periodic_transport_residue_coverage
       cert.(cert_transport)
       (periodic_transport_residue_jobs
          (extracted_task_scope ts)
          (extracted_periodic_tasks ts)
          (fun _ => 0)
          (extracted_periodic_jobs ts)
          (enumT_of_extracted_list ts)
          codec
          cert.(cert_transport).(transport_period))
  && check_window_transport_targets_complete_with_pairs
       (extracted_task_scope ts)
       (extracted_periodic_tasks ts)
       (fun _ => 0)
       (extracted_periodic_jobs ts)
       (enumT_of_extracted_list ts)
       codec
       cert.(cert_transport)
       sidecar.(checked_window_target_certs)
  && check_window_generated_pair_semantics_all
       (extracted_task_scope ts)
       (extracted_periodic_tasks ts)
       (fun _ => 0)
       (extracted_periodic_jobs ts)
       (enumT_of_extracted_list ts)
       codec
       cert.(cert_transport)
       sidecar.(checked_window_target_certs)
  && check_window_generated_pair_completion_all
       (extracted_task_scope ts)
       (extracted_periodic_tasks ts)
       (fun _ => 0)
       (extracted_periodic_jobs ts)
       (enumT_of_extracted_list ts)
       codec
       sidecar.(checked_window_target_certs)
  && edf_schedulability_decide ts.

Definition check_periodic_edf_checked_sidecar_extracted
    (ts : list ExtractedPeriodicTask)
    (cert : EDFInfiniteCert JobId)
    (sidecar : PeriodicEDFCheckedSidecarCert) : bool :=
  extracted_taskset_nonempty ts
  && check_periodic_edf_checked_sidecar
       ts (extracted_periodic_codec ts) cert sidecar.

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
    check_transport_basis_nodup cert.(cert_transport) = true
    /\
    check_transport_classes_rep_backlog
      cert.(cert_prefix)
      cert.(cert_transport).(transport_classes)
      sidecar.(checked_class_relevant_jobs) = true
    /\
    check_transport_classes_rep_backlog_generated
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      codec
      cert.(cert_prefix)
      cert.(cert_transport).(transport_classes) = true
    /\
    check_transport_classes_rep_periodic_generated
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      codec
      cert.(cert_transport).(transport_classes) = true
    /\
    check_periodic_transport_residue_coverage
      cert.(cert_transport)
      (periodic_transport_residue_jobs
        (extracted_task_scope ts)
        (extracted_periodic_tasks ts)
        (fun _ => 0)
        (extracted_periodic_jobs ts)
        (enumT_of_extracted_list ts)
        codec
        cert.(cert_transport).(transport_period)) = true
    /\
    check_window_transport_targets_complete_with_pairs
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      codec
      cert.(cert_transport)
      sidecar.(checked_window_target_certs) = true
    /\
    check_window_generated_pair_semantics_all
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      codec
      cert.(cert_transport)
      sidecar.(checked_window_target_certs) = true
    /\
    check_window_generated_pair_completion_all
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      codec
      sidecar.(checked_window_target_certs) = true
    /\
    edf_schedulability_decide ts = true.
Proof.
  intros ts codec cert sidecar Hcheck.
  unfold check_periodic_edf_checked_sidecar in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as
    [[[[[[[[[[[Hprefix Hfast] Htransport] Hbasis_nodup] Hrep]
        Hrep_generated] Hrep_periodic] Hcoverage] Hwindow]
        Hpair_semantics] Hpair_completion] Hdec].
  repeat split; try assumption.
  eapply check_prefix_slots_match_generated_edf_fast_sound.
  exact Hfast.
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
    as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hdec).
  unfold edf_schedulability_decide in Hdec.
  apply andb_true_iff in Hdec.
  exact (proj1 Hdec).
Qed.

Lemma check_periodic_edf_checked_sidecar_extracted_fields :
  forall ts cert sidecar,
    check_periodic_edf_checked_sidecar_extracted ts cert sidecar = true ->
    extracted_taskset_nonempty ts = true
    /\
    check_periodic_edf_checked_sidecar
      ts (extracted_periodic_codec ts) cert sidecar = true.
Proof.
  intros ts cert sidecar Hcheck.
  unfold check_periodic_edf_checked_sidecar_extracted in Hcheck.
  apply andb_true_iff in Hcheck.
  exact Hcheck.
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
  intros ts codec cert sidecar Hcheck Hrep Hwindow.
  destruct
    (check_periodic_edf_checked_sidecar_fields
       ts codec cert sidecar Hcheck)
    as (_ & _ & Htransport_check & _ & Hrep_check & _ & _
        & Hcoverage_check & Hwindow_check & _ & _ & Hdec).
  eapply edf_schedulability_decide_schedulable_by_on_with_periodic_transport_coverage.
  - eapply check_periodic_edf_checked_sidecar_wf; eauto.
  - exact Htransport_check.
  - exact Hrep.
  - exact Hrep_check.
  - eapply checked_periodic_transport_residue_coverage_sound.
    + exact Htransport_check.
    + apply extracted_enum_complete.
    + exact Hcoverage_check.
  - eapply check_window_transport_targets_complete_with_pairs_targets.
    exact Hwindow_check.
  - exact Hwindow.
  - exact Hdec.
Qed.

Theorem check_periodic_edf_checked_sidecar_extracted_sound :
  forall ts cert sidecar,
    check_periodic_edf_checked_sidecar_extracted ts cert sidecar = true ->
    TransportClassRepresentativeObligation
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      (extracted_periodic_codec ts)
      cert.(cert_prefix)
      cert.(cert_transport).(transport_classes)
      sidecar.(checked_class_relevant_jobs) ->
    WindowTransportTargetsObligation
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      (extracted_periodic_codec ts)
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
            (extracted_periodic_codec ts)))
      (extracted_periodic_jobs ts)
      1.
Proof.
  intros ts cert sidecar Hcheck Hrep Hwindow.
  destruct
    (check_periodic_edf_checked_sidecar_extracted_fields
       ts cert sidecar Hcheck)
    as [_ Hchecked].
  eapply check_periodic_edf_checked_sidecar_sound; eauto.
Qed.
