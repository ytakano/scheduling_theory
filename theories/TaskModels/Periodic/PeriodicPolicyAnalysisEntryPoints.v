From Stdlib Require Import Bool.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Analysis.Uniprocessor.BusyWindowSearch.
From RocqSched Require Import Analysis.Uniprocessor.EDFProcessorDemand.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Periodic.PeriodicCodec.
From RocqSched Require Import TaskModels.Periodic.PeriodicFiniteHorizon.
From RocqSched Require Import TaskModels.Periodic.PeriodicInfinite.
From RocqSched Require Import TaskModels.Periodic.PeriodicEnumeration.
From RocqSched Require Import TaskModels.Periodic.PeriodicWindowDemandBound.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFExtractionDecision.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFExtractionSoundness.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFExtractionTypes.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFBridge.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFFinalCertificateChecker.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFInfiniteBridge.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFPrefixCoherence.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFTransportWitnessChecker.
From RocqSched Require Import TaskModels.Periodic.PeriodicLLFInfiniteBridge.
From RocqSched Require Import TaskModels.Periodic.PeriodicPolicyAnalysis.
From RocqSched Require Import Uniprocessor.Generic.FinitePrefixScheduleWitness.
From RocqSched Require Import Uniprocessor.Policies.EDF.
From RocqSched Require Import Uniprocessor.Policies.LLF.

(** * Stable public entry points for policy-level periodic analysis

    The boolean checker is policy-neutral because it checks a feasibility
    witness.  The policy-specific part lives in the soundness theorem chosen by
    the caller. *)

Theorem check_periodic_policy_feasibility_edf_sound :
  forall ts cert sidecar,
    check_periodic_policy_feasibility PolicyEDF ts cert sidecar = true ->
    PeriodicHyperperiodCompletionTransportObligation
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (extracted_periodic_offsets ts)
      (extracted_offset_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      (extracted_offset_periodic_codec ts)
      sidecar.(checked_post_reset_window_target_certs) ->
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
            (extracted_offset_periodic_codec ts)))
      (extracted_offset_periodic_jobs ts)
      1.
Proof.
  intros ts cert sidecar Hcheck Hcompletion_transport.
  unfold check_periodic_policy_feasibility in Hcheck.
  eapply check_periodic_feasibility_checked_sidecar_sound_with_completion_transport_generated_rep;
    eauto.
Qed.

Theorem check_periodic_policy_feasibility_llf_sound :
  forall ts cert sidecar,
    check_periodic_policy_feasibility PolicyLLF ts cert sidecar = true ->
    (forall H j,
      periodic_jobset_upto
        (extracted_task_scope ts)
        (extracted_periodic_tasks ts)
        (extracted_periodic_offsets ts)
        (extracted_offset_periodic_jobs ts)
        H
        j ->
      job_abs_deadline (extracted_offset_periodic_jobs ts j) <= H /\
      exists t1 t2,
        busy_prefix_witness
          (generated_periodic_edf_schedule_upto
             (extracted_task_scope ts)
             (extracted_periodic_tasks ts)
             (extracted_periodic_offsets ts)
             (extracted_offset_periodic_jobs ts)
             H
             (enumT_of_extracted_list ts)
             (extracted_offset_periodic_codec ts))
          (job_abs_deadline (extracted_offset_periodic_jobs ts j))
          t1
          t2 /\
        periodic_edf_busy_prefix_bridge
          (extracted_task_scope ts)
          (extracted_periodic_tasks ts)
          (extracted_periodic_offsets ts)
          (extracted_offset_periodic_jobs ts)
          H
          (generated_periodic_edf_schedule_upto
             (extracted_task_scope ts)
             (extracted_periodic_tasks ts)
             (extracted_periodic_offsets ts)
             (extracted_offset_periodic_jobs ts)
             H
             (enumT_of_extracted_list ts)
             (extracted_offset_periodic_codec ts))
          j) ->
    schedulable_by_on
      (periodic_jobset
        (extracted_task_scope ts)
        (extracted_periodic_tasks ts)
        (extracted_periodic_offsets ts)
        (extracted_offset_periodic_jobs ts))
      (llf_scheduler
         (periodic_candidates_before
            (extracted_task_scope ts)
            (extracted_periodic_tasks ts)
            (extracted_periodic_offsets ts)
            (extracted_offset_periodic_jobs ts)
            (enumT_of_extracted_list ts)
            (extracted_offset_periodic_codec ts)))
      (extracted_offset_periodic_jobs ts)
      1.
Proof.
  intros ts cert sidecar Hcheck Hbridge.
  unfold check_periodic_policy_feasibility in Hcheck.
  unfold check_periodic_feasibility_checked_sidecar_extracted in Hcheck.
  destruct
    (check_periodic_edf_checked_sidecar_extracted_with_offsets_fields
       ts cert sidecar Hcheck)
    as [_ Hchecked].
  destruct
    (check_periodic_edf_checked_sidecar_with_jobs_fields
       ts
       (extracted_periodic_offsets ts)
       (extracted_offset_periodic_jobs ts)
       (extracted_offset_periodic_codec ts)
       cert
       sidecar
       Hchecked)
    as (_Hprefix_sem & _Hmatch & _Hreset_check & _Hperiod_eq
        & _Hhorizon_covers & _Hpost_reset_horizon
        & _Htransport_check & _Hbasis_nodup_check & _Hrep_check
        & _Hrep_generated_check & _Hrep_periodic_check
        & _Hresidue_check & _Hshift_check
        & _Hwindow_check & _Hpair_semantics & _Hpair_completion
        & _Hpost_reset_window_check & _Hpost_reset_basis_check
        & _Hpost_reset_list_check & Hdec).
  assert (Hwf : extracted_taskset_wf ts = true).
  {
    unfold edf_schedulability_decide in Hdec.
    apply andb_true_iff in Hdec.
    exact (proj1 Hdec).
  }
  eapply periodic_llf_schedulable_by_classical_dbf_any_offset_on.
  - apply extracted_tasks_well_formed_on_enum.
    exact Hwf.
  - apply extracted_offset_periodic_nonblocking.
  - apply enumT_of_extracted_list_nodup.
  - apply extracted_enum_complete.
  - apply extracted_enum_sound.
  - exact Hbridge.
  - apply edf_schedulability_decide_true_global_dbf_ok.
    exact Hdec.
Qed.
