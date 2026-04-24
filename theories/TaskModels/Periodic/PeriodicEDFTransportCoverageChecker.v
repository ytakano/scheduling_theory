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
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFInfiniteBridge.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFPrefixCoherence.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFTransportChecker.
From RocqSched Require Import TaskModels.Periodic.PeriodicInfinite.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import Uniprocessor.Policies.EDF.

Import ListNotations.

(** Boolean coverage layer for transport certificates.

    The checker verifies that a finite candidate-job list is covered by the
    transport basis.  Semantic completeness of that candidate list remains a
    small adapter obligation: the common layer does not prescribe how a concrete
    certificate generator enumerates all periodic jobs it wants to cover. *)

Definition check_transport_coverage_list
    (transport_cert : EDFTransportCert JobId)
    (candidate_jobs : list JobId) : bool :=
  check_transport_jobs_witness transport_cert candidate_jobs.

Definition check_periodic_jobs_covered_by_transport
    (transport_cert : EDFTransportCert JobId)
    (candidate_jobs : list JobId) : bool :=
  check_transport_coverage_list transport_cert candidate_jobs.

Definition periodic_transport_residue_jobs
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (enumT : list TaskId)
    (codec : PeriodicCodec T tasks offset jobs)
    (period : Time) : list JobId :=
  flat_map
    (fun τ =>
       map
         (global_periodic_job_id_of T tasks offset jobs codec τ)
         (seq 0 period))
    enumT.

Definition check_periodic_transport_residue_coverage
    (transport_cert : EDFTransportCert JobId)
    (residue_jobs : list JobId) : bool :=
  Nat.ltb 0 transport_cert.(transport_period)
  && check_transport_jobs_witness transport_cert residue_jobs.

Definition check_transport_residue_shifts
    (transport_cert : EDFTransportCert JobId) : bool :=
  forallb
    (fun shift => Nat.eqb shift transport_cert.(transport_period))
    transport_cert.(transport_job_shift).

Record TransportCoverageObligation
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (candidate_jobs : list JobId) : Prop := {
  transport_coverage_complete :
    forall j,
      periodic_jobset T tasks offset jobs j ->
      In j candidate_jobs
}.

Record PeriodicTransportCoverageObligation
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (codec : PeriodicCodec T tasks offset jobs)
    (transport_cert : EDFTransportCert JobId) : Prop := {
  periodic_transport_coverage_complete :
    forall j,
      periodic_jobset T tasks offset jobs j ->
      exists i class_id cls shift,
        nth_error transport_cert.(transport_basis_jobs) i =
          Some
            (global_periodic_job_id_of
               T tasks offset jobs codec
               (job_task (jobs j))
               (job_index (jobs j) mod transport_cert.(transport_period)))
        /\
        nth_error transport_cert.(transport_job_class) i = Some class_id
        /\
        nth_error transport_cert.(transport_classes) class_id = Some cls
        /\
        nth_error transport_cert.(transport_job_shift) i = Some shift
}.

Lemma check_transport_coverage_list_sound :
  forall transport_cert candidate_jobs j,
    check_transport_coverage_list transport_cert candidate_jobs = true ->
    In j candidate_jobs ->
    exists i,
      nth_error transport_cert.(transport_basis_jobs) i = Some j.
Proof.
  intros transport_cert candidate_jobs j Hcheck Hin.
  unfold check_transport_coverage_list,
         check_transport_jobs_witness in Hcheck.
  apply forallb_forall with (x := j) in Hcheck; [|exact Hin].
  unfold check_transport_job_witness in Hcheck.
  eapply check_job_in_basis_sound; eauto.
Qed.

Theorem checked_transport_coverage_sound :
  forall T tasks offset jobs transport_cert candidate_jobs,
    TransportCoverageObligation T tasks offset jobs candidate_jobs ->
    check_periodic_jobs_covered_by_transport
      transport_cert candidate_jobs = true ->
    forall j,
      periodic_jobset T tasks offset jobs j ->
      In j candidate_jobs /\
      exists i,
        nth_error transport_cert.(transport_basis_jobs) i = Some j.
Proof.
  intros T tasks offset jobs transport_cert candidate_jobs
         Hcoverage Hcheck j Hj.
  pose proof
    (transport_coverage_complete
       T tasks offset jobs candidate_jobs Hcoverage j Hj) as Hin.
  split; [exact Hin|].
  eapply check_transport_coverage_list_sound; eauto.
Qed.

Lemma periodic_transport_residue_jobs_complete :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs) period j,
    0 < period ->
    (forall τ, T τ -> In τ enumT) ->
    periodic_jobset T tasks offset jobs j ->
    In
      (global_periodic_job_id_of
         T tasks offset jobs codec
         (job_task (jobs j))
         (job_index (jobs j) mod period))
      (periodic_transport_residue_jobs
         T tasks offset jobs enumT codec period).
Proof.
  intros T tasks offset jobs enumT codec period j Hperiod Henum Hjob.
  unfold periodic_transport_residue_jobs.
  apply in_flat_map.
  exists (job_task (jobs j)).
  split.
  - apply Henum.
    unfold periodic_jobset in Hjob.
    exact (proj1 Hjob).
  - apply in_map.
    rewrite in_seq.
    split; [lia|].
    apply Nat.mod_upper_bound.
    lia.
Qed.

Theorem checked_periodic_transport_residue_coverage_sound :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs) transport_cert,
    check_transport_cert transport_cert = true ->
    (forall τ, T τ -> In τ enumT) ->
    check_periodic_transport_residue_coverage
      transport_cert
      (periodic_transport_residue_jobs
         T tasks offset jobs enumT codec
         transport_cert.(transport_period)) = true ->
    PeriodicTransportCoverageObligation
      T tasks offset jobs codec transport_cert.
Proof.
  intros T tasks offset jobs enumT codec transport_cert
         Htransport_check Henum Hcoverage_check.
  unfold check_periodic_transport_residue_coverage in Hcoverage_check.
  apply andb_true_iff in Hcoverage_check.
  destruct Hcoverage_check as [Hperiod_check Hresidue_check].
  apply Nat.ltb_lt in Hperiod_check.
  constructor.
  intros j Hjob.
  set (rep :=
    global_periodic_job_id_of
      T tasks offset jobs codec
      (job_task (jobs j))
      (job_index (jobs j) mod transport_cert.(transport_period))).
  assert (Hrep_in :
    In rep
      (periodic_transport_residue_jobs
         T tasks offset jobs enumT codec
         transport_cert.(transport_period))).
  {
    subst rep.
    eapply periodic_transport_residue_jobs_complete; eauto.
  }
  destruct
    (check_transport_coverage_list_sound
       transport_cert
       (periodic_transport_residue_jobs
          T tasks offset jobs enumT codec
          transport_cert.(transport_period))
       rep Hresidue_check Hrep_in)
    as [i Hbasis].
  pose proof (check_transport_cert_fields JobId transport_cert Htransport_check)
    as [_ [Hclass_len [Hshift_len Hclass_bound]]].
  assert (Hi : i < length transport_cert.(transport_basis_jobs)).
  {
    apply nth_error_Some.
    intro Hnone.
    rewrite Hbasis in Hnone.
    discriminate.
  }
  assert (Hclass_lt : i < length transport_cert.(transport_job_class)) by lia.
  assert (Hshift_lt : i < length transport_cert.(transport_job_shift)) by lia.
  destruct
    (nth_error_exists_of_lt nat transport_cert.(transport_job_class)
       i Hclass_lt)
    as [class_id Hclass].
  destruct
    (nth_error_exists_of_lt nat transport_cert.(transport_job_shift)
       i Hshift_lt)
    as [shift Hshift].
  assert (Hclass_id_in : In class_id transport_cert.(transport_job_class)).
  { eapply nth_error_In. exact Hclass. }
  pose proof (Hclass_bound class_id Hclass_id_in) as Hclass_id_lt.
  destruct
    (nth_error_exists_of_lt (EDFTransportClass JobId)
       transport_cert.(transport_classes) class_id Hclass_id_lt)
    as [cls Hcls].
  exists i, class_id, cls, shift.
  repeat split; assumption.
Qed.

Lemma check_transport_residue_shifts_sound :
  forall transport_cert i shift,
    check_transport_residue_shifts transport_cert = true ->
    nth_error transport_cert.(transport_job_shift) i = Some shift ->
    shift = transport_cert.(transport_period).
Proof.
  intros transport_cert i shift Hcheck Hshift.
  unfold check_transport_residue_shifts in Hcheck.
  apply forallb_forall with (x := shift) in Hcheck.
  - apply Nat.eqb_eq. exact Hcheck.
  - eapply nth_error_In. exact Hshift.
Qed.

Theorem periodic_edf_schedulable_by_classical_dbf_with_checked_transport_coverage :
  forall T tasks offset enumT jobs
         (codec : PeriodicCodec T tasks offset jobs)
         transport_cert candidate_jobs,
    well_formed_periodic_tasks_on T tasks ->
    (forall j t,
      periodic_jobset T tasks offset jobs j ->
      ~ blocked jobs j t) ->
    NoDup enumT ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    (forall τ, In τ enumT -> offset τ = 0) ->
    check_transport_cert transport_cert = true ->
    EDFTransportCertSemantics
      (transport_class_backlog_holds T tasks offset jobs enumT codec)
      transport_cert ->
    TransportCoverageObligation T tasks offset jobs candidate_jobs ->
    check_periodic_jobs_covered_by_transport
      transport_cert candidate_jobs = true ->
    (forall t, taskset_periodic_dbf tasks enumT t <= t) ->
    schedulable_by_on
      (periodic_jobset T tasks offset jobs)
      (edf_scheduler (periodic_candidates_before T tasks offset jobs enumT codec))
      jobs 1.
Proof.
  intros T tasks offset enumT jobs codec transport_cert candidate_jobs
         Hwf Hnonblocked HnodupT HenumT_complete HenumT_sound Hoff
         Htransport_check Htransport_sem Hcoverage Hcoverage_check Hdbf.
  eapply periodic_edf_schedulable_by_classical_dbf_with_no_carry_in_bridge;
    eauto.
  intros j Hj.
  eapply checked_transport_no_carry_in_for_list_from_backlog.
  - exact Hwf.
  - exact HenumT_complete.
  - exact HenumT_sound.
  - exact Htransport_check.
  - exact Htransport_sem.
  - unfold check_periodic_jobs_covered_by_transport in Hcoverage_check.
    exact Hcoverage_check.
  - exact
      (transport_coverage_complete
         T tasks offset jobs candidate_jobs Hcoverage j Hj).
Qed.

Theorem edf_schedulability_decide_schedulable_by_on_with_checked_transport_coverage
    (ts : list ExtractedPeriodicTask)
    (codec :
      PeriodicCodec
        (extracted_task_scope ts)
        (extracted_periodic_tasks ts)
        (fun _ => 0)
        (extracted_periodic_jobs ts))
    (transport_cert : EDFTransportCert JobId)
    (candidate_jobs : list JobId) :
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
  intros Hwf Htransport_check Htransport_sem Hcoverage Hcoverage_check Hdec.
  eapply periodic_edf_schedulable_by_classical_dbf_with_checked_transport_coverage.
  - apply extracted_tasks_well_formed_on_enum.
    exact Hwf.
  - apply extracted_periodic_nonblocking.
  - apply enumT_of_extracted_list_nodup.
  - apply extracted_enum_complete.
  - apply extracted_enum_sound.
  - apply extracted_zero_offset.
  - exact Htransport_check.
  - exact Htransport_sem.
  - exact Hcoverage.
  - exact Hcoverage_check.
  - apply edf_schedulability_decide_true_global_dbf_ok.
    exact Hdec.
Qed.
