From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Analysis.Uniprocessor.EDFProcessorDemand.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Periodic.PeriodicInfinite.
From RocqSched Require Import TaskModels.Periodic.PeriodicWindowDemandBound.
From RocqSched Require Import TaskModels.Periodic.PeriodicCodec.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFCertificate.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFCertificateSoundness.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFBacklogBridgeChecker.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFInfiniteBridge.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFNoCarryInSupply.

Import ListNotations.

(** Verified transport lookup layer for periodic EDF certificates.

    The transport certificate already carries class and shift tables.  This file
    adds the small executable check that a transported target job is present in
    the transport basis, and connects that boolean fact to the semantic witness
    stored behind [EDFTransportCertSemantics].

    The file intentionally does not decide the transport decomposition of an
    arbitrary periodic job.  Downstream adapters provide a finite list of jobs
    covered by transport, plus the semantic coverage obligation. *)

Definition periodic_shifted_job
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (codec : PeriodicCodec T tasks offset jobs)
    (τ : TaskId)
    (k q shift : nat) : JobId :=
  global_periodic_job_id_of T tasks offset jobs codec τ (k + shift * q).

Definition check_transport_job_witness
    (c : EDFTransportCert JobId)
    (j : JobId) : bool :=
  check_job_in_basis c.(transport_basis_jobs) j.

Definition check_transport_jobs_witness
    (c : EDFTransportCert JobId)
    (jobs : list JobId) : bool :=
  forallb (check_transport_job_witness c) jobs.

Definition transport_class_backlog_holds
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (enumT : list TaskId)
    (codec : PeriodicCodec T tasks offset jobs)
    (j : JobId)
    (_cls : EDFTransportClass JobId)
    (_shift : nat) : Prop :=
  periodic_edf_backlog_free_before_release
    T tasks offset jobs
    (S (job_abs_deadline (jobs j)))
    (generated_periodic_edf_schedule_upto
       T tasks offset jobs (S (job_abs_deadline (jobs j))) enumT codec)
    j.

Definition transport_class_no_carry_in_holds
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (enumT : list TaskId)
    (codec : PeriodicCodec T tasks offset jobs)
    (j : JobId)
    (_cls : EDFTransportClass JobId)
    (_shift : nat) : Prop :=
  periodic_edf_busy_prefix_no_carry_in_bridge
    T tasks offset jobs
    (S (job_abs_deadline (jobs j)))
    (generated_periodic_edf_schedule_upto
       T tasks offset jobs (S (job_abs_deadline (jobs j))) enumT codec)
    j.

Lemma check_transport_job_witness_sound :
  forall transport_witness_holds c j,
    check_transport_cert c = true ->
    EDFTransportCertSemantics transport_witness_holds c ->
    check_transport_job_witness c j = true ->
    exists cls shift,
      transport_witness_holds j cls shift.
Proof.
  intros transport_witness_holds c j Hcheck Hsem Hjob.
  unfold check_transport_job_witness in Hjob.
  destruct (check_job_in_basis_sound c.(transport_basis_jobs) j Hjob)
    as [i Hj].
  pose proof (check_transport_cert_fields JobId c Hcheck)
    as [_ [Hclass_len [Hshift_len _]]].
  assert (Hi : i < length c.(transport_basis_jobs)).
  {
    apply nth_error_Some.
    intro Hnone.
    rewrite Hj in Hnone.
    discriminate.
  }
  assert (Hclass_lt : i < length c.(transport_job_class)) by lia.
  assert (Hshift_lt : i < length c.(transport_job_shift)) by lia.
  destruct (nth_error_exists_of_lt nat c.(transport_job_class) i Hclass_lt)
    as [class_id Hclass].
  destruct (nth_error_exists_of_lt nat c.(transport_job_shift) i Hshift_lt)
    as [shift Hshift].
  pose proof
    (check_transport_cert_semantic_sound
       transport_witness_holds c Hcheck Hsem)
    as [_ Hlookup].
  destruct (Hlookup i j class_id shift Hj Hclass Hshift)
    as [cls [_ Hholds]].
  exists cls, shift.
  exact Hholds.
Qed.

Lemma check_transport_jobs_witness_sound :
  forall transport_witness_holds c transported_jobs j,
    check_transport_cert c = true ->
    EDFTransportCertSemantics transport_witness_holds c ->
    check_transport_jobs_witness c transported_jobs = true ->
    In j transported_jobs ->
    exists cls shift,
      transport_witness_holds j cls shift.
Proof.
  intros transport_witness_holds c transported_jobs j
         Hcheck Hsem Hjobs Hin.
  unfold check_transport_jobs_witness in Hjobs.
  apply forallb_forall with (x := j) in Hjobs; [|exact Hin].
  eapply check_transport_job_witness_sound; eauto.
Qed.

Theorem checked_transport_backlog_free_before_release :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs)
         c target,
    check_transport_cert c = true ->
    EDFTransportCertSemantics
      (transport_class_backlog_holds T tasks offset jobs enumT codec)
      c ->
    check_transport_job_witness c target = true ->
    periodic_edf_backlog_free_before_release
      T tasks offset jobs
      (S (job_abs_deadline (jobs target)))
      (generated_periodic_edf_schedule_upto
         T tasks offset jobs
         (S (job_abs_deadline (jobs target))) enumT codec)
      target.
Proof.
  intros T tasks offset jobs enumT codec c target Hcheck Hsem Htarget.
  destruct
    (check_transport_job_witness_sound
       (transport_class_backlog_holds T tasks offset jobs enumT codec)
       c target Hcheck Hsem Htarget)
    as [cls [shift Hholds]].
  exact Hholds.
Qed.

Theorem checked_transport_no_carry_in_bridge_from_backlog :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs)
         c target,
    well_formed_periodic_tasks_on T tasks ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    check_transport_cert c = true ->
    EDFTransportCertSemantics
      (transport_class_backlog_holds T tasks offset jobs enumT codec)
      c ->
    check_transport_job_witness c target = true ->
    periodic_edf_busy_prefix_no_carry_in_bridge
      T tasks offset jobs
      (S (job_abs_deadline (jobs target)))
      (generated_periodic_edf_schedule_upto
         T tasks offset jobs
         (S (job_abs_deadline (jobs target))) enumT codec)
      target.
Proof.
  intros T tasks offset jobs enumT codec c target
         Hwf Henum_complete Henum_sound Hcheck Hsem Htarget.
  eapply periodic_edf_no_carry_in_bridge_of_backlog_free.
  - apply generated_periodic_edf_schedule_upto_valid; eauto.
  - eapply checked_transport_backlog_free_before_release; eauto.
Qed.

Theorem checked_transport_no_carry_in_bridge :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs)
         c target,
    check_transport_cert c = true ->
    EDFTransportCertSemantics
      (transport_class_no_carry_in_holds T tasks offset jobs enumT codec)
      c ->
    check_transport_job_witness c target = true ->
    periodic_edf_busy_prefix_no_carry_in_bridge
      T tasks offset jobs
      (S (job_abs_deadline (jobs target)))
      (generated_periodic_edf_schedule_upto
         T tasks offset jobs
         (S (job_abs_deadline (jobs target))) enumT codec)
      target.
Proof.
  intros T tasks offset jobs enumT codec c target Hcheck Hsem Htarget.
  destruct
    (check_transport_job_witness_sound
       (transport_class_no_carry_in_holds T tasks offset jobs enumT codec)
       c target Hcheck Hsem Htarget)
    as [cls [shift Hholds]].
  exact Hholds.
Qed.

Theorem checked_transport_backlog_free_for_list :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs)
         c transported_jobs target,
    check_transport_cert c = true ->
    EDFTransportCertSemantics
      (transport_class_backlog_holds T tasks offset jobs enumT codec)
      c ->
    check_transport_jobs_witness c transported_jobs = true ->
    In target transported_jobs ->
    periodic_edf_backlog_free_before_release
      T tasks offset jobs
      (S (job_abs_deadline (jobs target)))
      (generated_periodic_edf_schedule_upto
         T tasks offset jobs
         (S (job_abs_deadline (jobs target))) enumT codec)
      target.
Proof.
  intros T tasks offset jobs enumT codec c transported_jobs target
         Hcheck Hsem Hjobs Hin.
  destruct
    (check_transport_jobs_witness_sound
       (transport_class_backlog_holds T tasks offset jobs enumT codec)
       c transported_jobs target Hcheck Hsem Hjobs Hin)
    as [cls [shift Hholds]].
  exact Hholds.
Qed.

Theorem checked_transport_no_carry_in_for_list_from_backlog :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs)
         c transported_jobs target,
    well_formed_periodic_tasks_on T tasks ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    check_transport_cert c = true ->
    EDFTransportCertSemantics
      (transport_class_backlog_holds T tasks offset jobs enumT codec)
      c ->
    check_transport_jobs_witness c transported_jobs = true ->
    In target transported_jobs ->
    periodic_edf_busy_prefix_no_carry_in_bridge
      T tasks offset jobs
      (S (job_abs_deadline (jobs target)))
      (generated_periodic_edf_schedule_upto
         T tasks offset jobs
         (S (job_abs_deadline (jobs target))) enumT codec)
      target.
Proof.
  intros T tasks offset jobs enumT codec c transported_jobs target
         Hwf Henum_complete Henum_sound Hcheck Hsem Hjobs Hin.
  eapply periodic_edf_no_carry_in_bridge_of_backlog_free.
  - apply generated_periodic_edf_schedule_upto_valid; eauto.
  - eapply checked_transport_backlog_free_for_list; eauto.
Qed.

Theorem checked_transport_no_carry_in_for_all_periodic_jobs_from_backlog :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs)
         c transported_jobs,
    well_formed_periodic_tasks_on T tasks ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    check_transport_cert c = true ->
    EDFTransportCertSemantics
      (transport_class_backlog_holds T tasks offset jobs enumT codec)
      c ->
    check_transport_jobs_witness c transported_jobs = true ->
    (forall j,
       periodic_jobset T tasks offset jobs j ->
       In j transported_jobs) ->
    forall j,
      periodic_jobset T tasks offset jobs j ->
      periodic_edf_busy_prefix_no_carry_in_bridge
        T tasks offset jobs
        (S (job_abs_deadline (jobs j)))
        (generated_periodic_edf_schedule_upto
           T tasks offset jobs
           (S (job_abs_deadline (jobs j))) enumT codec)
        j.
Proof.
  intros T tasks offset jobs enumT codec c transported_jobs
         Hwf Henum_complete Henum_sound Hcheck Hsem Hjobs Hcover j Hj.
  eapply checked_transport_no_carry_in_for_list_from_backlog; eauto.
Qed.
