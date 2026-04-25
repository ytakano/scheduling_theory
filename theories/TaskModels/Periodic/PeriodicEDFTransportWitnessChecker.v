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
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFTransportAlgebra.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFTransportChecker.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFTransportCoverageChecker.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFWindowTransport.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFWindowTransportChecker.
From RocqSched Require Import TaskModels.Periodic.PeriodicConcreteAnalysis.
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

Definition transport_class_rep_relevant_jobs
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (enumT : list TaskId)
    (codec : PeriodicCodec T tasks offset jobs)
    (cls : EDFTransportClass JobId) : list JobId :=
  window_target_relevant_earlier_jobs
    T tasks offset jobs enumT codec cls.(transport_rep_job).

Definition transport_classes_rep_relevant_jobs
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (enumT : list TaskId)
    (codec : PeriodicCodec T tasks offset jobs)
    (classes : list (EDFTransportClass JobId)) : list (list JobId) :=
  map
    (transport_class_rep_relevant_jobs T tasks offset jobs enumT codec)
    classes.

Definition check_transport_class_rep_backlog_generated
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (enumT : list TaskId)
    (codec : PeriodicCodec T tasks offset jobs)
    (prefix_cert : EDFPrefixCert JobId)
    (cls : EDFTransportClass JobId) : bool :=
  check_transport_class_rep_backlog
    prefix_cert cls
    (transport_class_rep_relevant_jobs
       T tasks offset jobs enumT codec cls).

Fixpoint check_transport_classes_rep_backlog_generated
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (enumT : list TaskId)
    (codec : PeriodicCodec T tasks offset jobs)
    (prefix_cert : EDFPrefixCert JobId)
    (classes : list (EDFTransportClass JobId)) : bool :=
  match classes with
  | [] => true
  | cls :: classes' =>
      check_transport_class_rep_backlog_generated
        T tasks offset jobs enumT codec prefix_cert cls
      && check_transport_classes_rep_backlog_generated
           T tasks offset jobs enumT codec prefix_cert classes'
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

Theorem transport_class_algebra_obligation_of_backlog_algebra :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs)
         prefix_cert,
    TransportBacklogAlgebraObligation
      T tasks offset jobs enumT codec prefix_cert ->
    TransportClassAlgebraObligation
      T tasks offset jobs enumT codec prefix_cert.
Proof.
  intros T tasks offset jobs enumT codec prefix_cert Halgebra.
  constructor.
  intros j cls shift Hrep.
  eapply transport_window_algebra_sound.
  - exact
      (transport_backlog_window_algebra
         T tasks offset jobs enumT codec prefix_cert Halgebra j cls shift).
  - exact Hrep.
Qed.

Theorem transport_class_algebra_obligation_of_checked_window_transport :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs)
         prefix_cert transport_cert target_certs,
    check_window_transport_targets jobs transport_cert target_certs = true ->
    WindowTransportTargetsObligation
      T tasks offset jobs enumT codec prefix_cert transport_cert target_certs ->
    TransportClassAlgebraObligation
      T tasks offset jobs enumT codec prefix_cert.
Proof.
  intros T tasks offset jobs enumT codec prefix_cert transport_cert target_certs
         Hcheck Hobligation.
  apply transport_class_algebra_obligation_of_backlog_algebra.
  apply transport_backlog_algebra_of_shifted_generated_window.
  eapply checked_window_transport_targets_obligation_sound; eauto.
Qed.

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

Lemma check_transport_classes_rep_backlog_generated_sound :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs)
         prefix_cert classes i cls,
    check_transport_classes_rep_backlog_generated
      T tasks offset jobs enumT codec prefix_cert classes = true ->
    nth_error classes i = Some cls ->
    check_transport_class_rep_backlog_generated
      T tasks offset jobs enumT codec prefix_cert cls = true.
Proof.
  intros T tasks offset jobs enumT codec prefix_cert classes.
  induction classes as [|cls0 classes IH]; intros i cls Hcheck Hcls.
  - destruct i; discriminate.
  - destruct i as [|i].
    + cbn in Hcheck, Hcls.
      inversion Hcls; subst.
      apply andb_true_iff in Hcheck.
      exact (proj1 Hcheck).
    + cbn in Hcheck, Hcls.
      apply andb_true_iff in Hcheck.
      destruct Hcheck as [_ Htail].
      eapply IH; eauto.
Qed.

Theorem checked_transport_class_rep_completion_generated_sound :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs)
         prefix_cert classes i cls,
    well_formed_periodic_tasks_on T tasks ->
    (forall τ, T τ -> In τ enumT) ->
    valid_schedule jobs 1
      (generated_periodic_edf_prefix T tasks offset jobs enumT codec prefix_cert) ->
    periodic_jobset T tasks offset jobs cls.(transport_rep_job) ->
    check_prefix_cert_semantic jobs prefix_cert = true ->
    check_prefix_slots_match_generated_edf
      T tasks offset jobs enumT codec prefix_cert = true ->
    check_transport_classes_rep_backlog_generated
      T tasks offset jobs enumT codec prefix_cert classes = true ->
    nth_error classes i = Some cls ->
    representative_earlier_completion_before_release
      T tasks offset jobs
      (generated_periodic_edf_prefix T tasks offset jobs enumT codec prefix_cert)
      cls.(transport_rep_job).
Proof.
  intros T tasks offset jobs enumT codec prefix_cert classes i cls
         Hwf HenumT_complete Hvalid Hrep Hcert Hmatch Hcheck Hcls.
  pose proof
    (check_transport_classes_rep_backlog_generated_sound
       T tasks offset jobs enumT codec prefix_cert classes i cls Hcheck Hcls)
    as Hrep_check.
  unfold check_transport_class_rep_backlog_generated,
         check_transport_class_rep_backlog,
         transport_class_rep_relevant_jobs in Hrep_check.
  intros x Hbetween Hrelease.
  eapply check_prefix_backlog_free_before_release_sound.
  - eapply checked_prefix_semantics_on_generated_edf; eauto.
  - exact Hrep_check.
  - eapply window_target_relevant_earlier_jobs_complete; eauto.
Qed.

Theorem transport_class_representative_obligation_of_generated_checks :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs)
         prefix_cert classes,
    well_formed_periodic_tasks_on T tasks ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    valid_schedule jobs 1
      (generated_periodic_edf_prefix T tasks offset jobs enumT codec prefix_cert) ->
    check_prefix_cert_semantic jobs prefix_cert = true ->
    check_prefix_slots_match_generated_edf_fast
      T tasks offset jobs enumT codec prefix_cert = true ->
    check_transport_classes_rep_periodic_generated
      T tasks offset jobs enumT codec classes = true ->
    TransportClassRepresentativeObligation
      T tasks offset jobs enumT codec prefix_cert classes
      (transport_classes_rep_relevant_jobs
         T tasks offset jobs enumT codec classes).
Proof.
  intros T tasks offset jobs enumT codec prefix_cert classes
         Hwf HenumT_complete HenumT_sound Hvalid Hprefix_sem
         Hprefix_fast Hrep_periodic.
  constructor.
  - exact Hvalid.
  - exact Hprefix_sem.
  - eapply check_prefix_slots_match_generated_edf_fast_sound.
    exact Hprefix_fast.
  - intros i cls relevant Hcls Hrelevant.
    unfold transport_classes_rep_relevant_jobs in Hrelevant.
    rewrite nth_error_map in Hrelevant.
    rewrite Hcls in Hrelevant.
    inversion Hrelevant; subst relevant.
    eapply check_transport_classes_rep_periodic_generated_sound; eauto.
  - intros i cls relevant x Hcls Hrelevant Hbetween Hrelease.
    unfold transport_classes_rep_relevant_jobs in Hrelevant.
    rewrite nth_error_map in Hrelevant.
    rewrite Hcls in Hrelevant.
    inversion Hrelevant; subst relevant.
    unfold transport_class_rep_relevant_jobs.
    eapply window_target_relevant_earlier_jobs_complete; eauto.
Qed.

Record WindowGeneratedPairSemanticObligation
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (enumT : list TaskId)
    (codec : PeriodicCodec T tasks offset jobs)
    (prefix_cert : EDFPrefixCert JobId)
    (transport_cert : EDFTransportCert JobId)
    (target_certs : list EDFWindowTransportTargetCert) : Prop := {
  window_generated_transport_basis_nodup :
    NoDup transport_cert.(transport_basis_jobs);
  window_generated_target_cert_complete :
    forall target (cls : EDFTransportClass JobId) (shift : nat),
      exists target_cert i class_id,
        In target_cert target_certs
        /\ target_cert.(window_transport_target_job) = target
        /\ nth_error transport_cert.(transport_basis_jobs) i = Some target
        /\ nth_error transport_cert.(transport_job_class) i = Some class_id
        /\ nth_error transport_cert.(transport_job_shift) i = Some shift
        /\ nth_error transport_cert.(transport_classes) class_id = Some cls
        /\ target_cert.(window_transport_class_id) = class_id
        /\ target_cert.(window_transport_shift) = shift;
  window_generated_rep_periodic :
    forall target_cert i cls,
      In target_cert target_certs ->
      nth_error transport_cert.(transport_basis_jobs) i =
        Some target_cert.(window_transport_target_job) ->
      nth_error transport_cert.(transport_job_class) i =
        Some target_cert.(window_transport_class_id) ->
      nth_error transport_cert.(transport_classes)
        target_cert.(window_transport_class_id) = Some cls ->
      periodic_jobset T tasks offset jobs cls.(transport_rep_job);
  window_generated_pair_rep_earlier_between :
    forall target_cert i cls p,
      In target_cert target_certs ->
      nth_error transport_cert.(transport_basis_jobs) i =
        Some target_cert.(window_transport_target_job) ->
      nth_error transport_cert.(transport_job_class) i =
        Some target_cert.(window_transport_class_id) ->
      nth_error transport_cert.(transport_classes)
        target_cert.(window_transport_class_id) = Some cls ->
      In p target_cert.(window_transport_pairs) ->
      periodic_jobset_deadline_between
        T tasks offset jobs 0 (job_abs_deadline (jobs cls.(transport_rep_job)))
        p.(window_rep_earlier_job);
  window_generated_pair_completion_transport :
    forall target_cert i cls,
      In target_cert target_certs ->
      nth_error transport_cert.(transport_basis_jobs) i =
        Some target_cert.(window_transport_target_job) ->
      nth_error transport_cert.(transport_job_class) i =
        Some target_cert.(window_transport_class_id) ->
      nth_error transport_cert.(transport_classes)
        target_cert.(window_transport_class_id) = Some cls ->
      WindowPairGeneratedCompletionTransportObligation
        T tasks offset jobs enumT codec prefix_cert
        cls.(transport_rep_job)
        target_cert.(window_transport_target_job)
        target_cert
}.

Record WindowGeneratedPairCompletionOnlyObligation
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (enumT : list TaskId)
    (codec : PeriodicCodec T tasks offset jobs)
    (prefix_cert : EDFPrefixCert JobId)
    (transport_cert : EDFTransportCert JobId)
    (target_certs : list EDFWindowTransportTargetCert) : Prop := {
  window_completion_only_transport_basis_nodup :
    NoDup transport_cert.(transport_basis_jobs);
  window_completion_only_target_cert_complete :
    forall target (cls : EDFTransportClass JobId) (shift : nat),
      exists target_cert i class_id,
        In target_cert target_certs
        /\ target_cert.(window_transport_target_job) = target
        /\ nth_error transport_cert.(transport_basis_jobs) i = Some target
        /\ nth_error transport_cert.(transport_job_class) i = Some class_id
        /\ nth_error transport_cert.(transport_job_shift) i = Some shift
        /\ nth_error transport_cert.(transport_classes) class_id = Some cls
        /\ target_cert.(window_transport_class_id) = class_id
        /\ target_cert.(window_transport_shift) = shift;
  window_completion_only_rep_periodic :
    forall target_cert i cls,
      In target_cert target_certs ->
      nth_error transport_cert.(transport_basis_jobs) i =
        Some target_cert.(window_transport_target_job) ->
      nth_error transport_cert.(transport_job_class) i =
        Some target_cert.(window_transport_class_id) ->
      nth_error transport_cert.(transport_classes)
        target_cert.(window_transport_class_id) = Some cls ->
      periodic_jobset T tasks offset jobs cls.(transport_rep_job);
  window_completion_only_pair_transport :
    forall target_cert i cls p,
      In target_cert target_certs ->
      nth_error transport_cert.(transport_basis_jobs) i =
        Some target_cert.(window_transport_target_job) ->
      nth_error transport_cert.(transport_job_class) i =
        Some target_cert.(window_transport_class_id) ->
      nth_error transport_cert.(transport_classes)
        target_cert.(window_transport_class_id) = Some cls ->
      In p target_cert.(window_transport_pairs) ->
      GeneratedShiftedCompletionTransport
        T tasks offset jobs enumT codec prefix_cert
        cls.(transport_rep_job)
        target_cert.(window_transport_target_job)
        p.(window_rep_earlier_job)
        p.(window_target_earlier_job)
}.

Record WindowGeneratedPairCheckedStructuralObligation
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (enumT : list TaskId)
    (codec : PeriodicCodec T tasks offset jobs)
    (transport_cert : EDFTransportCert JobId)
    (target_certs : list EDFWindowTransportTargetCert) : Prop := {
  window_checked_structural_transport_basis_nodup :
    NoDup transport_cert.(transport_basis_jobs);
  window_checked_structural_target_cert_complete_rows :
    forall i target class_id shift cls,
      nth_error transport_cert.(transport_basis_jobs) i = Some target ->
      nth_error transport_cert.(transport_job_class) i = Some class_id ->
      nth_error transport_cert.(transport_job_shift) i = Some shift ->
      nth_error transport_cert.(transport_classes) class_id = Some cls ->
      exists target_cert,
        In target_cert target_certs
        /\ target_cert.(window_transport_target_job) = target
        /\ target_cert.(window_transport_class_id) = class_id
        /\ target_cert.(window_transport_shift) = shift
        /\ check_window_transport_target jobs transport_cert target_cert = true;
  window_checked_structural_rep_periodic :
    forall class_id cls,
      nth_error transport_cert.(transport_classes) class_id = Some cls ->
      periodic_jobset T tasks offset jobs cls.(transport_rep_job)
}.

Theorem window_checked_structural_obligation_of_checks :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs)
         transport_cert target_certs,
    (forall τ, In τ enumT -> T τ) ->
    check_transport_cert transport_cert = true ->
    check_transport_basis_nodup transport_cert = true ->
    check_window_transport_targets_complete_with_pairs
      T tasks offset jobs enumT codec transport_cert target_certs = true ->
    check_transport_classes_rep_periodic_generated
      T tasks offset jobs enumT codec
      transport_cert.(transport_classes) = true ->
    WindowGeneratedPairCheckedStructuralObligation
      T tasks offset jobs enumT codec transport_cert target_certs.
Proof.
  intros T tasks offset jobs enumT codec transport_cert target_certs
         HenumT_sound Htransport_check Hbasis_nodup_check
         Htarget_complete_check Hrep_periodic_check.
  constructor.
  - eapply check_transport_basis_nodup_sound; eauto.
  - intros i target class_id shift cls Hbasis Hclass Hshift Hcls.
    eapply check_window_transport_targets_complete_with_pairs_basis_sound; eauto.
  - intros class_id cls Hcls.
    eapply check_transport_classes_rep_periodic_generated_sound; eauto.
Qed.

Theorem window_checked_structural_rep_periodic_for_target_cert :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs)
         transport_cert target_certs target_cert i cls,
    WindowGeneratedPairCheckedStructuralObligation
      T tasks offset jobs enumT codec transport_cert target_certs ->
    In target_cert target_certs ->
    nth_error transport_cert.(transport_basis_jobs) i =
      Some target_cert.(window_transport_target_job) ->
    nth_error transport_cert.(transport_job_class) i =
      Some target_cert.(window_transport_class_id) ->
    nth_error transport_cert.(transport_classes)
      target_cert.(window_transport_class_id) = Some cls ->
    periodic_jobset T tasks offset jobs cls.(transport_rep_job).
Proof.
  intros T tasks offset jobs enumT codec transport_cert target_certs
         target_cert i cls Hstruct _ _ _ Hcls.
  eapply window_checked_structural_rep_periodic; eauto.
Qed.

Theorem window_completion_only_obligation_of_generated_completion_check :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs)
         prefix_cert transport_cert target_certs,
    well_formed_periodic_tasks_on T tasks ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    NoDup transport_cert.(transport_basis_jobs) ->
    (forall target (cls : EDFTransportClass JobId) (shift : nat),
      exists target_cert i class_id,
        In target_cert target_certs
        /\ target_cert.(window_transport_target_job) = target
        /\ nth_error transport_cert.(transport_basis_jobs) i = Some target
        /\ nth_error transport_cert.(transport_job_class) i = Some class_id
        /\ nth_error transport_cert.(transport_job_shift) i = Some shift
        /\ nth_error transport_cert.(transport_classes) class_id = Some cls
        /\ target_cert.(window_transport_class_id) = class_id
        /\ target_cert.(window_transport_shift) = shift) ->
    (forall target_cert i cls,
      In target_cert target_certs ->
      nth_error transport_cert.(transport_basis_jobs) i =
        Some target_cert.(window_transport_target_job) ->
      nth_error transport_cert.(transport_job_class) i =
        Some target_cert.(window_transport_class_id) ->
      nth_error transport_cert.(transport_classes)
        target_cert.(window_transport_class_id) = Some cls ->
      periodic_jobset T tasks offset jobs cls.(transport_rep_job)) ->
    check_window_generated_pair_semantics_all
      T tasks offset jobs enumT codec transport_cert target_certs = true ->
    check_window_generated_pair_completion_all
      T tasks offset jobs enumT codec target_certs = true ->
    WindowGeneratedPairCompletionOnlyObligation
      T tasks offset jobs enumT codec prefix_cert transport_cert target_certs.
Proof.
  intros T tasks offset jobs enumT codec prefix_cert transport_cert target_certs
         Hwf HenumT_complete HenumT_sound Hnodup Hcomplete Hrep_periodic
         Hpair_semantics Hpair_completion.
  constructor.
  - exact Hnodup.
  - exact Hcomplete.
  - exact Hrep_periodic.
  - intros target_cert i cls p Hin Hbasis Hclass Hcls Hp.
    destruct
      (check_window_generated_pair_semantics_all_sound
         T tasks offset jobs enumT codec transport_cert target_certs
         target_cert cls HenumT_sound Hpair_semantics Hin Hcls)
      as [Htarget_periodic _].
    eapply check_window_generated_pair_completion_all_sound.
    + exact Hwf.
    + exact HenumT_complete.
    + exact HenumT_sound.
    + exact Htarget_periodic.
    + exact Hpair_completion.
    + exact Hin.
    + reflexivity.
    + exact Hp.
Qed.

Theorem window_generated_pair_semantic_obligation_of_completion_only :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs)
         prefix_cert transport_cert target_certs,
    (forall τ, In τ enumT -> T τ) ->
    check_window_generated_pair_semantics_all
      T tasks offset jobs enumT codec transport_cert target_certs = true ->
    WindowGeneratedPairCompletionOnlyObligation
      T tasks offset jobs enumT codec prefix_cert transport_cert target_certs ->
    WindowGeneratedPairSemanticObligation
      T tasks offset jobs enumT codec prefix_cert transport_cert target_certs.
Proof.
  intros T tasks offset jobs enumT codec prefix_cert transport_cert target_certs
         HenumT_sound Hcheck Hobligation.
  constructor.
  - exact
      (window_completion_only_transport_basis_nodup
         T tasks offset jobs enumT codec prefix_cert transport_cert
         target_certs Hobligation).
  - exact
      (window_completion_only_target_cert_complete
         T tasks offset jobs enumT codec prefix_cert transport_cert
         target_certs Hobligation).
  - intros target_cert i cls Hin Hbasis Hclass Hcls.
    eapply window_completion_only_rep_periodic; eauto.
  - intros target_cert i cls p Hin Hbasis Hclass Hcls Hp.
    destruct
      (check_window_generated_pair_semantics_all_sound
         T tasks offset jobs enumT codec transport_cert target_certs
         target_cert cls HenumT_sound Hcheck Hin Hcls)
      as [_ Hrep_between].
    exact (Hrep_between p Hp).
  - intros target_cert i cls Hin Hbasis Hclass Hcls.
    constructor.
    + destruct
        (check_window_generated_pair_semantics_all_sound
           T tasks offset jobs enumT codec transport_cert target_certs
           target_cert cls HenumT_sound Hcheck Hin Hcls)
        as [Htarget_periodic _].
      exact Htarget_periodic.
    + intros p Hp.
      eapply window_completion_only_pair_transport; eauto.
Qed.

Theorem checked_window_transport_targets_obligation_of_generated_checks :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs)
         prefix_cert transport_cert target_certs class_relevant_jobs,
    well_formed_periodic_tasks_on T tasks ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    TransportClassRepresentativeObligation
      T tasks offset jobs enumT codec
      prefix_cert transport_cert.(transport_classes) class_relevant_jobs ->
    check_transport_classes_rep_backlog_generated
      T tasks offset jobs enumT codec prefix_cert
      transport_cert.(transport_classes) = true ->
    check_window_transport_targets_complete_with_pairs
      T tasks offset jobs enumT codec transport_cert target_certs = true ->
    WindowGeneratedPairSemanticObligation
      T tasks offset jobs enumT codec prefix_cert transport_cert target_certs ->
    WindowTransportTargetsObligation
      T tasks offset jobs enumT codec prefix_cert transport_cert target_certs.
Proof.
  intros T tasks offset jobs enumT codec prefix_cert transport_cert target_certs
         class_relevant_jobs Hwf HenumT_complete HenumT_sound Hrep
         Hrep_generated_check Hwindow_check Hsemantic.
  constructor.
  - exact
      (window_generated_transport_basis_nodup
         T tasks offset jobs enumT codec prefix_cert transport_cert
         target_certs Hsemantic).
  - exact
      (window_generated_target_cert_complete
         T tasks offset jobs enumT codec prefix_cert transport_cert
         target_certs Hsemantic).
  - intros target_cert i cls Hin Hbasis Hclass Hcls.
    eapply window_transport_target_obligation_of_generated_completion.
    + exact Hwf.
    + exact HenumT_complete.
    + exact HenumT_sound.
    + intros _.
      eapply checked_transport_class_rep_completion_generated_sound.
      * exact Hwf.
      * exact HenumT_complete.
      * exact
          (transport_rep_prefix_valid
             T tasks offset jobs enumT codec prefix_cert
             transport_cert.(transport_classes) class_relevant_jobs Hrep).
      * eapply window_generated_rep_periodic; eauto.
      * exact
          (transport_rep_prefix_semantic_check
             T tasks offset jobs enumT codec prefix_cert
             transport_cert.(transport_classes) class_relevant_jobs Hrep).
      * exact
          (transport_rep_prefix_matches_generated
             T tasks offset jobs enumT codec prefix_cert
             transport_cert.(transport_classes) class_relevant_jobs Hrep).
      * exact Hrep_generated_check.
      * exact Hcls.
    + intros t1 t2 x _ _ Hbetween Hrelease.
      assert (Hbetween0 :
        periodic_jobset_deadline_between
          T tasks offset jobs 0
          (job_abs_deadline
             (jobs target_cert.(window_transport_target_job))) x).
      {
        destruct Hbetween as [HT [Hgen [_ Hdeadline]]].
        split; [exact HT|].
        split; [exact Hgen|].
        split; [lia|exact Hdeadline].
      }
      pose proof
        (window_target_relevant_earlier_jobs_complete
           T tasks offset jobs enumT codec
           target_cert.(window_transport_target_job) x
           Hwf HenumT_complete Hbetween0 Hrelease)
        as Hrelevant.
      destruct
        (check_window_transport_targets_complete_with_pairs_coverage_sound
           T tasks offset jobs enumT codec transport_cert target_certs
           target_cert cls x Hwindow_check Hin Hcls Hrelevant)
        as [p [Hp_in [Htarget [Hrep_release [_ Hshifted]]]]].
      exists p.
      split; [exact Hp_in|].
      split; [exact Htarget|].
      split.
      * eapply window_generated_pair_rep_earlier_between; eauto.
      * exact Hrep_release.
    + eapply window_generated_pair_completion_transport; eauto.
Qed.

Theorem checked_window_transport_targets_obligation_of_completion_only_checks :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs)
         prefix_cert transport_cert target_certs class_relevant_jobs,
    well_formed_periodic_tasks_on T tasks ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    TransportClassRepresentativeObligation
      T tasks offset jobs enumT codec
      prefix_cert transport_cert.(transport_classes) class_relevant_jobs ->
    check_transport_classes_rep_backlog_generated
      T tasks offset jobs enumT codec prefix_cert
      transport_cert.(transport_classes) = true ->
    check_window_transport_targets_complete_with_pairs
      T tasks offset jobs enumT codec transport_cert target_certs = true ->
    check_window_generated_pair_semantics_all
      T tasks offset jobs enumT codec transport_cert target_certs = true ->
    WindowGeneratedPairCompletionOnlyObligation
      T tasks offset jobs enumT codec prefix_cert transport_cert target_certs ->
    WindowTransportTargetsObligation
      T tasks offset jobs enumT codec prefix_cert transport_cert target_certs.
Proof.
  intros T tasks offset jobs enumT codec prefix_cert transport_cert target_certs
         class_relevant_jobs Hwf HenumT_complete HenumT_sound Hrep
         Hrep_generated_check Hwindow_check Hpair_check Hcompletion_only.
  eapply checked_window_transport_targets_obligation_of_generated_checks; eauto.
  eapply window_generated_pair_semantic_obligation_of_completion_only; eauto.
Qed.

Theorem checked_window_transport_targets_obligation_of_generated_completion_check :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs)
         prefix_cert transport_cert target_certs class_relevant_jobs,
    well_formed_periodic_tasks_on T tasks ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    TransportClassRepresentativeObligation
      T tasks offset jobs enumT codec
      prefix_cert transport_cert.(transport_classes) class_relevant_jobs ->
    check_transport_classes_rep_backlog_generated
      T tasks offset jobs enumT codec prefix_cert
      transport_cert.(transport_classes) = true ->
    check_window_transport_targets_complete_with_pairs
      T tasks offset jobs enumT codec transport_cert target_certs = true ->
    check_window_generated_pair_semantics_all
      T tasks offset jobs enumT codec transport_cert target_certs = true ->
    check_window_generated_pair_completion_all
      T tasks offset jobs enumT codec target_certs = true ->
    NoDup transport_cert.(transport_basis_jobs) ->
    (forall target (cls : EDFTransportClass JobId) (shift : nat),
      exists target_cert i class_id,
        In target_cert target_certs
        /\ target_cert.(window_transport_target_job) = target
        /\ nth_error transport_cert.(transport_basis_jobs) i = Some target
        /\ nth_error transport_cert.(transport_job_class) i = Some class_id
        /\ nth_error transport_cert.(transport_job_shift) i = Some shift
        /\ nth_error transport_cert.(transport_classes) class_id = Some cls
        /\ target_cert.(window_transport_class_id) = class_id
        /\ target_cert.(window_transport_shift) = shift) ->
    (forall target_cert i cls,
      In target_cert target_certs ->
      nth_error transport_cert.(transport_basis_jobs) i =
        Some target_cert.(window_transport_target_job) ->
      nth_error transport_cert.(transport_job_class) i =
        Some target_cert.(window_transport_class_id) ->
      nth_error transport_cert.(transport_classes)
        target_cert.(window_transport_class_id) = Some cls ->
      periodic_jobset T tasks offset jobs cls.(transport_rep_job)) ->
    WindowTransportTargetsObligation
      T tasks offset jobs enumT codec prefix_cert transport_cert target_certs.
Proof.
  intros T tasks offset jobs enumT codec prefix_cert transport_cert target_certs
         class_relevant_jobs Hwf HenumT_complete HenumT_sound Hrep
         Hrep_generated_check Hwindow_check Hpair_semantics Hpair_completion
         Hnodup Htarget_complete Hrep_periodic.
  eapply checked_window_transport_targets_obligation_of_completion_only_checks.
  - exact Hwf.
  - exact HenumT_complete.
  - exact HenumT_sound.
  - exact Hrep.
  - exact Hrep_generated_check.
  - exact Hwindow_check.
  - exact Hpair_semantics.
  - eapply window_completion_only_obligation_of_generated_completion_check; eauto.
Qed.

Theorem checked_window_transport_row_shifted_backlog_of_generated_checks :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs)
         prefix_cert transport_cert target_certs class_relevant_jobs
         i target class_id shift cls target_cert,
    well_formed_periodic_tasks_on T tasks ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    TransportClassRepresentativeObligation
      T tasks offset jobs enumT codec
      prefix_cert transport_cert.(transport_classes) class_relevant_jobs ->
    check_transport_classes_rep_backlog_generated
      T tasks offset jobs enumT codec prefix_cert
      transport_cert.(transport_classes) = true ->
    check_window_transport_targets_complete_with_pairs
      T tasks offset jobs enumT codec transport_cert target_certs = true ->
    check_window_generated_pair_semantics_all
      T tasks offset jobs enumT codec transport_cert target_certs = true ->
    check_window_generated_pair_completion_all
      T tasks offset jobs enumT codec target_certs = true ->
    check_transport_classes_rep_periodic_generated
      T tasks offset jobs enumT codec
      transport_cert.(transport_classes) = true ->
    NoDup transport_cert.(transport_basis_jobs) ->
    nth_error transport_cert.(transport_basis_jobs) i = Some target ->
    nth_error transport_cert.(transport_job_class) i = Some class_id ->
    nth_error transport_cert.(transport_job_shift) i = Some shift ->
    nth_error transport_cert.(transport_classes) class_id = Some cls ->
    In target_cert target_certs ->
    target_cert.(window_transport_target_job) = target ->
    target_cert.(window_transport_class_id) = class_id ->
    target_cert.(window_transport_shift) = shift ->
    check_window_transport_target jobs transport_cert target_cert = true ->
    ShiftedBacklogWindowTransport
      T tasks offset jobs
      (generated_periodic_edf_prefix
         T tasks offset jobs enumT codec prefix_cert)
      (generated_periodic_edf_schedule_upto
         T tasks offset jobs
         (S (job_abs_deadline (jobs target))) enumT codec)
      cls.(transport_rep_job)
      target.
Proof.
  intros T tasks offset jobs enumT codec prefix_cert transport_cert target_certs
         class_relevant_jobs i target class_id shift cls target_cert
         Hwf HenumT_complete HenumT_sound Hrep Hrep_generated_check
         Hwindow_check Hpair_semantics Hpair_completion Hrep_periodic_check Hnodup
         Hbasis Hclass Hshift Hcls Hin Htarget Htarget_class
         Htarget_shift Htarget_check.
  assert (Hbasis_target :
    nth_error transport_cert.(transport_basis_jobs) i =
      Some target_cert.(window_transport_target_job)).
  {
    rewrite Htarget.
    exact Hbasis.
  }
  assert (Hclass_target :
    nth_error transport_cert.(transport_job_class) i =
      Some target_cert.(window_transport_class_id)).
  {
    rewrite Htarget_class.
    exact Hclass.
  }
  assert (Hshift_target :
    nth_error transport_cert.(transport_job_shift) i =
      Some target_cert.(window_transport_shift)).
  {
    rewrite Htarget_shift.
    exact Hshift.
  }
  assert (Hcls_target :
    nth_error transport_cert.(transport_classes)
      target_cert.(window_transport_class_id) = Some cls).
  {
    rewrite Htarget_class.
    exact Hcls.
  }
  assert (Htarget_periodic :
    periodic_jobset
      T tasks offset jobs target_cert.(window_transport_target_job)).
  {
    destruct
      (check_window_generated_pair_semantics_all_sound
         T tasks offset jobs enumT codec transport_cert target_certs
         target_cert cls HenumT_sound Hpair_semantics Hin Hcls_target)
      as [Hperiodic _].
    exact Hperiodic.
  }
  assert (Htarget_obligation :
    WindowTransportTargetObligation
      T tasks offset jobs
      (generated_periodic_edf_prefix
         T tasks offset jobs enumT codec prefix_cert)
      (generated_periodic_edf_schedule_upto
         T tasks offset jobs
         (S (job_abs_deadline
               (jobs target_cert.(window_transport_target_job)))) enumT codec)
      cls.(transport_rep_job)
      target_cert.(window_transport_target_job)
      target_cert).
  {
    eapply window_transport_target_obligation_of_generated_completion.
    - exact Hwf.
    - exact HenumT_complete.
    - exact HenumT_sound.
    - intros _.
      eapply checked_transport_class_rep_completion_generated_sound.
      + exact Hwf.
      + exact HenumT_complete.
      + exact
          (transport_rep_prefix_valid
             T tasks offset jobs enumT codec prefix_cert
             transport_cert.(transport_classes) class_relevant_jobs Hrep).
      + eapply check_transport_classes_rep_periodic_generated_sound; eauto.
      + exact
          (transport_rep_prefix_semantic_check
             T tasks offset jobs enumT codec prefix_cert
             transport_cert.(transport_classes) class_relevant_jobs Hrep).
      + exact
          (transport_rep_prefix_matches_generated
             T tasks offset jobs enumT codec prefix_cert
             transport_cert.(transport_classes) class_relevant_jobs Hrep).
      + exact Hrep_generated_check.
      + exact Hcls.
    - intros t1 t2 x _ _ Hbetween Hrelease.
      assert (Hbetween0 :
        periodic_jobset_deadline_between
          T tasks offset jobs 0
          (job_abs_deadline
             (jobs target_cert.(window_transport_target_job))) x).
      {
        destruct Hbetween as [HT [Hgen [_ Hdeadline]]].
        split; [exact HT|].
        split; [exact Hgen|].
        split; [lia|exact Hdeadline].
      }
      pose proof
        (window_target_relevant_earlier_jobs_complete
           T tasks offset jobs enumT codec
           target_cert.(window_transport_target_job) x
           Hwf HenumT_complete Hbetween0 Hrelease)
        as Hrelevant.
      destruct
        (check_window_transport_targets_complete_with_pairs_coverage_sound
           T tasks offset jobs enumT codec transport_cert target_certs
           target_cert cls x Hwindow_check Hin Hcls_target Hrelevant)
        as [p [Hp_in [Hx [Hrep_release [_ _]]]]].
      exists p.
      split; [exact Hp_in|].
      split; [exact Hx|].
      split.
      + destruct
          (check_window_generated_pair_semantics_all_sound
             T tasks offset jobs enumT codec transport_cert target_certs
             target_cert cls HenumT_sound Hpair_semantics Hin Hcls_target)
          as [_ Hrep_between].
        exact (Hrep_between p Hp_in).
      + exact Hrep_release.
    - constructor.
      + exact Htarget_periodic.
      + intros p Hp.
        eapply check_window_generated_pair_completion_all_sound.
        * exact Hwf.
        * exact HenumT_complete.
        * exact HenumT_sound.
        * exact Htarget_periodic.
        * exact Hpair_completion.
        * exact Hin.
        * reflexivity.
        * exact Hp.
  }
  rewrite <- Htarget.
  eapply checked_window_transport_target_sound.
  - exact Htarget_check.
  - exact Hnodup.
  - exact Hbasis_target.
  - exact Hclass_target.
  - exact Hshift_target.
  - exact Hcls_target.
  - exact Htarget_obligation.
Qed.

(** Schedule-level bridge from a checked residue representative window to an
    arbitrary periodic job in the same residue class.  The boolean checker
    proves the finite residue coverage and the row-level window transport; this
    obligation isolates the remaining semantic fact that generated EDF windows
    can be transported repeatedly across equal-period residue steps. *)
Record PeriodicResidueWindowTransportLiftObligation
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (enumT : list TaskId)
    (codec : PeriodicCodec T tasks offset jobs)
    (transport_cert : EDFTransportCert JobId) : Prop := {
  periodic_residue_window_transport_lift :
    forall residue target q,
      periodic_jobset T tasks offset jobs target ->
      transport_rep_to_target_job
        T tasks offset jobs codec residue target
        transport_cert.(transport_period) q ->
      periodic_edf_backlog_free_before_release
        T tasks offset jobs
        (S (job_abs_deadline (jobs residue)))
        (generated_periodic_edf_schedule_upto
           T tasks offset jobs
           (S (job_abs_deadline (jobs residue))) enumT codec)
        residue ->
      periodic_edf_backlog_free_before_release
        T tasks offset jobs
        (S (job_abs_deadline (jobs target)))
        (generated_periodic_edf_schedule_upto
           T tasks offset jobs
           (S (job_abs_deadline (jobs target))) enumT codec)
        target
}.

Lemma periodic_residue_target_hyperperiod_multiple :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs)
         (transport_cert : EDFTransportCert JobId) residue target q,
    transport_cert.(transport_period) = periodic_hyperperiod tasks enumT ->
    periodic_jobset T tasks offset jobs residue ->
    transport_rep_to_target_job
      T tasks offset jobs codec residue target
      transport_cert.(transport_period) q ->
    (exists n,
      job_release (jobs target) =
      job_release (jobs residue) + periodic_hyperperiod tasks enumT * n)
    /\
    (exists n,
      job_abs_deadline (jobs target) =
      job_abs_deadline (jobs residue) + periodic_hyperperiod tasks enumT * n).
Proof.
  intros T tasks offset jobs enumT codec transport_cert residue target q
         Hperiod_eq Hresidue Htarget.
  rewrite Hperiod_eq in Htarget.
  split.
  - eapply codec_transport_target_release_hyperperiod_multiple.
    + exact (proj1 Hresidue).
    + exact (proj2 Hresidue).
    + exact Htarget.
  - eapply codec_transport_target_deadline_hyperperiod_multiple.
    + exact (proj1 Hresidue).
    + exact (proj2 Hresidue).
    + exact Htarget.
Qed.

(** The remaining schedule-level fact needed after the boolean checker has
    fixed the transport period to the hyperperiod.  The checker and transport
    algebra establish the residue decomposition and the release/deadline
    arithmetic; this obligation isolates only the generated-EDF fact that a
    backlog-free representative window can be shifted along the same
    hyperperiod phase. *)
Record PeriodicHyperperiodBacklogTransportObligation
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (enumT : list TaskId)
    (codec : PeriodicCodec T tasks offset jobs)
    (transport_cert : EDFTransportCert JobId) : Prop := {
  periodic_hyperperiod_backlog_transport :
    forall residue target q,
      transport_cert.(transport_period) = periodic_hyperperiod tasks enumT ->
      periodic_jobset T tasks offset jobs target ->
      transport_rep_to_target_job
        T tasks offset jobs codec residue target
        transport_cert.(transport_period) q ->
      periodic_edf_backlog_free_before_release
        T tasks offset jobs
        (S (job_abs_deadline (jobs residue)))
        (generated_periodic_edf_schedule_upto
           T tasks offset jobs
           (S (job_abs_deadline (jobs residue))) enumT codec)
        residue ->
      periodic_edf_backlog_free_before_release
        T tasks offset jobs
        (S (job_abs_deadline (jobs target)))
        (generated_periodic_edf_schedule_upto
           T tasks offset jobs
           (S (job_abs_deadline (jobs target))) enumT codec)
        target
}.

(** Narrower schedule-level interface.  The caller supplies the checked
    hyperperiod reset facts already transported to the target finite horizon;
    this obligation only states that the same hyperperiod phase preserves the
    backlog-free window beyond that reset boundary. *)
Record PeriodicHyperperiodWindowShiftObligation
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (enumT : list TaskId)
    (codec : PeriodicCodec T tasks offset jobs)
    (transport_cert : EDFTransportCert JobId) : Prop := {
  periodic_hyperperiod_window_shift :
    forall residue target q,
      transport_cert.(transport_period) = periodic_hyperperiod tasks enumT ->
      periodic_jobset T tasks offset jobs target ->
      transport_rep_to_target_job
        T tasks offset jobs codec residue target
        transport_cert.(transport_period) q ->
      (periodic_hyperperiod tasks enumT <
         S (job_abs_deadline (jobs target)) ->
       forall x,
         periodic_jobset T tasks offset jobs x ->
         job_release (jobs x) < periodic_hyperperiod tasks enumT ->
         completed jobs 1
           (generated_periodic_edf_schedule_upto
              T tasks offset jobs
              (S (job_abs_deadline (jobs target))) enumT codec)
           x
           (periodic_hyperperiod tasks enumT)) ->
      periodic_edf_backlog_free_before_release
        T tasks offset jobs
        (S (job_abs_deadline (jobs residue)))
        (generated_periodic_edf_schedule_upto
           T tasks offset jobs
           (S (job_abs_deadline (jobs residue))) enumT codec)
        residue ->
      periodic_edf_backlog_free_before_release
        T tasks offset jobs
        (S (job_abs_deadline (jobs target)))
        (generated_periodic_edf_schedule_upto
           T tasks offset jobs
           (S (job_abs_deadline (jobs target))) enumT codec)
        target
}.

Record PeriodicHyperperiodEarlierCompletionShiftObligation
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (enumT : list TaskId)
    (codec : PeriodicCodec T tasks offset jobs)
    (transport_cert : EDFTransportCert JobId) : Prop := {
  periodic_hyperperiod_earlier_completion_shift :
    forall residue target q,
      transport_cert.(transport_period) = periodic_hyperperiod tasks enumT ->
      periodic_jobset T tasks offset jobs target ->
      transport_rep_to_target_job
        T tasks offset jobs codec residue target
        transport_cert.(transport_period) q ->
      (periodic_hyperperiod tasks enumT <
         S (job_abs_deadline (jobs target)) ->
       forall x,
         periodic_jobset T tasks offset jobs x ->
         job_release (jobs x) < periodic_hyperperiod tasks enumT ->
         completed jobs 1
           (generated_periodic_edf_schedule_upto
              T tasks offset jobs
              (S (job_abs_deadline (jobs target))) enumT codec)
           x
           (periodic_hyperperiod tasks enumT)) ->
      periodic_edf_backlog_free_before_release
        T tasks offset jobs
        (S (job_abs_deadline (jobs residue)))
        (generated_periodic_edf_schedule_upto
           T tasks offset jobs
           (S (job_abs_deadline (jobs residue))) enumT codec)
        residue ->
      forall x,
        periodic_jobset_deadline_between
          T tasks offset jobs 0 (job_abs_deadline (jobs target)) x ->
        job_release (jobs x) < job_release (jobs target) ->
        completed jobs 1
          (generated_periodic_edf_schedule_upto
             T tasks offset jobs
             (S (job_abs_deadline (jobs target))) enumT codec)
          x
          (job_release (jobs target))
}.

Lemma periodic_hyperperiod_window_shift_of_earlier_completion_shift :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs)
         transport_cert,
    well_formed_periodic_tasks_on T tasks ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    PeriodicHyperperiodEarlierCompletionShiftObligation
      T tasks offset jobs enumT codec transport_cert ->
    PeriodicHyperperiodWindowShiftObligation
      T tasks offset jobs enumT codec transport_cert.
Proof.
  intros T tasks offset jobs enumT codec transport_cert
         Hwf HenumT_complete HenumT_sound Hearlier.
  constructor.
  intros residue target q Hperiod_eq Htarget Htransport Hreset Hresidue_backlog.
  eapply periodic_edf_backlog_free_before_release_of_earlier_completion.
  - eapply generated_periodic_edf_schedule_upto_valid; eauto.
  - exact Htarget.
  - intros x Hbetween Hrelease.
    eapply periodic_hyperperiod_earlier_completion_shift.
    + exact Hearlier.
    + exact Hperiod_eq.
    + exact Htarget.
    + exact Htransport.
    + exact Hreset.
    + exact Hresidue_backlog.
    + exact Hbetween.
    + exact Hrelease.
Qed.

Lemma periodic_residue_window_transport_lift_of_hyperperiod_backlog_transport :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs)
         transport_cert,
    transport_cert.(transport_period) = periodic_hyperperiod tasks enumT ->
    PeriodicHyperperiodBacklogTransportObligation
      T tasks offset jobs enumT codec transport_cert ->
    PeriodicResidueWindowTransportLiftObligation
      T tasks offset jobs enumT codec transport_cert.
Proof.
  intros T tasks offset jobs enumT codec transport_cert
         Hperiod_eq Hhyper_transport.
  constructor.
  intros residue target q Htarget Htransport Hresidue_backlog.
  eapply periodic_hyperperiod_backlog_transport.
  - exact Hhyper_transport.
  - exact Hperiod_eq.
  - exact Htarget.
  - exact Htransport.
  - exact Hresidue_backlog.
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

Theorem periodic_edf_no_carry_in_bridge_of_periodic_residue_transport :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs)
         prefix_cert transport_cert target_certs class_relevant_jobs j,
    well_formed_periodic_tasks_on T tasks ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    0 < transport_cert.(transport_period) ->
    check_transport_cert transport_cert = true ->
    check_transport_basis_nodup transport_cert = true ->
    TransportClassRepresentativeObligation
      T tasks offset jobs enumT codec
      prefix_cert transport_cert.(transport_classes) class_relevant_jobs ->
    check_transport_classes_rep_backlog
      prefix_cert transport_cert.(transport_classes) class_relevant_jobs = true ->
    check_transport_classes_rep_backlog_generated
      T tasks offset jobs enumT codec prefix_cert
      transport_cert.(transport_classes) = true ->
    check_transport_classes_rep_periodic_generated
      T tasks offset jobs enumT codec
      transport_cert.(transport_classes) = true ->
    PeriodicTransportCoverageObligation
      T tasks offset jobs codec transport_cert ->
    check_transport_residue_shifts transport_cert = true ->
    check_window_transport_targets_complete_with_pairs
      T tasks offset jobs enumT codec transport_cert target_certs = true ->
    check_window_generated_pair_semantics_all
      T tasks offset jobs enumT codec transport_cert target_certs = true ->
    check_window_generated_pair_completion_all
      T tasks offset jobs enumT codec target_certs = true ->
    PeriodicResidueWindowTransportLiftObligation
      T tasks offset jobs enumT codec transport_cert ->
    periodic_jobset T tasks offset jobs j ->
    periodic_edf_busy_prefix_no_carry_in_bridge
      T tasks offset jobs
      (S (job_abs_deadline (jobs j)))
      (generated_periodic_edf_schedule_upto
         T tasks offset jobs
         (S (job_abs_deadline (jobs j))) enumT codec)
      j.
Proof.
  intros T tasks offset jobs enumT codec prefix_cert transport_cert
         target_certs class_relevant_jobs j
         Hwf HenumT_complete HenumT_sound Hperiod Htransport_check
         Hbasis_nodup_check Hrep Hrep_check Hrep_generated_check
         Hrep_periodic_check Hcoverage Hshift_check Hwindow_check
         Hpair_semantics Hpair_completion Hresidue_lift Hj.
  destruct
    (periodic_transport_coverage_complete
       T tasks offset jobs codec transport_cert Hcoverage j Hj)
    as [i [class_id [cls [shift
        [Hbasis [Hclass [Hcls Hshift]]]]]]].
  pose proof
    (check_transport_residue_shifts_sound
       transport_cert i shift Hshift_check Hshift) as Hshift_period.
  subst shift.
  set (residue :=
    global_periodic_job_id_of
      T tasks offset jobs codec
      (job_task (jobs j))
      (job_index (jobs j) mod transport_cert.(transport_period))).
  destruct
    (check_window_transport_targets_complete_with_pairs_basis_sound
       T tasks offset jobs enumT codec transport_cert target_certs
       i residue class_id transport_cert.(transport_period) cls
       Hwindow_check Hbasis Hclass Hshift Hcls)
    as [target_cert
        [Hin [Htarget [Htarget_class [Htarget_shift Htarget_check]]]]].
  eapply periodic_edf_no_carry_in_bridge_of_backlog_free.
  - apply generated_periodic_edf_schedule_upto_valid; eauto.
  - pose proof
      (checked_transport_class_rep_backlog_sound
         T tasks offset jobs enumT codec prefix_cert
         transport_cert.(transport_classes) class_relevant_jobs
         class_id cls Hrep Hrep_check Hcls) as Hclass_rep_backlog.
    pose proof
      (checked_window_transport_row_shifted_backlog_of_generated_checks
         T tasks offset jobs enumT codec prefix_cert transport_cert target_certs
         class_relevant_jobs i residue class_id
         transport_cert.(transport_period) cls target_cert
         Hwf HenumT_complete HenumT_sound Hrep Hrep_generated_check
         Hwindow_check Hpair_semantics Hpair_completion Hrep_periodic_check
         (check_transport_basis_nodup_sound transport_cert Hbasis_nodup_check)
         Hbasis Hclass Hshift Hcls Hin Htarget Htarget_class Htarget_shift
         Htarget_check) as Hshifted_residue.
    pose proof
      (shifted_backlog_window_transport_sound
         T tasks offset jobs
         (generated_periodic_edf_prefix
            T tasks offset jobs enumT codec prefix_cert)
         (generated_periodic_edf_schedule_upto
            T tasks offset jobs
            (S (job_abs_deadline (jobs residue))) enumT codec)
         cls.(transport_rep_job)
         residue
         Hshifted_residue Hclass_rep_backlog) as Hresidue_backlog.
    eapply periodic_residue_window_transport_lift.
    + exact Hresidue_lift.
    + exact Hj.
    + subst residue.
      eapply periodic_residue_rep_to_job_transport; eauto.
    + exact Hresidue_backlog.
Qed.

Theorem periodic_edf_no_carry_in_bridge_of_periodic_hyperperiod_transport :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs)
         prefix_cert transport_cert target_certs class_relevant_jobs j,
    well_formed_periodic_tasks_on T tasks ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    transport_cert.(transport_period) = periodic_hyperperiod tasks enumT ->
    0 < transport_cert.(transport_period) ->
    check_transport_cert transport_cert = true ->
    check_transport_basis_nodup transport_cert = true ->
    TransportClassRepresentativeObligation
      T tasks offset jobs enumT codec
      prefix_cert transport_cert.(transport_classes) class_relevant_jobs ->
    check_transport_classes_rep_backlog
      prefix_cert transport_cert.(transport_classes) class_relevant_jobs = true ->
    check_transport_classes_rep_backlog_generated
      T tasks offset jobs enumT codec prefix_cert
      transport_cert.(transport_classes) = true ->
    check_transport_classes_rep_periodic_generated
      T tasks offset jobs enumT codec
      transport_cert.(transport_classes) = true ->
    PeriodicTransportCoverageObligation
      T tasks offset jobs codec transport_cert ->
    check_transport_residue_shifts transport_cert = true ->
    check_window_transport_targets_complete_with_pairs
      T tasks offset jobs enumT codec transport_cert target_certs = true ->
    check_window_generated_pair_semantics_all
      T tasks offset jobs enumT codec transport_cert target_certs = true ->
    check_window_generated_pair_completion_all
      T tasks offset jobs enumT codec target_certs = true ->
    PeriodicHyperperiodBacklogTransportObligation
      T tasks offset jobs enumT codec transport_cert ->
    periodic_jobset T tasks offset jobs j ->
    periodic_edf_busy_prefix_no_carry_in_bridge
      T tasks offset jobs
      (S (job_abs_deadline (jobs j)))
      (generated_periodic_edf_schedule_upto
         T tasks offset jobs
         (S (job_abs_deadline (jobs j))) enumT codec)
      j.
Proof.
  intros T tasks offset jobs enumT codec prefix_cert transport_cert
         target_certs class_relevant_jobs j
         Hwf HenumT_complete HenumT_sound Hperiod_eq Hperiod
         Htransport_check Hbasis_nodup_check Hrep Hrep_check
         Hrep_generated_check Hrep_periodic_check Hcoverage Hshift_check
         Hwindow_check Hpair_semantics Hpair_completion Hhyper_transport Hj.
  eapply periodic_edf_no_carry_in_bridge_of_periodic_residue_transport; eauto.
  eapply periodic_residue_window_transport_lift_of_hyperperiod_backlog_transport;
    eauto.
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

Theorem periodic_edf_schedulable_by_classical_dbf_with_checked_window_transport_witnesses :
  forall T tasks offset enumT jobs
         (codec : PeriodicCodec T tasks offset jobs)
         prefix_cert transport_cert candidate_jobs
         class_relevant_jobs target_certs,
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
    check_transport_classes_rep_backlog
      prefix_cert transport_cert.(transport_classes) class_relevant_jobs = true ->
    TransportCoverageObligation T tasks offset jobs candidate_jobs ->
    check_periodic_jobs_covered_by_transport
      transport_cert candidate_jobs = true ->
    check_window_transport_targets jobs transport_cert target_certs = true ->
    WindowTransportTargetsObligation
      T tasks offset jobs enumT codec prefix_cert transport_cert target_certs ->
    (forall t, taskset_periodic_dbf tasks enumT t <= t) ->
    schedulable_by_on
      (periodic_jobset T tasks offset jobs)
      (edf_scheduler (periodic_candidates_before T tasks offset jobs enumT codec))
      jobs 1.
Proof.
  intros T tasks offset enumT jobs codec prefix_cert transport_cert
         candidate_jobs class_relevant_jobs target_certs
         Hwf Hnonblocked HnodupT HenumT_complete HenumT_sound Hoff
         Htransport_check Hrep Hrep_check Hcoverage Hcoverage_check
         Hwindow_check Hwindow_obligation Hdbf.
  eapply periodic_edf_schedulable_by_classical_dbf_with_checked_transport_witnesses.
  - exact Hwf.
  - exact Hnonblocked.
  - exact HnodupT.
  - exact HenumT_complete.
  - exact HenumT_sound.
  - exact Hoff.
  - exact Htransport_check.
  - exact Hrep.
  - eapply transport_class_algebra_obligation_of_checked_window_transport;
      eauto.
  - exact Hrep_check.
  - exact Hcoverage.
  - exact Hcoverage_check.
  - exact Hdbf.
Qed.

Theorem edf_schedulability_decide_schedulable_by_on_with_checked_window_transport_witnesses
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
    (class_relevant_jobs : list (list JobId))
    (target_certs : list EDFWindowTransportTargetCert) :
  extracted_taskset_wf ts = true ->
  check_transport_cert transport_cert = true ->
  TransportClassRepresentativeObligation
    (extracted_task_scope ts)
    (extracted_periodic_tasks ts)
    (fun _ => 0)
    (extracted_periodic_jobs ts)
    (enumT_of_extracted_list ts)
    codec prefix_cert transport_cert.(transport_classes) class_relevant_jobs ->
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
  check_window_transport_targets
    (extracted_periodic_jobs ts) transport_cert target_certs = true ->
  WindowTransportTargetsObligation
    (extracted_task_scope ts)
    (extracted_periodic_tasks ts)
    (fun _ => 0)
    (extracted_periodic_jobs ts)
    (enumT_of_extracted_list ts)
    codec prefix_cert transport_cert target_certs ->
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
  intros Hwf Htransport_check Hrep Hrep_check
         Hcoverage Hcoverage_check Hwindow_check Hwindow_obligation Hdec.
  eapply periodic_edf_schedulable_by_classical_dbf_with_checked_window_transport_witnesses.
  - apply extracted_tasks_well_formed_on_enum.
    exact Hwf.
  - apply extracted_periodic_nonblocking.
  - apply enumT_of_extracted_list_nodup.
  - apply extracted_enum_complete.
  - apply extracted_enum_sound.
  - apply extracted_zero_offset.
  - exact Htransport_check.
  - exact Hrep.
  - exact Hrep_check.
  - exact Hcoverage.
  - exact Hcoverage_check.
  - exact Hwindow_check.
  - exact Hwindow_obligation.
  - apply edf_schedulability_decide_true_global_dbf_ok.
    exact Hdec.
Qed.

Theorem periodic_edf_schedulable_by_classical_dbf_with_checked_window_transport_generated_checks :
  forall T tasks offset enumT jobs
         (codec : PeriodicCodec T tasks offset jobs)
         prefix_cert transport_cert candidate_jobs
         class_relevant_jobs target_certs,
    well_formed_periodic_tasks_on T tasks ->
    (forall j t,
      periodic_jobset T tasks offset jobs j ->
      ~ blocked jobs j t) ->
    NoDup enumT ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    (forall τ, In τ enumT -> offset τ = 0) ->
    check_transport_cert transport_cert = true ->
    check_transport_basis_nodup transport_cert = true ->
    TransportClassRepresentativeObligation
      T tasks offset jobs enumT codec
      prefix_cert transport_cert.(transport_classes) class_relevant_jobs ->
    check_transport_classes_rep_backlog
      prefix_cert transport_cert.(transport_classes) class_relevant_jobs = true ->
    check_transport_classes_rep_backlog_generated
      T tasks offset jobs enumT codec prefix_cert
      transport_cert.(transport_classes) = true ->
    check_transport_classes_rep_periodic_generated
      T tasks offset jobs enumT codec
      transport_cert.(transport_classes) = true ->
    TransportCoverageObligation T tasks offset jobs candidate_jobs ->
    check_periodic_jobs_covered_by_transport
      transport_cert candidate_jobs = true ->
    check_window_transport_targets_complete_with_pairs
      T tasks offset jobs enumT codec transport_cert target_certs = true ->
    check_window_generated_pair_semantics_all
      T tasks offset jobs enumT codec transport_cert target_certs = true ->
    check_window_generated_pair_completion_all
      T tasks offset jobs enumT codec target_certs = true ->
    (forall t, taskset_periodic_dbf tasks enumT t <= t) ->
    schedulable_by_on
      (periodic_jobset T tasks offset jobs)
      (edf_scheduler (periodic_candidates_before T tasks offset jobs enumT codec))
      jobs 1.
Proof.
  intros T tasks offset enumT jobs codec prefix_cert transport_cert
         candidate_jobs class_relevant_jobs target_certs
         Hwf Hnonblocked HnodupT HenumT_complete HenumT_sound Hoff
         Htransport_check Hbasis_nodup_check Hrep Hrep_check
         Hrep_generated_check Hrep_periodic_check Hcoverage Hcoverage_check
         Hwindow_check Hpair_semantics Hpair_completion Hdbf.
  eapply periodic_edf_schedulable_by_classical_dbf_with_no_carry_in_bridge;
    eauto.
  intros j Hj.
  destruct
    (checked_transport_coverage_sound
       T tasks offset jobs transport_cert candidate_jobs
       Hcoverage Hcoverage_check j Hj)
    as [_ [i Hbasis]].
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
  destruct
    (check_window_transport_targets_complete_with_pairs_basis_sound
       T tasks offset jobs enumT codec transport_cert target_certs
       i j class_id shift cls Hwindow_check Hbasis Hclass Hshift Hcls)
    as [target_cert
        [Hin [Htarget [Htarget_class [Htarget_shift Htarget_check]]]]].
  eapply periodic_edf_no_carry_in_bridge_of_backlog_free.
  - apply generated_periodic_edf_schedule_upto_valid; eauto.
  - pose proof
      (checked_transport_class_rep_backlog_sound
         T tasks offset jobs enumT codec prefix_cert
         transport_cert.(transport_classes) class_relevant_jobs
         class_id cls Hrep Hrep_check Hcls) as Hrep_backlog.
    pose proof
      (checked_window_transport_row_shifted_backlog_of_generated_checks
         T tasks offset jobs enumT codec prefix_cert transport_cert target_certs
         class_relevant_jobs i j class_id shift cls target_cert
         Hwf HenumT_complete HenumT_sound Hrep Hrep_generated_check
         Hwindow_check Hpair_semantics Hpair_completion Hrep_periodic_check
         (check_transport_basis_nodup_sound transport_cert Hbasis_nodup_check)
         Hbasis Hclass Hshift Hcls Hin Htarget Htarget_class Htarget_shift
         Htarget_check) as Hshifted.
    exact
      (shifted_backlog_window_transport_sound
         T tasks offset jobs
         (generated_periodic_edf_prefix
            T tasks offset jobs enumT codec prefix_cert)
         (generated_periodic_edf_schedule_upto
            T tasks offset jobs (S (job_abs_deadline (jobs j))) enumT codec)
         cls.(transport_rep_job)
         j
         Hshifted
         Hrep_backlog).
Qed.

Theorem periodic_edf_schedulable_by_classical_dbf_with_periodic_transport_coverage :
  forall T tasks offset enumT jobs
         (codec : PeriodicCodec T tasks offset jobs)
         prefix_cert transport_cert class_relevant_jobs target_certs,
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
    check_transport_classes_rep_backlog
      prefix_cert transport_cert.(transport_classes) class_relevant_jobs = true ->
    PeriodicTransportCoverageObligation
      T tasks offset jobs codec transport_cert ->
    check_window_transport_targets jobs transport_cert target_certs = true ->
    WindowTransportTargetsObligation
      T tasks offset jobs enumT codec prefix_cert transport_cert target_certs ->
    (forall t, taskset_periodic_dbf tasks enumT t <= t) ->
    schedulable_by_on
      (periodic_jobset T tasks offset jobs)
      (edf_scheduler (periodic_candidates_before T tasks offset jobs enumT codec))
      jobs 1.
Proof.
  intros T tasks offset enumT jobs codec prefix_cert transport_cert
         class_relevant_jobs target_certs
         Hwf Hnonblocked HnodupT HenumT_complete HenumT_sound Hoff
         Htransport_check Hrep Hrep_check Hcoverage
         Hwindow_check Hwindow_obligation Hdbf.
  eapply periodic_edf_schedulable_by_classical_dbf_with_no_carry_in_bridge;
    eauto.
  intros j Hj.
  destruct
    (periodic_transport_coverage_complete
       T tasks offset jobs codec transport_cert Hcoverage j Hj)
    as [i [class_id [cls [shift
        [Hbasis [Hclass [Hcls Hshift]]]]]]].
  eapply periodic_edf_no_carry_in_bridge_of_backlog_free.
  - apply generated_periodic_edf_schedule_upto_valid; eauto.
  - pose proof
      (checked_transport_class_rep_backlog_sound
         T tasks offset jobs enumT codec prefix_cert
         transport_cert.(transport_classes) class_relevant_jobs
         class_id cls Hrep Hrep_check Hcls) as Hrep_backlog.
    pose proof
      (transport_class_algebra_obligation_of_checked_window_transport
         T tasks offset jobs enumT codec prefix_cert transport_cert
         target_certs Hwindow_check Hwindow_obligation)
      as Halgebra.
    exact
      (transport_class_algebra_sound
         T tasks offset jobs enumT codec prefix_cert
         Halgebra j cls shift Hrep_backlog).
Qed.

Theorem periodic_edf_schedulable_by_classical_dbf_with_periodic_transport_generated_checks :
  forall T tasks offset enumT jobs
         (codec : PeriodicCodec T tasks offset jobs)
         prefix_cert transport_cert class_relevant_jobs target_certs,
    well_formed_periodic_tasks_on T tasks ->
    (forall j t,
      periodic_jobset T tasks offset jobs j ->
      ~ blocked jobs j t) ->
    NoDup enumT ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    (forall τ, In τ enumT -> offset τ = 0) ->
    0 < transport_cert.(transport_period) ->
    check_transport_cert transport_cert = true ->
    check_transport_basis_nodup transport_cert = true ->
    TransportClassRepresentativeObligation
      T tasks offset jobs enumT codec
      prefix_cert transport_cert.(transport_classes) class_relevant_jobs ->
    check_transport_classes_rep_backlog
      prefix_cert transport_cert.(transport_classes) class_relevant_jobs = true ->
    check_transport_classes_rep_backlog_generated
      T tasks offset jobs enumT codec prefix_cert
      transport_cert.(transport_classes) = true ->
    check_transport_classes_rep_periodic_generated
      T tasks offset jobs enumT codec
      transport_cert.(transport_classes) = true ->
    PeriodicTransportCoverageObligation
      T tasks offset jobs codec transport_cert ->
    check_transport_residue_shifts transport_cert = true ->
    check_window_transport_targets_complete_with_pairs
      T tasks offset jobs enumT codec transport_cert target_certs = true ->
    check_window_generated_pair_semantics_all
      T tasks offset jobs enumT codec transport_cert target_certs = true ->
    check_window_generated_pair_completion_all
      T tasks offset jobs enumT codec target_certs = true ->
    PeriodicResidueWindowTransportLiftObligation
      T tasks offset jobs enumT codec transport_cert ->
    (forall t, taskset_periodic_dbf tasks enumT t <= t) ->
    schedulable_by_on
      (periodic_jobset T tasks offset jobs)
      (edf_scheduler (periodic_candidates_before T tasks offset jobs enumT codec))
      jobs 1.
Proof.
  intros T tasks offset enumT jobs codec prefix_cert transport_cert
         class_relevant_jobs target_certs
         Hwf Hnonblocked HnodupT HenumT_complete HenumT_sound Hoff
         Hperiod Htransport_check Hbasis_nodup_check Hrep Hrep_check
         Hrep_generated_check Hrep_periodic_check Hcoverage Hshift_check
         Hwindow_check Hpair_semantics Hpair_completion Hresidue_lift Hdbf.
  eapply periodic_edf_schedulable_by_classical_dbf_with_no_carry_in_bridge;
    eauto.
  intros j Hj.
  eapply periodic_edf_no_carry_in_bridge_of_periodic_residue_transport; eauto.
Qed.

Theorem periodic_edf_schedulable_by_classical_dbf_with_periodic_hyperperiod_transport_generated_checks :
  forall T tasks offset enumT jobs
         (codec : PeriodicCodec T tasks offset jobs)
         prefix_cert transport_cert class_relevant_jobs target_certs,
    well_formed_periodic_tasks_on T tasks ->
    (forall j t,
      periodic_jobset T tasks offset jobs j ->
      ~ blocked jobs j t) ->
    NoDup enumT ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    (forall τ, In τ enumT -> offset τ = 0) ->
    transport_cert.(transport_period) = periodic_hyperperiod tasks enumT ->
    0 < transport_cert.(transport_period) ->
    check_transport_cert transport_cert = true ->
    check_transport_basis_nodup transport_cert = true ->
    TransportClassRepresentativeObligation
      T tasks offset jobs enumT codec
      prefix_cert transport_cert.(transport_classes) class_relevant_jobs ->
    check_transport_classes_rep_backlog
      prefix_cert transport_cert.(transport_classes) class_relevant_jobs = true ->
    check_transport_classes_rep_backlog_generated
      T tasks offset jobs enumT codec prefix_cert
      transport_cert.(transport_classes) = true ->
    check_transport_classes_rep_periodic_generated
      T tasks offset jobs enumT codec
      transport_cert.(transport_classes) = true ->
    PeriodicTransportCoverageObligation
      T tasks offset jobs codec transport_cert ->
    check_transport_residue_shifts transport_cert = true ->
    check_window_transport_targets_complete_with_pairs
      T tasks offset jobs enumT codec transport_cert target_certs = true ->
    check_window_generated_pair_semantics_all
      T tasks offset jobs enumT codec transport_cert target_certs = true ->
    check_window_generated_pair_completion_all
      T tasks offset jobs enumT codec target_certs = true ->
    PeriodicHyperperiodBacklogTransportObligation
      T tasks offset jobs enumT codec transport_cert ->
    (forall t, taskset_periodic_dbf tasks enumT t <= t) ->
    schedulable_by_on
      (periodic_jobset T tasks offset jobs)
      (edf_scheduler (periodic_candidates_before T tasks offset jobs enumT codec))
      jobs 1.
Proof.
  intros T tasks offset enumT jobs codec prefix_cert transport_cert
         class_relevant_jobs target_certs
         Hwf Hnonblocked HnodupT HenumT_complete HenumT_sound Hoff
         Hperiod_eq Hperiod Htransport_check Hbasis_nodup_check Hrep Hrep_check
         Hrep_generated_check Hrep_periodic_check Hcoverage Hshift_check
         Hwindow_check Hpair_semantics Hpair_completion Hhyper_transport Hdbf.
  eapply periodic_edf_schedulable_by_classical_dbf_with_no_carry_in_bridge;
    eauto.
  intros j Hj.
  eapply periodic_edf_no_carry_in_bridge_of_periodic_hyperperiod_transport; eauto.
Qed.

Theorem edf_schedulability_decide_schedulable_by_on_with_periodic_transport_coverage
    (ts : list ExtractedPeriodicTask)
    (codec :
      PeriodicCodec
        (extracted_task_scope ts)
        (extracted_periodic_tasks ts)
        (fun _ => 0)
        (extracted_periodic_jobs ts))
    (prefix_cert : EDFPrefixCert JobId)
    (transport_cert : EDFTransportCert JobId)
    (class_relevant_jobs : list (list JobId))
    (target_certs : list EDFWindowTransportTargetCert) :
  extracted_taskset_wf ts = true ->
  check_transport_cert transport_cert = true ->
  TransportClassRepresentativeObligation
    (extracted_task_scope ts)
    (extracted_periodic_tasks ts)
    (fun _ => 0)
    (extracted_periodic_jobs ts)
    (enumT_of_extracted_list ts)
    codec prefix_cert transport_cert.(transport_classes) class_relevant_jobs ->
  check_transport_classes_rep_backlog
    prefix_cert transport_cert.(transport_classes) class_relevant_jobs = true ->
  PeriodicTransportCoverageObligation
    (extracted_task_scope ts)
    (extracted_periodic_tasks ts)
    (fun _ => 0)
    (extracted_periodic_jobs ts)
    codec transport_cert ->
  check_window_transport_targets
    (extracted_periodic_jobs ts) transport_cert target_certs = true ->
  WindowTransportTargetsObligation
    (extracted_task_scope ts)
    (extracted_periodic_tasks ts)
    (fun _ => 0)
    (extracted_periodic_jobs ts)
    (enumT_of_extracted_list ts)
    codec prefix_cert transport_cert target_certs ->
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
  intros Hwf Htransport_check Hrep Hrep_check
         Hcoverage Hwindow_check Hwindow_obligation Hdec.
  eapply periodic_edf_schedulable_by_classical_dbf_with_periodic_transport_coverage.
  - apply extracted_tasks_well_formed_on_enum.
    exact Hwf.
  - apply extracted_periodic_nonblocking.
  - apply enumT_of_extracted_list_nodup.
  - apply extracted_enum_complete.
  - apply extracted_enum_sound.
  - apply extracted_zero_offset.
  - exact Htransport_check.
  - exact Hrep.
  - exact Hrep_check.
  - exact Hcoverage.
  - exact Hwindow_check.
  - exact Hwindow_obligation.
  - apply edf_schedulability_decide_true_global_dbf_ok.
    exact Hdec.
Qed.
