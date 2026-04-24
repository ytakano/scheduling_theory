From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Analysis.Uniprocessor.BusyWindowSearch.
From RocqSched Require Import Analysis.Uniprocessor.EDFProcessorDemand.
From RocqSched Require Import TaskModels.Periodic.PeriodicCodec.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFCertificate.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFGeneratedPrefixChecker.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFInfiniteBridge.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFNoCarryInSupply.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFTransportAlgebra.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFTransportChecker.
From RocqSched Require Import TaskModels.Periodic.PeriodicInfinite.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Periodic.PeriodicWindowDemandBound.

Import ListNotations.

(** Schedule-level transport interface for periodic EDF windows.

    [TransportWindowAlgebra] deliberately exposes only the final bridge needed
    by the checked transport witness layer.  This file decomposes that bridge
    into smaller proof obligations: a representative-window completion source,
    a mapping from each target-window earlier job to a representative-window
    job, and a completion transport fact between the two generated schedules.

    The definitions remain propositional.  They are intended as the next stable
    target for boolean checkers without baking a particular runtime schedule
    encoding into the common theory layer. *)

Definition representative_earlier_completion_before_release
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (sched : Schedule)
    (rep : JobId) : Prop :=
  forall x,
    periodic_jobset_deadline_between
      T tasks offset jobs 0 (job_abs_deadline (jobs rep)) x ->
    job_release (jobs x) < job_release (jobs rep) ->
    completed jobs 1 sched x (job_release (jobs rep)).

Record ShiftedJobRelation
    (jobs : JobId -> Job)
    (rep target x_rep x : JobId)
    (delta : Time) : Prop := {
  shifted_target_release :
    job_release (jobs target) = job_release (jobs rep) + delta;
  shifted_target_deadline :
    job_abs_deadline (jobs target) = job_abs_deadline (jobs rep) + delta;
  shifted_earlier_release :
    job_release (jobs x) = job_release (jobs x_rep) + delta;
  shifted_earlier_deadline :
    job_abs_deadline (jobs x) = job_abs_deadline (jobs x_rep) + delta
}.

Record ShiftedCompletionTransport
    (jobs : JobId -> Job)
    (rep_sched target_sched : Schedule)
    (rep target x_rep x : JobId) : Prop := {
  shifted_completion_at_release :
    completed jobs 1 rep_sched x_rep (job_release (jobs rep)) ->
    completed jobs 1 target_sched x (job_release (jobs target))
}.

Record GeneratedShiftedCompletionTransport
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (enumT : list TaskId)
    (codec : PeriodicCodec T tasks offset jobs)
    (prefix_cert : EDFPrefixCert JobId)
    (rep target x_rep x : JobId) : Prop := {
  generated_shifted_completion_at_release :
    completed jobs 1
      (generated_periodic_edf_prefix
         T tasks offset jobs enumT codec prefix_cert)
      x_rep (job_release (jobs rep)) ->
    completed jobs 1
      (generated_periodic_edf_schedule T tasks offset jobs enumT codec)
      x (job_release (jobs target))
}.

Theorem generated_shifted_completion_transport_sound :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs)
         prefix_cert rep target x_rep x,
    well_formed_periodic_tasks_on T tasks ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    periodic_jobset T tasks offset jobs target ->
    GeneratedShiftedCompletionTransport
      T tasks offset jobs enumT codec prefix_cert rep target x_rep x ->
    ShiftedCompletionTransport
      jobs
      (generated_periodic_edf_prefix
         T tasks offset jobs enumT codec prefix_cert)
      (generated_periodic_edf_schedule_upto
         T tasks offset jobs (S (job_abs_deadline (jobs target))) enumT codec)
      rep target x_rep x.
Proof.
  intros T tasks offset jobs enumT codec prefix_cert rep target x_rep x
         Hwf HenumT_complete HenumT_sound Htarget Htransport.
  constructor.
  intros Hrep_completed.
  assert (Htarget_release :
    job_release (jobs target) < S (job_abs_deadline (jobs target))).
  {
    destruct Htarget as [_ Hgen].
    pose proof (generated_job_deadline tasks offset jobs target Hgen).
    lia.
  }
  pose proof
    (generated_periodic_edf_schedule_upto_completed_iff_generated_before
       T tasks offset jobs enumT codec
       (S (job_abs_deadline (jobs target)))
       x (job_release (jobs target))
       Hwf HenumT_complete HenumT_sound Htarget_release)
    as Hiff.
  apply (proj2 Hiff).
  exact
    (generated_shifted_completion_at_release
       T tasks offset jobs enumT codec prefix_cert
       rep target x_rep x Htransport Hrep_completed).
Qed.

Record ShiftedBacklogWindowTransport
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (rep_sched target_sched : Schedule)
    (rep target : JobId) : Prop := {
  shifted_window_rep_backlog_to_completion :
    periodic_edf_backlog_free_before_release
      T tasks offset jobs
      (job_abs_deadline (jobs rep))
      rep_sched
      rep ->
    representative_earlier_completion_before_release
      T tasks offset jobs rep_sched rep;
  shifted_window_target_earlier_job :
    forall t1 t2 x,
      busy_prefix_witness target_sched (job_abs_deadline (jobs target)) t1 t2 ->
      t1 <= job_release (jobs target) ->
      periodic_jobset_deadline_between
        T tasks offset jobs t1 (job_abs_deadline (jobs target)) x ->
      job_release (jobs x) < job_release (jobs target) ->
      exists x_rep,
        periodic_jobset_deadline_between
          T tasks offset jobs 0 (job_abs_deadline (jobs rep)) x_rep /\
        job_release (jobs x_rep) < job_release (jobs rep) /\
        ShiftedCompletionTransport
          jobs rep_sched target_sched rep target x_rep x
}.

Theorem shifted_backlog_window_transport_sound :
  forall T tasks offset jobs rep_sched target_sched rep target,
    ShiftedBacklogWindowTransport
      T tasks offset jobs rep_sched target_sched rep target ->
    periodic_edf_backlog_free_before_release
      T tasks offset jobs
      (job_abs_deadline (jobs rep))
      rep_sched
      rep ->
    periodic_edf_backlog_free_before_release
      T tasks offset jobs
      (job_abs_deadline (jobs target))
      target_sched
      target.
Proof.
  intros T tasks offset jobs rep_sched target_sched rep target
         Htransport Hrep_backlog.
  unfold periodic_edf_backlog_free_before_release.
  intros t1 t2 x Hbusy Ht1 Hbetween Hrelease.
  pose proof
    (shifted_window_target_earlier_job
       T tasks offset jobs rep_sched target_sched rep target
       Htransport t1 t2 x Hbusy Ht1 Hbetween Hrelease)
    as [x_rep [Hrep_between [Hrep_release Hcomplete_transport]]].
  pose proof
    (shifted_window_rep_backlog_to_completion
       T tasks offset jobs rep_sched target_sched rep target
       Htransport Hrep_backlog)
    as Hrep_done.
  exact
    (shifted_completion_at_release
       jobs rep_sched target_sched rep target x_rep x Hcomplete_transport
       (Hrep_done x_rep Hrep_between Hrep_release)).
Qed.

Theorem shifted_generated_window_transport_algebra :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs)
         prefix_cert cls target shift,
    ShiftedBacklogWindowTransport
      T tasks offset jobs
      (generated_periodic_edf_prefix T tasks offset jobs enumT codec prefix_cert)
      (generated_periodic_edf_schedule_upto
         T tasks offset jobs (S (job_abs_deadline (jobs target))) enumT codec)
      cls.(transport_rep_job)
      target ->
    TransportWindowAlgebra
      T tasks offset jobs enumT codec prefix_cert cls target shift.
Proof.
  intros T tasks offset jobs enumT codec prefix_cert cls target shift
         Htransport.
  constructor.
  intros Hrep_backlog.
  exact
    (shifted_backlog_window_transport_sound
       T tasks offset jobs
       (generated_periodic_edf_prefix T tasks offset jobs enumT codec prefix_cert)
       (generated_periodic_edf_schedule_upto
          T tasks offset jobs (S (job_abs_deadline (jobs target))) enumT codec)
       cls.(transport_rep_job)
       target
       Htransport
       Hrep_backlog).
Qed.

Record ShiftedGeneratedWindowTransportObligation
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (enumT : list TaskId)
    (codec : PeriodicCodec T tasks offset jobs)
    (prefix_cert : EDFPrefixCert JobId) : Prop := {
  shifted_generated_window_transport :
    forall target cls (shift : nat),
      ShiftedBacklogWindowTransport
        T tasks offset jobs
        (generated_periodic_edf_prefix T tasks offset jobs enumT codec prefix_cert)
        (generated_periodic_edf_schedule_upto
           T tasks offset jobs (S (job_abs_deadline (jobs target))) enumT codec)
        cls.(transport_rep_job)
        target
}.

Theorem transport_backlog_algebra_of_shifted_generated_window :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs)
         prefix_cert,
    ShiftedGeneratedWindowTransportObligation
      T tasks offset jobs enumT codec prefix_cert ->
    TransportBacklogAlgebraObligation
      T tasks offset jobs enumT codec prefix_cert.
Proof.
  intros T tasks offset jobs enumT codec prefix_cert Hshifted.
  constructor.
  intros target cls shift.
  apply shifted_generated_window_transport_algebra.
  exact
    (shifted_generated_window_transport
       T tasks offset jobs enumT codec prefix_cert
       Hshifted target cls shift).
Qed.
