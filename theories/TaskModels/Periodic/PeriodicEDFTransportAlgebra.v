From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Analysis.Uniprocessor.EDFProcessorDemand.
From RocqSched Require Import TaskModels.Periodic.PeriodicCodec.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFCertificate.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFGeneratedPrefixChecker.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFNoCarryInSupply.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFTransportChecker.
From RocqSched Require Import TaskModels.Periodic.PeriodicConcreteAnalysis.
From RocqSched Require Import TaskModels.Periodic.PeriodicInfinite.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.

Import ListNotations.

(** Transport algebra for canonical periodic EDF certificates.

    This file isolates the job-id/index/release/deadline arithmetic needed by
    transport witnesses.  It intentionally does not prove schedule periodicity:
    the remaining schedule-level transport fact is exposed as a small algebra
    obligation that later boolean checkers can target directly. *)

Definition transport_same_task_index_shift
    (jobs : JobId -> Job)
    (rep target : JobId)
    (shift q : nat) : Prop :=
  job_task (jobs target) = job_task (jobs rep) /\
  job_index (jobs target) = job_index (jobs rep) + shift * q.

Definition transport_rep_to_target_job
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (codec : PeriodicCodec T tasks offset jobs)
    (rep target : JobId)
    (shift q : nat) : Prop :=
  target =
    global_periodic_job_id_of
      T tasks offset jobs codec
      (job_task (jobs rep))
      (job_index (jobs rep) + shift * q).

Record TransportClassIndexAlgebra
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (codec : PeriodicCodec T tasks offset jobs)
    (cls : EDFTransportClass JobId)
    (target : JobId)
    (shift q : nat) : Prop := {
  transport_index_rep_in_scope :
    T (job_task (jobs cls.(transport_rep_job)));
  transport_index_target_eq :
    transport_rep_to_target_job
      T tasks offset jobs codec cls.(transport_rep_job) target shift q
}.

Record TransportWindowAlgebra
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (enumT : list TaskId)
    (codec : PeriodicCodec T tasks offset jobs)
    (prefix_cert : EDFPrefixCert JobId)
    (cls : EDFTransportClass JobId)
    (target : JobId)
    (shift : nat) : Prop := {
  transport_window_backlog_lift :
    periodic_edf_backlog_free_before_release
      T tasks offset jobs prefix_cert.(prefix_horizon)
      (generated_periodic_edf_prefix T tasks offset jobs enumT codec prefix_cert)
      cls.(transport_rep_job) ->
    transport_class_backlog_holds
      T tasks offset jobs enumT codec target cls shift
}.

Record TransportBacklogAlgebraObligation
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (enumT : list TaskId)
    (codec : PeriodicCodec T tasks offset jobs)
    (prefix_cert : EDFPrefixCert JobId) : Prop := {
  transport_backlog_window_algebra :
    forall target cls shift,
      TransportWindowAlgebra
        T tasks offset jobs enumT codec prefix_cert cls target shift
}.

Lemma codec_job_task :
  forall T tasks offset jobs
         (codec : PeriodicCodec T tasks offset jobs) τ k,
    T τ ->
    job_task
      (jobs (global_periodic_job_id_of T tasks offset jobs codec τ k)) = τ.
Proof.
  intros T tasks offset jobs codec τ k Hτ.
  destruct (global_periodic_job_id_of_sound
              T tasks offset jobs codec τ k Hτ)
    as [Htask _].
  exact Htask.
Qed.

Lemma codec_job_index :
  forall T tasks offset jobs
         (codec : PeriodicCodec T tasks offset jobs) τ k,
    T τ ->
    job_index
      (jobs (global_periodic_job_id_of T tasks offset jobs codec τ k)) = k.
Proof.
  intros T tasks offset jobs codec τ k Hτ.
  destruct (global_periodic_job_id_of_sound
              T tasks offset jobs codec τ k Hτ)
    as [_ [Hindex _]].
  exact Hindex.
Qed.

Lemma codec_job_generated :
  forall T tasks offset jobs
         (codec : PeriodicCodec T tasks offset jobs) τ k,
    T τ ->
    generated_by_periodic_task
      tasks offset jobs
      (global_periodic_job_id_of T tasks offset jobs codec τ k).
Proof.
  intros T tasks offset jobs codec τ k Hτ.
  destruct (global_periodic_job_id_of_sound
              T tasks offset jobs codec τ k Hτ)
    as [_ [_ Hgen]].
  exact Hgen.
Qed.

Lemma codec_job_release :
  forall T tasks offset jobs
         (codec : PeriodicCodec T tasks offset jobs) τ k,
    T τ ->
    job_release
      (jobs (global_periodic_job_id_of T tasks offset jobs codec τ k)) =
    expected_release tasks offset τ k.
Proof.
  intros T tasks offset jobs codec τ k Hτ.
  pose proof (codec_job_generated T tasks offset jobs codec τ k Hτ) as Hgen.
  pose proof
    (generated_job_release
       tasks offset jobs
       (global_periodic_job_id_of T tasks offset jobs codec τ k)
       Hgen) as Hrel.
  rewrite (codec_job_task T tasks offset jobs codec τ k Hτ) in Hrel.
  rewrite (codec_job_index T tasks offset jobs codec τ k Hτ) in Hrel.
  exact Hrel.
Qed.

Lemma codec_job_deadline :
  forall T tasks offset jobs
         (codec : PeriodicCodec T tasks offset jobs) τ k,
    T τ ->
    job_abs_deadline
      (jobs (global_periodic_job_id_of T tasks offset jobs codec τ k)) =
    expected_abs_deadline tasks offset τ k.
Proof.
  intros T tasks offset jobs codec τ k Hτ.
  pose proof (codec_job_generated T tasks offset jobs codec τ k Hτ) as Hgen.
  destruct Hgen as [_ [Hdeadline _]].
  rewrite (codec_job_task T tasks offset jobs codec τ k Hτ) in Hdeadline.
  rewrite (codec_job_index T tasks offset jobs codec τ k Hτ) in Hdeadline.
  exact Hdeadline.
Qed.

Lemma transport_rep_to_target_job_same_task_index_shift :
  forall T tasks offset jobs
         (codec : PeriodicCodec T tasks offset jobs)
         rep target shift q,
    T (job_task (jobs rep)) ->
    transport_rep_to_target_job
      T tasks offset jobs codec rep target shift q ->
    transport_same_task_index_shift jobs rep target shift q.
Proof.
  intros T tasks offset jobs codec rep target shift q HrepT Htarget.
  unfold transport_rep_to_target_job in Htarget.
  subst target.
  split.
  - apply codec_job_task.
    exact HrepT.
  - apply codec_job_index.
    exact HrepT.
Qed.

Lemma periodic_residue_rep_to_job_transport :
  forall T tasks offset jobs
         (codec : PeriodicCodec T tasks offset jobs)
         period j,
    0 < period ->
    periodic_jobset T tasks offset jobs j ->
    let rep :=
      global_periodic_job_id_of
        T tasks offset jobs codec
        (job_task (jobs j))
        (job_index (jobs j) mod period) in
    transport_rep_to_target_job
      T tasks offset jobs codec
      rep j period (job_index (jobs j) / period).
Proof.
  intros T tasks offset jobs codec period j Hperiod Hjob rep.
  unfold transport_rep_to_target_job, rep.
  replace
    (job_task
       (jobs
          (global_periodic_job_id_of
             T tasks offset jobs codec
             (job_task (jobs j))
             (job_index (jobs j) mod period))))
    with (job_task (jobs j)).
  2: {
    symmetry.
    apply codec_job_task.
    exact (proj1 Hjob).
  }
  replace
    (job_index
       (jobs
          (global_periodic_job_id_of
             T tasks offset jobs codec
             (job_task (jobs j))
             (job_index (jobs j) mod period))) +
     period * (job_index (jobs j) / period))
    with (job_index (jobs j)).
  2: {
    rewrite (codec_job_index
               T tasks offset jobs codec
               (job_task (jobs j))
               (job_index (jobs j) mod period)
               (proj1 Hjob)).
    rewrite Nat.add_comm.
    exact (Nat.div_mod (job_index (jobs j)) period ltac:(lia)).
  }
  exact (global_periodic_job_id_of_complete
           T tasks offset jobs codec j Hjob).
Qed.

Lemma expected_release_shift :
  forall tasks offset τ k shift q,
    expected_release tasks offset τ (k + shift * q) =
    expected_release tasks offset τ k + shift * q * task_period (tasks τ).
Proof.
  intros tasks offset τ k shift q.
  unfold expected_release.
  lia.
Qed.

Lemma expected_deadline_shift :
  forall tasks offset τ k shift q,
    expected_abs_deadline tasks offset τ (k + shift * q) =
    expected_abs_deadline tasks offset τ k +
    shift * q * task_period (tasks τ).
Proof.
  intros tasks offset τ k shift q.
  unfold expected_abs_deadline.
  rewrite expected_release_shift.
  lia.
Qed.

Lemma codec_transport_target_release_shift :
  forall T tasks offset jobs
         (codec : PeriodicCodec T tasks offset jobs)
         rep target shift q,
    T (job_task (jobs rep)) ->
    generated_by_periodic_task tasks offset jobs rep ->
    transport_rep_to_target_job
      T tasks offset jobs codec rep target shift q ->
    job_release (jobs target) =
    job_release (jobs rep) +
    shift * q * task_period (tasks (job_task (jobs rep))).
Proof.
  intros T tasks offset jobs codec rep target shift q HrepT Hrep_gen Htarget.
  unfold transport_rep_to_target_job in Htarget.
  subst target.
  rewrite (codec_job_release
             T tasks offset jobs codec
             (job_task (jobs rep))
             (job_index (jobs rep) + shift * q) HrepT).
  rewrite (generated_job_release tasks offset jobs rep Hrep_gen).
  apply expected_release_shift.
Qed.

Lemma codec_transport_target_deadline_shift :
  forall T tasks offset jobs
         (codec : PeriodicCodec T tasks offset jobs)
         rep target shift q,
    T (job_task (jobs rep)) ->
    generated_by_periodic_task tasks offset jobs rep ->
    transport_rep_to_target_job
      T tasks offset jobs codec rep target shift q ->
    job_abs_deadline (jobs target) =
    job_abs_deadline (jobs rep) +
    shift * q * task_period (tasks (job_task (jobs rep))).
Proof.
  intros T tasks offset jobs codec rep target shift q HrepT Hrep_gen Htarget.
  unfold transport_rep_to_target_job in Htarget.
  subst target.
  rewrite (codec_job_deadline
             T tasks offset jobs codec
             (job_task (jobs rep))
             (job_index (jobs rep) + shift * q) HrepT).
  destruct Hrep_gen as [Hrel [Hdeadline Hcost]].
  rewrite Hdeadline.
  apply expected_deadline_shift.
Qed.

Lemma codec_transport_target_release_hyperperiod_multiple :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs)
         rep target q,
    T (job_task (jobs rep)) ->
    generated_by_periodic_task tasks offset jobs rep ->
    transport_rep_to_target_job
      T tasks offset jobs codec rep target
      (periodic_hyperperiod tasks enumT) q ->
    exists n,
      job_release (jobs target) =
      job_release (jobs rep) + periodic_hyperperiod tasks enumT * n.
Proof.
  intros T tasks offset jobs enumT codec rep target q
         HrepT Hrep_gen Htarget.
  exists (q * task_period (tasks (job_task (jobs rep)))).
  rewrite
    (codec_transport_target_release_shift
       T tasks offset jobs codec rep target
       (periodic_hyperperiod tasks enumT) q
       HrepT Hrep_gen Htarget).
  lia.
Qed.

Lemma codec_transport_target_deadline_hyperperiod_multiple :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs)
         rep target q,
    T (job_task (jobs rep)) ->
    generated_by_periodic_task tasks offset jobs rep ->
    transport_rep_to_target_job
      T tasks offset jobs codec rep target
      (periodic_hyperperiod tasks enumT) q ->
    exists n,
      job_abs_deadline (jobs target) =
      job_abs_deadline (jobs rep) + periodic_hyperperiod tasks enumT * n.
Proof.
  intros T tasks offset jobs enumT codec rep target q
         HrepT Hrep_gen Htarget.
  exists (q * task_period (tasks (job_task (jobs rep)))).
  rewrite
    (codec_transport_target_deadline_shift
       T tasks offset jobs codec rep target
       (periodic_hyperperiod tasks enumT) q
       HrepT Hrep_gen Htarget).
  lia.
Qed.

Lemma transport_window_algebra_sound :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs)
         prefix_cert cls target shift,
    TransportWindowAlgebra
      T tasks offset jobs enumT codec prefix_cert cls target shift ->
    periodic_edf_backlog_free_before_release
      T tasks offset jobs prefix_cert.(prefix_horizon)
      (generated_periodic_edf_prefix T tasks offset jobs enumT codec prefix_cert)
      cls.(transport_rep_job) ->
    transport_class_backlog_holds
      T tasks offset jobs enumT codec target cls shift.
Proof.
  intros T tasks offset jobs enumT codec prefix_cert cls target shift
         Halgebra Hrep.
  exact (transport_window_backlog_lift
           T tasks offset jobs enumT codec prefix_cert cls target shift
           Halgebra Hrep).
Qed.
