From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.EnumCandidates.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicInfiniteJobset.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicCodec.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicEnumeration.
Import ListNotations.

Definition jittered_periodic_candidates_before
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jitter : TaskId -> Time)
    (jobs : JobId -> Job)
    (enumT : list TaskId)
    (codec : JitteredPeriodicCodec T tasks offset jitter jobs)
  : CandidateSource :=
  fun _ _ _ t =>
    enum_jittered_periodic_jobs_before
      T tasks offset jitter jobs enumT codec (S t).

Lemma jittered_periodic_candidates_before_prefix_extensional :
  forall T tasks offset jitter jobs enumT
         (codec : JitteredPeriodicCodec T tasks offset jitter jobs)
         jobs' m s1 s2 t,
    jittered_periodic_candidates_before
      T tasks offset jitter jobs enumT codec jobs' m s1 t =
    jittered_periodic_candidates_before
      T tasks offset jitter jobs enumT codec jobs' m s2 t.
Proof.
  intros.
  unfold jittered_periodic_candidates_before.
  reflexivity.
Qed.

Lemma jittered_periodic_candidates_before_sound :
  forall T tasks offset jitter jobs enumT
         (codec : JitteredPeriodicCodec T tasks offset jitter jobs),
    (forall τ, In τ enumT -> T τ) ->
    forall jobs' m s t j,
      In j (jittered_periodic_candidates_before
              T tasks offset jitter jobs enumT codec jobs' m s t) ->
      jittered_periodic_jobset T tasks offset jitter jobs j /\
      job_release (jobs j) < S t.
Proof.
  intros T tasks offset jitter jobs enumT codec HenumT_sound jobs' m s t j Hj.
  unfold jittered_periodic_candidates_before in Hj.
  eapply enum_jittered_periodic_jobs_before_sound; eauto.
Qed.

Lemma jittered_periodic_candidates_before_complete :
  forall T tasks offset jitter jobs enumT
         (codec : JitteredPeriodicCodec T tasks offset jitter jobs),
    well_formed_periodic_tasks_on T tasks ->
    (forall τ, T τ -> In τ enumT) ->
    forall jobs' m s t j,
      jittered_periodic_jobset T tasks offset jitter jobs j ->
      job_release (jobs j) < S t ->
      In j (jittered_periodic_candidates_before
              T tasks offset jitter jobs enumT codec jobs' m s t).
Proof.
  intros T tasks offset jitter jobs enumT codec Hwf HenumT_complete jobs' m s t j Hjob Hrel.
  unfold jittered_periodic_candidates_before.
  eapply enum_jittered_periodic_jobs_before_complete; eauto.
Qed.

Lemma jittered_periodic_candidates_before_nodup :
  forall T tasks offset jitter jobs enumT
         (codec : JitteredPeriodicCodec T tasks offset jitter jobs),
    NoDup enumT ->
    (forall τ, In τ enumT -> T τ) ->
    forall jobs' m s t,
      NoDup
        (jittered_periodic_candidates_before
           T tasks offset jitter jobs enumT codec jobs' m s t).
Proof.
  intros T tasks offset jitter jobs enumT codec HnodupT HenumT jobs' m s t.
  unfold jittered_periodic_candidates_before.
  apply enum_jittered_periodic_jobs_before_nodup; assumption.
Qed.

Lemma jittered_periodic_candidates_before_prefix_monotone :
  forall T tasks offset jitter jobs enumT
         (codec : JitteredPeriodicCodec T tasks offset jitter jobs),
    well_formed_periodic_tasks_on T tasks ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    forall jobs' m s t1 t2 j,
      t1 <= t2 ->
      In j (jittered_periodic_candidates_before
              T tasks offset jitter jobs enumT codec jobs' m s t1) ->
      In j (jittered_periodic_candidates_before
              T tasks offset jitter jobs enumT codec jobs' m s t2).
Proof.
  intros T tasks offset jitter jobs enumT codec Hwf HenumT_complete HenumT_sound
         jobs' m s t1 t2 j Hle Hin.
  pose proof
    (jittered_periodic_candidates_before_sound
       T tasks offset jitter jobs enumT codec HenumT_sound
       jobs' m s t1 j Hin) as [Hjob Hrel].
  eapply jittered_periodic_candidates_before_complete; eauto.
  lia.
Qed.
