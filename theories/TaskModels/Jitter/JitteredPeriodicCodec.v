From Stdlib Require Import Arith Arith.PeanoNat Lia Bool List.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicTasks.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicFiniteHorizon.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicInfiniteJobset.
Import ListNotations.

Record JitteredPeriodicCodec
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jitter : TaskId -> Time)
    (jobs : JobId -> Job) : Type := mkJitteredPeriodicCodec {
  global_jittered_periodic_job_id_of : TaskId -> nat -> JobId;

  global_jittered_periodic_job_id_of_sound :
    forall τ k,
      T τ ->
      let j := global_jittered_periodic_job_id_of τ k in
      job_task (jobs j) = τ /\
      job_index (jobs j) = k /\
      generated_by_jittered_periodic_task tasks offset jitter jobs j;

  global_jittered_periodic_job_id_of_complete :
    forall j,
      jittered_periodic_jobset T tasks offset jitter jobs j ->
      j =
      global_jittered_periodic_job_id_of
        (job_task (jobs j)) (job_index (jobs j))
}.

Record JitteredPeriodicFiniteHorizonCodec
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jitter : TaskId -> Time)
    (jobs : JobId -> Job)
    (H : Time) : Type := mkJitteredPeriodicFiniteHorizonCodec {

  jittered_periodic_job_id_of : TaskId -> nat -> JobId;

  jittered_periodic_job_id_of_sound :
    forall τ k,
      T τ ->
      expected_release tasks offset τ k < H ->
      let j := jittered_periodic_job_id_of τ k in
      job_task (jobs j) = τ /\
      job_index (jobs j) = k /\
      generated_by_jittered_periodic_task tasks offset jitter jobs j;

  jittered_periodic_job_id_of_complete :
    forall j,
      jittered_periodic_jobset_upto T tasks offset jitter jobs H j ->
      j =
      jittered_periodic_job_id_of
        (job_task (jobs j)) (job_index (jobs j))
}.

Definition jittered_periodic_finite_horizon_codec_of
    T tasks offset jitter jobs H
    (codec : JitteredPeriodicCodec T tasks offset jitter jobs)
  : JitteredPeriodicFiniteHorizonCodec T tasks offset jitter jobs H.
Proof.
  refine
    (mkJitteredPeriodicFiniteHorizonCodec
       T tasks offset jitter jobs H
       (global_jittered_periodic_job_id_of
          T tasks offset jitter jobs codec) _ _).
  - intros τ k HT _.
    exact
      (global_jittered_periodic_job_id_of_sound
         T tasks offset jitter jobs codec τ k HT).
  - intros j Hjobset.
    apply global_jittered_periodic_job_id_of_complete.
    exact
      (jittered_periodic_jobset_upto_implies_jittered_periodic_jobset
         T tasks offset jitter jobs H j Hjobset).
Defined.

Lemma codec_jittered_periodic_jobs_same_task_index_eq :
  forall T tasks offset jitter jobs H
         (codec : JitteredPeriodicFiniteHorizonCodec
                     T tasks offset jitter jobs H)
         j1 j2,
    jittered_periodic_jobset_upto T tasks offset jitter jobs H j1 ->
    jittered_periodic_jobset_upto T tasks offset jitter jobs H j2 ->
    job_task (jobs j1) = job_task (jobs j2) ->
    job_index (jobs j1) = job_index (jobs j2) ->
    j1 = j2.
Proof.
  intros T tasks offset jitter jobs H codec j1 j2 Hj1 Hj2 Htask Hidx.
  rewrite
    (jittered_periodic_job_id_of_complete
       T tasks offset jitter jobs H codec j1 Hj1).
  rewrite
    (jittered_periodic_job_id_of_complete
       T tasks offset jitter jobs H codec j2 Hj2).
  now rewrite Htask, Hidx.
Qed.

