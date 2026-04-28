From Stdlib Require Import Arith Arith.PeanoNat Lia Bool.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicTasks.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicFiniteHorizon.

Definition jittered_periodic_jobset
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jitter : TaskId -> Time)
    (jobs : JobId -> Job) : JobId -> Prop :=
  fun j =>
    T (job_task (jobs j)) /\
    generated_by_jittered_periodic_task tasks offset jitter jobs j.

Lemma jittered_periodic_jobset_implies_generated :
  forall T tasks offset jitter jobs j,
    jittered_periodic_jobset T tasks offset jitter jobs j ->
    generated_by_jittered_periodic_task tasks offset jitter jobs j.
Proof.
  intros T tasks offset jitter jobs j [_ Hgen].
  exact Hgen.
Qed.

Lemma jittered_periodic_jobset_implies_task_in_scope :
  forall T tasks offset jitter jobs j,
    jittered_periodic_jobset T tasks offset jitter jobs j ->
    T (job_task (jobs j)).
Proof.
  intros T tasks offset jitter jobs j [HT _].
  exact HT.
Qed.

Lemma jittered_periodic_jobset_implies_valid_job_of_task :
  forall T tasks offset jitter jobs j,
    jittered_periodic_jobset T tasks offset jitter jobs j ->
    valid_job_of_task tasks jobs j.
Proof.
  intros T tasks offset jitter jobs j Hjobset.
  exact
    (generated_jittered_implies_valid_job_of_task
       tasks offset jitter jobs j
       (jittered_periodic_jobset_implies_generated
          T tasks offset jitter jobs j Hjobset)).
Qed.

Lemma jittered_periodic_jobset_upto_implies_jittered_periodic_jobset :
  forall T tasks offset jitter jobs H j,
    jittered_periodic_jobset_upto T tasks offset jitter jobs H j ->
    jittered_periodic_jobset T tasks offset jitter jobs j.
Proof.
  intros T tasks offset jitter jobs H j [HT [Hgen _]].
  split; assumption.
Qed.

Lemma jittered_periodic_jobset_with_release_lt_implies_upto :
  forall T tasks offset jitter jobs H j,
    jittered_periodic_jobset T tasks offset jitter jobs j ->
    job_release (jobs j) < H ->
    jittered_periodic_jobset_upto T tasks offset jitter jobs H j.
Proof.
  intros T tasks offset jitter jobs H j [HT Hgen] Hrel.
  split; [exact HT | split; assumption].
Qed.

