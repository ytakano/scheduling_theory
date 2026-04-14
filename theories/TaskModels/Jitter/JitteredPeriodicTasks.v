From Stdlib Require Import Arith Arith.PeanoNat Lia Bool.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Jitter.ReleaseJitter.

Definition generated_by_jittered_periodic_task
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jitter : TaskId -> Time)
    (jobs : JobId -> Job)
    (j : JobId) : Prop :=
  let τ := job_task (jobs j) in
  let k := job_index (jobs j) in
  within_jitter
    (expected_release tasks offset τ k)
    (job_release (jobs j))
    (jitter τ) /\
  valid_job_of_task tasks jobs j.

Definition generated_by_jittered_periodic_task_b
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jitter : TaskId -> Time)
    (jobs : JobId -> Job)
    (j : JobId) : bool :=
  within_jitter_b
    (expected_release tasks offset (job_task (jobs j)) (job_index (jobs j)))
    (job_release (jobs j))
    (jitter (job_task (jobs j)))
  &&
  Nat.eqb
    (job_abs_deadline (jobs j))
    (job_release (jobs j) + task_relative_deadline (tasks (job_task (jobs j))))
  &&
  Nat.leb
    (job_cost (jobs j))
    (task_cost (tasks (job_task (jobs j)))).

Definition jittered_periodic_job_model_on
    (J : JobId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jitter : TaskId -> Time)
    (jobs : JobId -> Job) : Prop :=
  forall j, J j -> generated_by_jittered_periodic_task tasks offset jitter jobs j.

Lemma generated_by_jittered_periodic_task_b_spec :
  forall tasks offset jitter jobs j,
    generated_by_jittered_periodic_task_b tasks offset jitter jobs j = true <->
    generated_by_jittered_periodic_task tasks offset jitter jobs j.
Proof.
  intros tasks offset jitter jobs j.
  unfold generated_by_jittered_periodic_task_b,
         generated_by_jittered_periodic_task,
         valid_job_of_task.
  rewrite !andb_true_iff.
  rewrite within_jitter_b_spec, Nat.eqb_eq, Nat.leb_le.
  tauto.
Qed.

Lemma generated_jittered_job_release_lb :
  forall tasks offset jitter jobs j,
    generated_by_jittered_periodic_task tasks offset jitter jobs j ->
    expected_release tasks offset (job_task (jobs j)) (job_index (jobs j))
      <= job_release (jobs j).
Proof.
  intros tasks offset jitter jobs j Hgen.
  exact (within_jitter_implies_lower_bound _ _ _
    (proj1 Hgen)).
Qed.

Lemma generated_jittered_job_release_ub :
  forall tasks offset jitter jobs j,
    generated_by_jittered_periodic_task tasks offset jitter jobs j ->
    job_release (jobs j) <=
      expected_release tasks offset (job_task (jobs j)) (job_index (jobs j))
      + jitter (job_task (jobs j)).
Proof.
  intros tasks offset jitter jobs j Hgen.
  exact (within_jitter_implies_upper_bound _ _ _
    (proj1 Hgen)).
Qed.

Lemma generated_jittered_job_deadline :
  forall tasks offset jitter jobs j,
    generated_by_jittered_periodic_task tasks offset jitter jobs j ->
    job_abs_deadline (jobs j) =
      job_release (jobs j) + task_relative_deadline (tasks (job_task (jobs j))).
Proof.
  intros tasks offset jitter jobs j Hgen.
  exact (proj1 (proj2 Hgen)).
Qed.

Lemma generated_jittered_job_cost_bounded :
  forall tasks offset jitter jobs j,
    generated_by_jittered_periodic_task tasks offset jitter jobs j ->
    job_cost (jobs j) <= task_cost (tasks (job_task (jobs j))).
Proof.
  intros tasks offset jitter jobs j Hgen.
  exact (proj2 (proj2 Hgen)).
Qed.

Lemma generated_jittered_implies_valid_job_of_task :
  forall tasks offset jitter jobs j,
    generated_by_jittered_periodic_task tasks offset jitter jobs j ->
    valid_job_of_task tasks jobs j.
Proof.
  intros tasks offset jitter jobs j Hgen.
  exact (proj2 Hgen).
Qed.

Lemma generated_by_periodic_implies_jittered_periodic :
  forall tasks offset jitter jobs j,
    generated_by_periodic_task tasks offset jobs j ->
    generated_by_jittered_periodic_task tasks offset jitter jobs j.
Proof.
  intros tasks offset jitter jobs j Hgen.
  split.
  - unfold within_jitter.
    split.
    + rewrite <- (generated_job_release tasks offset jobs j Hgen).
      lia.
    + rewrite (generated_job_release tasks offset jobs j Hgen).
      lia.
  - exact (generated_implies_valid_job_of_task tasks offset jobs j Hgen).
Qed.
