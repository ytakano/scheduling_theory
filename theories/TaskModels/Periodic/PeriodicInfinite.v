From Stdlib Require Import Arith Arith.PeanoNat Lia Bool.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Periodic.PeriodicFiniteHorizon.

Definition periodic_jobset
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job) : JobId -> Prop :=
  fun j =>
    T (job_task (jobs j)) /\
    generated_by_periodic_task tasks offset jobs j.

Lemma periodic_jobset_implies_generated :
  forall T tasks offset jobs j,
    periodic_jobset T tasks offset jobs j ->
    generated_by_periodic_task tasks offset jobs j.
Proof.
  intros T tasks offset jobs j [_ Hgen].
  exact Hgen.
Qed.

Lemma periodic_jobset_implies_task_in_scope :
  forall T tasks offset jobs j,
    periodic_jobset T tasks offset jobs j ->
    T (job_task (jobs j)).
Proof.
  intros T tasks offset jobs j [HT _].
  exact HT.
Qed.

Lemma periodic_jobset_implies_valid_job_of_task :
  forall T tasks offset jobs j,
    periodic_jobset T tasks offset jobs j ->
    valid_job_of_task tasks jobs j.
Proof.
  intros T tasks offset jobs j Hjobset.
  exact
    (generated_implies_valid_job_of_task
       tasks offset jobs j
       (periodic_jobset_implies_generated T tasks offset jobs j Hjobset)).
Qed.

Lemma periodic_jobset_upto_implies_periodic_jobset :
  forall T tasks offset jobs H j,
    periodic_jobset_upto T tasks offset jobs H j ->
    periodic_jobset T tasks offset jobs j.
Proof.
  intros T tasks offset jobs H j [HT [Hgen _]].
  split; assumption.
Qed.
