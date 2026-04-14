From Stdlib Require Import Arith Arith.PeanoNat Lia Bool.
From RocqSched Require Import Foundation.Base.

(* ===== Sporadic Task Model ===== *)

(* No two distinct jobs in J share the same task and job index.
   This is the uniqueness invariant that makes index-based reasoning coherent. *)
Definition unique_task_index_on
    (J : JobId -> Prop)
    (jobs : JobId -> Job) : Prop :=
  forall j1 j2,
    J j1 -> J j2 ->
    job_task (jobs j1) = job_task (jobs j2) ->
    job_index (jobs j1) = job_index (jobs j2) ->
    j1 = j2.

(* Minimum inter-arrival constraint for sporadic tasks.
   For any two jobs j1, j2 in J from the same task with j1.index < j2.index:
     j1.release + (j2.index - j1.index) * period(task) <= j2.release *)
Definition sporadic_separation_on
    (J : JobId -> Prop)
    (tasks : TaskId -> Task)
    (jobs : JobId -> Job) : Prop :=
  forall j1 j2,
    J j1 -> J j2 ->
    job_task (jobs j1) = job_task (jobs j2) ->
    job_index (jobs j1) < job_index (jobs j2) ->
    job_release (jobs j1)
      + (job_index (jobs j2) - job_index (jobs j1))
        * task_period (tasks (job_task (jobs j1)))
      <= job_release (jobs j2).

(* The sporadic job model on a designated job set J and task set T:
   - every job in J belongs to a task in T
   - every job in J satisfies the local task consistency predicate (valid_job_of_task)
   - job indices are unique within each task
   - consecutive jobs respect the minimum inter-arrival constraint *)
Definition sporadic_job_model_on
    (J : JobId -> Prop)
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (jobs : JobId -> Job) : Prop :=
  (forall j, J j -> T (job_task (jobs j))) /\
  (forall j, J j -> valid_job_of_task tasks jobs j) /\
  unique_task_index_on J jobs /\
  sporadic_separation_on J tasks jobs.

(* ===== Basic Lemmas ===== *)

Lemma sporadic_job_model_on_implies_task_in_scope :
  forall J T tasks jobs j,
    sporadic_job_model_on J T tasks jobs ->
    J j ->
    T (job_task (jobs j)).
Proof.
  intros J T tasks jobs j [Hscope _] Hj.
  exact (Hscope j Hj).
Qed.

Lemma sporadic_job_model_on_implies_valid_job_of_task :
  forall J T tasks jobs j,
    sporadic_job_model_on J T tasks jobs ->
    J j ->
    valid_job_of_task tasks jobs j.
Proof.
  intros J T tasks jobs j [_ [Hvalid _]] Hj.
  exact (Hvalid j Hj).
Qed.

Lemma sporadic_job_model_on_implies_unique_index :
  forall J T tasks jobs,
    sporadic_job_model_on J T tasks jobs ->
    unique_task_index_on J jobs.
Proof.
  intros J T tasks jobs [_ [_ [Huniq _]]].
  exact Huniq.
Qed.

Lemma sporadic_job_model_on_implies_separation :
  forall J T tasks jobs,
    sporadic_job_model_on J T tasks jobs ->
    sporadic_separation_on J tasks jobs.
Proof.
  intros J T tasks jobs [_ [_ [_ Hsep]]].
  exact Hsep.
Qed.

(* Special case of sporadic_separation_on for consecutive indices (k, k+1).
   Useful when reasoning about adjacent sporadic job releases. *)
Lemma sporadic_separation_on_consecutive :
  forall J tasks jobs j1 j2,
    sporadic_separation_on J tasks jobs ->
    J j1 -> J j2 ->
    job_task (jobs j1) = job_task (jobs j2) ->
    job_index (jobs j2) = S (job_index (jobs j1)) ->
    job_release (jobs j1) + task_period (tasks (job_task (jobs j1)))
      <= job_release (jobs j2).
Proof.
  intros J tasks jobs j1 j2 Hsep Hj1 Hj2 Htask Hidx.
  pose proof (Hsep j1 j2 Hj1 Hj2 Htask) as H.
  assert (Hlt : job_index (jobs j1) < job_index (jobs j2)) by lia.
  pose proof (H Hlt) as Hsep'.
  rewrite Hidx in Hsep'.
  lia.
Qed.
