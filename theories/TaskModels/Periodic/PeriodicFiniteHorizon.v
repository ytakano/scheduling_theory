From Stdlib Require Import Arith Arith.PeanoNat Lia Bool.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.

Definition periodic_jobset_upto
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (H : Time) : JobId -> Prop :=
  fun j =>
    T (job_task (jobs j)) /\
    generated_by_periodic_task tasks offset jobs j /\
    job_release (jobs j) < H.

Definition periodic_jobset_upto_bool
    (T_bool : TaskId -> bool)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (H : Time) : JobId -> bool :=
  fun j =>
    T_bool (job_task (jobs j))
    &&
    generated_by_periodic_task_b tasks offset jobs j
    &&
    Nat.ltb (job_release (jobs j)) H.

Lemma periodic_jobset_upto_bool_spec :
  forall T T_bool tasks offset jobs H,
    (forall τ, T_bool τ = true <-> T τ) ->
    forall j,
      periodic_jobset_upto_bool T_bool tasks offset jobs H j = true <->
      periodic_jobset_upto T tasks offset jobs H j.
Proof.
  intros T T_bool tasks offset jobs H HT j.
  unfold periodic_jobset_upto_bool, periodic_jobset_upto.
  rewrite !andb_true_iff.
  rewrite generated_by_periodic_task_b_spec.
  rewrite Nat.ltb_lt.
  rewrite HT.
  tauto.
Qed.

Lemma periodic_jobset_upto_implies_generated :
  forall T tasks offset jobs H j,
    periodic_jobset_upto T tasks offset jobs H j ->
    generated_by_periodic_task tasks offset jobs j.
Proof.
  intros T tasks offset jobs H j [_ [Hgen _]].
  exact Hgen.
Qed.

Lemma periodic_jobset_upto_implies_task_in_scope :
  forall T tasks offset jobs H j,
    periodic_jobset_upto T tasks offset jobs H j ->
    T (job_task (jobs j)).
Proof.
  intros T tasks offset jobs H j [HT _].
  exact HT.
Qed.

Lemma periodic_jobset_upto_implies_release_lt :
  forall T tasks offset jobs H j,
    periodic_jobset_upto T tasks offset jobs H j ->
    job_release (jobs j) < H.
Proof.
  intros T tasks offset jobs H j [_ [_ Hrel]].
  exact Hrel.
Qed.

Lemma periodic_jobset_upto_implies_valid_job_of_task :
  forall T tasks offset jobs H j,
    periodic_jobset_upto T tasks offset jobs H j ->
    valid_job_of_task tasks jobs j.
Proof.
  intros T tasks offset jobs H j Hjobset.
  exact
    (generated_implies_valid_job_of_task
       tasks offset jobs j
       (periodic_jobset_upto_implies_generated T tasks offset jobs H j Hjobset)).
Qed.

(* The expected release of a job in the jobset is strictly below the horizon.
   Combines generated_job_release with periodic_jobset_upto_implies_release_lt. *)
Lemma periodic_jobset_upto_expected_release_lt :
  forall T tasks offset jobs H j,
    periodic_jobset_upto T tasks offset jobs H j ->
    expected_release tasks offset (job_task (jobs j)) (job_index (jobs j)) < H.
Proof.
  intros T tasks offset jobs H j Hjobset.
  rewrite <- generated_job_release.
  - exact (periodic_jobset_upto_implies_release_lt T tasks offset jobs H j Hjobset).
  - exact (periodic_jobset_upto_implies_generated T tasks offset jobs H j Hjobset).
Qed.

(* The job index of any in-scope job is strictly below the horizon.
   Requires that all in-scope tasks have positive period. *)
Lemma periodic_jobset_upto_implies_index_lt :
  forall T tasks offset jobs H j,
    well_formed_periodic_tasks_on T tasks ->
    periodic_jobset_upto T tasks offset jobs H j ->
    job_index (jobs j) < H.
Proof.
  intros T tasks offset jobs H j Hwf Hjobset.
  pose proof (periodic_jobset_upto_implies_task_in_scope T tasks offset jobs H j Hjobset) as HT.
  pose proof (Hwf _ HT) as Hp.
  pose proof (periodic_jobset_upto_expected_release_lt T tasks offset jobs H j Hjobset) as Hrel_lt.
  unfold expected_release in Hrel_lt.
  nia.
Qed.
