From Stdlib Require Import Arith Arith.PeanoNat Lia Bool.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Periodic.PeriodicFiniteHorizon.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicTasks.

Definition jittered_periodic_jobset_upto
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jitter : TaskId -> Time)
    (jobs : JobId -> Job)
    (H : Time) : JobId -> Prop :=
  fun j =>
    T (job_task (jobs j)) /\
    generated_by_jittered_periodic_task tasks offset jitter jobs j /\
    job_release (jobs j) < H.

Definition jittered_periodic_jobset_upto_bool
    (T_bool : TaskId -> bool)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jitter : TaskId -> Time)
    (jobs : JobId -> Job)
    (H : Time) : JobId -> bool :=
  fun j =>
    T_bool (job_task (jobs j))
    &&
    generated_by_jittered_periodic_task_b tasks offset jitter jobs j
    &&
    Nat.ltb (job_release (jobs j)) H.

Lemma jittered_periodic_jobset_upto_bool_spec :
  forall T T_bool tasks offset jitter jobs H,
    (forall τ, T_bool τ = true <-> T τ) ->
    forall j,
      jittered_periodic_jobset_upto_bool T_bool tasks offset jitter jobs H j = true <->
      jittered_periodic_jobset_upto T tasks offset jitter jobs H j.
Proof.
  intros T T_bool tasks offset jitter jobs H HT j.
  unfold jittered_periodic_jobset_upto_bool, jittered_periodic_jobset_upto.
  rewrite !andb_true_iff.
  rewrite generated_by_jittered_periodic_task_b_spec.
  rewrite Nat.ltb_lt.
  rewrite HT.
  tauto.
Qed.

Lemma jittered_periodic_jobset_upto_implies_generated :
  forall T tasks offset jitter jobs H j,
    jittered_periodic_jobset_upto T tasks offset jitter jobs H j ->
    generated_by_jittered_periodic_task tasks offset jitter jobs j.
Proof.
  intros T tasks offset jitter jobs H j [_ [Hgen _]].
  exact Hgen.
Qed.

Lemma jittered_periodic_jobset_upto_implies_task_in_scope :
  forall T tasks offset jitter jobs H j,
    jittered_periodic_jobset_upto T tasks offset jitter jobs H j ->
    T (job_task (jobs j)).
Proof.
  intros T tasks offset jitter jobs H j [HT _].
  exact HT.
Qed.

Lemma jittered_periodic_jobset_upto_implies_release_lt :
  forall T tasks offset jitter jobs H j,
    jittered_periodic_jobset_upto T tasks offset jitter jobs H j ->
    job_release (jobs j) < H.
Proof.
  intros T tasks offset jitter jobs H j [_ [_ Hrel]].
  exact Hrel.
Qed.

Lemma jittered_periodic_jobset_upto_implies_valid_job_of_task :
  forall T tasks offset jitter jobs H j,
    jittered_periodic_jobset_upto T tasks offset jitter jobs H j ->
    valid_job_of_task tasks jobs j.
Proof.
  intros T tasks offset jitter jobs H j Hjobset.
  exact (generated_jittered_implies_valid_job_of_task tasks offset jitter jobs j
    (jittered_periodic_jobset_upto_implies_generated
       T tasks offset jitter jobs H j Hjobset)).
Qed.

Lemma jittered_periodic_jobset_upto_expected_release_lt :
  forall T tasks offset jitter jobs H j,
    jittered_periodic_jobset_upto T tasks offset jitter jobs H j ->
    expected_release tasks offset (job_task (jobs j)) (job_index (jobs j)) < H.
Proof.
  intros T tasks offset jitter jobs H j Hjobset.
  pose proof (generated_jittered_job_release_lb tasks offset jitter jobs j
    (jittered_periodic_jobset_upto_implies_generated
       T tasks offset jitter jobs H j Hjobset)) as Hlb.
  pose proof (jittered_periodic_jobset_upto_implies_release_lt
    T tasks offset jitter jobs H j Hjobset) as Hlt.
  lia.
Qed.

Lemma jittered_periodic_jobset_upto_implies_index_lt :
  forall T tasks offset jitter jobs H j,
    well_formed_periodic_tasks_on T tasks ->
    jittered_periodic_jobset_upto T tasks offset jitter jobs H j ->
    job_index (jobs j) < H.
Proof.
  intros T tasks offset jitter jobs H j Hwf Hjobset.
  pose proof (jittered_periodic_jobset_upto_expected_release_lt
    T tasks offset jitter jobs H j Hjobset) as Hrel_lt.
  pose proof (jittered_periodic_jobset_upto_implies_task_in_scope
    T tasks offset jitter jobs H j Hjobset) as HT.
  eapply expected_release_lt_horizon_implies_index_lt; eauto.
Qed.
