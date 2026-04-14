From Stdlib Require Import Arith Arith.PeanoNat Lia Bool.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Sporadic.SporadicTasks.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicTasks.

Lemma generated_by_jittered_periodic_implies_sporadic :
  forall tasks offset jitter jobs j,
    generated_by_jittered_periodic_task tasks offset jitter jobs j ->
    generated_by_sporadic_task tasks jobs j.
Proof.
  intros tasks offset jitter jobs j Hgen.
  split.
  - pose proof (generated_jittered_job_release_lb tasks offset jitter jobs j Hgen) as Hlb.
    unfold earliest_sporadic_release, expected_release.
    eapply Nat.le_trans.
    + apply Nat.le_add_l.
    + exact Hlb.
  - exact (generated_jittered_implies_valid_job_of_task tasks offset jitter jobs j Hgen).
Qed.

Theorem jittered_periodic_model_implies_sporadic_model :
  forall J T tasks offset jitter jobs,
    (forall j, J j -> T (job_task (jobs j))) ->
    jittered_periodic_job_model_on J tasks offset jitter jobs ->
    unique_task_index_on J jobs ->
    sporadic_separation_on J tasks jobs ->
    sporadic_job_model_on J T tasks jobs.
Proof.
  intros J T tasks offset jitter jobs Hscope Hmodel Huniq Hsep.
  split. { exact Hscope. }
  split.
  - intros j Hj.
    exact (generated_by_jittered_periodic_implies_sporadic tasks offset jitter jobs j
      (Hmodel j Hj)).
  - split; assumption.
Qed.
