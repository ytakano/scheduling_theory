From Stdlib Require Import Arith Arith.PeanoNat Lia Bool.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Periodic.PeriodicReleaseLemmas.
From RocqSched Require Import TaskModels.Sporadic.SporadicTasks.

(* ===== Periodic-to-Sporadic Bridge ===== *)

(* A periodically generated job satisfies the sporadic generation predicate.
   Key argument: offset(τ) >= 0 (since Time = nat), so
     job_release j = offset(τ) + k * period(τ) >= k * period(τ)
                   = earliest_sporadic_release tasks τ k. *)
Lemma generated_by_periodic_implies_sporadic :
  forall tasks offset jobs j,
    generated_by_periodic_task tasks offset jobs j ->
    generated_by_sporadic_task tasks jobs j.
Proof.
  intros tasks offset jobs j Hgen.
  split.
  - destruct Hgen as [Hrel _].
    unfold earliest_sporadic_release, expected_release in *.
    lia.
  - exact (generated_implies_valid_job_of_task tasks offset jobs j Hgen).
Qed.

(* For a periodic job model, the sporadic separation constraint holds exactly.
   Proof: release(j2) = offset + k2 * p = offset + k1 * p + (k2 - k1) * p
          = release(j1) + (k2 - k1) * p, which equals the lower bound required. *)
Lemma periodic_model_satisfies_separation :
  forall J tasks offset jobs,
    periodic_job_model_on J tasks offset jobs ->
    sporadic_separation_on J tasks jobs.
Proof.
  intros J tasks offset jobs Hperiodic.
  unfold sporadic_separation_on.
  intros j1 j2 Hj1 Hj2 Htask Hidx.
  destruct (Hperiodic j1 Hj1) as [Hrel1 _].
  destruct (Hperiodic j2 Hj2) as [Hrel2 _].
  unfold expected_release in *.
  rewrite Htask in Hrel1 |- *.
  rewrite Hrel1, Hrel2.
  nia.
Qed.

Lemma periodic_model_same_task_same_release_implies_same_index :
  forall J T tasks offset jobs j1 j2,
    well_formed_periodic_tasks_on T tasks ->
    (forall j, J j -> T (job_task (jobs j))) ->
    periodic_job_model_on J tasks offset jobs ->
    J j1 ->
    J j2 ->
    job_task (jobs j1) = job_task (jobs j2) ->
    job_release (jobs j1) = job_release (jobs j2) ->
    job_index (jobs j1) = job_index (jobs j2).
Proof.
  intros J T tasks offset jobs j1 j2 Hwf Hscope Hperiodic Hj1 Hj2 Htask Hrel.
  eapply generated_by_periodic_same_task_same_release_implies_same_index; eauto.
Qed.

(* Complete bridge: periodic_job_model_on + task scope + uniqueness => sporadic_job_model_on.
   Note: uniqueness (unique_task_index_on) must be supplied explicitly, as
   periodic_job_model_on only constrains generation per job, not across jobs. *)
Theorem periodic_model_implies_sporadic_model :
  forall J T tasks offset jobs,
    (forall j, J j -> T (job_task (jobs j))) ->
    periodic_job_model_on J tasks offset jobs ->
    unique_task_index_on J jobs ->
    sporadic_job_model_on J T tasks jobs.
Proof.
  intros J T tasks offset jobs Hscope Hperiodic Huniq.
  split. { exact Hscope. }
  split.
  { intros j Hj.
    exact (generated_by_periodic_implies_sporadic tasks offset jobs j (Hperiodic j Hj)). }
  split. { exact Huniq. }
  exact (periodic_model_satisfies_separation J tasks offset jobs Hperiodic).
Qed.
