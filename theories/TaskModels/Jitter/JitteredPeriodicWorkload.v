From Stdlib Require Import Arith Arith.PeanoNat Lia List.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Sporadic.SporadicTasks.
From RocqSched Require Import TaskModels.Sporadic.SporadicFiniteHorizon.
From RocqSched Require Import TaskModels.Sporadic.SporadicWorkload.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicTasks.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicFiniteHorizon.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicSporadicBridge.

Import ListNotations.

Lemma jittered_periodic_jobset_upto_implies_sporadic_jobset_upto :
  forall T tasks offset jitter jobs H j,
    jittered_periodic_jobset_upto T tasks offset jitter jobs H j ->
    sporadic_jobset_upto T tasks jobs H j.
Proof.
  intros T tasks offset jitter jobs H j [HT [Hgen Hrel]].
  split.
  - exact HT.
  - split.
    + exact (generated_by_jittered_periodic_implies_sporadic tasks offset jitter jobs j Hgen).
    + exact Hrel.
Qed.

Lemma jittered_periodic_job_count_upto_le_sporadic_bound :
  forall T tasks offset jitter jobs H τ l,
    well_formed_periodic_tasks_on T tasks ->
    NoDup l ->
    unique_task_index_on
      (jittered_periodic_jobset_upto T tasks offset jitter jobs H) jobs ->
    sporadic_separation_on
      (jittered_periodic_jobset_upto T tasks offset jitter jobs H) tasks jobs ->
    (forall j,
      In j l ->
      jittered_periodic_jobset_upto T tasks offset jitter jobs H j /\
      job_task (jobs j) = τ) ->
    length l <= sporadic_jobs_of_task_upto_bound T tasks τ H.
Proof.
  intros T tasks offset jitter jobs H τ l Hwf Hnodup Huniq _ Hjobs.
  unfold sporadic_jobs_of_task_upto_bound.
  pose (idx := fun j => job_index (jobs j)).
  assert (Hnodup_idx : NoDup (map idx l)).
  {
    eapply nodup_job_indices_of_unique_task_index; eauto.
  }
  assert (Hincl : incl (map idx l) (seq 0 H)).
  {
    intros k Hk.
    apply in_map_iff in Hk.
    destruct Hk as [j [Hidx Hj]].
    subst k.
    rewrite in_seq.
    split.
    - apply Nat.le_0_l.
    - destruct (Hjobs j Hj) as [Hjobset _].
      pose proof (jittered_periodic_jobset_upto_implies_sporadic_jobset_upto
                    T tasks offset jitter jobs H j Hjobset) as Hsp.
      pose proof (sporadic_jobset_upto_implies_index_lt T tasks jobs H j Hwf Hsp) as Hlt.
      exact Hlt.
  }
  eapply Nat.le_trans.
  - replace (length l) with (length (map idx l)) by apply List.length_map.
    apply NoDup_incl_length with (l := map idx l) (l' := seq 0 H); try exact Hnodup_idx.
    exact Hincl.
  - rewrite length_seq. lia.
Qed.

Lemma jittered_periodic_workload_upto_le_sporadic_bound :
  forall T tasks offset jitter jobs H τ l,
    well_formed_periodic_tasks_on T tasks ->
    NoDup l ->
    unique_task_index_on
      (jittered_periodic_jobset_upto T tasks offset jitter jobs H) jobs ->
    sporadic_separation_on
      (jittered_periodic_jobset_upto T tasks offset jitter jobs H) tasks jobs ->
    (forall j,
      In j l ->
      jittered_periodic_jobset_upto T tasks offset jitter jobs H j /\
      job_task (jobs j) = τ) ->
    total_job_cost jobs l <= sporadic_workload_upto_bound tasks τ H.
Proof.
  intros T tasks offset jitter jobs H τ l Hwf Hnodup Huniq Hsep Hjobs.
  unfold sporadic_workload_upto_bound.
  eapply Nat.le_trans.
  - eapply (total_job_cost_le_length_mul jobs l (task_cost (tasks τ))).
    intros j Hj.
    destruct (Hjobs j Hj) as [Hjobset Htask].
    rewrite <- Htask.
    exact (generated_jittered_job_cost_bounded
             tasks offset jitter jobs j
             (jittered_periodic_jobset_upto_implies_generated
                T tasks offset jitter jobs H j Hjobset)).
  - pose proof (jittered_periodic_job_count_upto_le_sporadic_bound
                  T tasks offset jitter jobs H τ l
                  Hwf Hnodup Huniq Hsep Hjobs) as Hcount.
    unfold sporadic_jobs_of_task_upto_bound in Hcount.
    nia.
Qed.
