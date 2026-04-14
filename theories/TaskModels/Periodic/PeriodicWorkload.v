From Stdlib Require Import Arith Arith.PeanoNat Lia List.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Periodic.PeriodicFiniteHorizon.
From RocqSched Require Import Analysis.Common.WorkloadAggregation.
From RocqSched Require Import Analysis.Uniprocessor.RequestBound.

Import ListNotations.

(* ===== Period-aware count and workload bounds ===== *)

(* The number of jobs of task τ that can have release time < H is at most ⌈H/period⌉.
   This replaces the coarse bound H with a period-aware ceiling-division bound. *)
Definition periodic_jobs_of_task_upto_count
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (τ : TaskId)
    (H : Time) : nat :=
  (H + task_period (tasks τ) - 1) / task_period (tasks τ).

(* The total workload of task τ in horizon H is at most ⌈H/period⌉ × wcet.
   This equals periodic_rbf tasks τ H by definition. *)
Definition periodic_workload_upto
    (tasks : TaskId -> Task)
    (τ : TaskId)
    (H : Time) : nat :=
  periodic_jobs_of_task_upto_count (fun _ => True) tasks (fun _ => 0) τ H
  * task_cost (tasks τ).

(* periodic_workload_upto equals periodic_rbf. *)
Lemma periodic_workload_upto_eq_rbf :
  forall tasks τ H,
    periodic_workload_upto tasks τ H = periodic_rbf tasks τ H.
Proof.
  intros tasks τ H.
  unfold periodic_workload_upto, periodic_jobs_of_task_upto_count, periodic_rbf.
  reflexivity.
Qed.

(* ===== Count bound ===== *)

Lemma periodic_job_index_bound_upto :
  forall T tasks offset jobs H j,
    well_formed_periodic_tasks_on T tasks ->
    periodic_jobset_upto T tasks offset jobs H j ->
    job_index (jobs j) <
    periodic_jobs_of_task_upto_count
      T tasks offset (job_task (jobs j)) H.
Proof.
  intros T tasks offset jobs H j Hwf Hjobset.
  unfold periodic_jobs_of_task_upto_count.
  exact (periodic_jobset_upto_implies_index_lt_tight
           T tasks offset jobs H j Hwf Hjobset).
Qed.

Lemma periodic_jobs_of_task_upto_count_sound :
  forall T tasks offset jobs H τ l,
    well_formed_periodic_tasks_on T tasks ->
    NoDup (map (fun j => job_index (jobs j)) l) ->
    (forall j,
      In j l ->
      periodic_jobset_upto T tasks offset jobs H j /\
      job_task (jobs j) = τ) ->
    length l <= periodic_jobs_of_task_upto_count T tasks offset τ H.
Proof.
  intros T tasks offset jobs H τ l Hwf Hnodup_idx Hjobs.
  unfold periodic_jobs_of_task_upto_count.
  set (cnt := (H + task_period (tasks τ) - 1) / task_period (tasks τ)).
  pose (idx := fun j => job_index (jobs j)).
  assert (Hincl : incl (map idx l) (seq 0 cnt)).
  {
    intros k Hk.
    apply in_map_iff in Hk.
    destruct Hk as [j [Hidx Hj]].
    subst k.
    rewrite in_seq.
    split.
    - apply Nat.le_0_l.
    - destruct (Hjobs j Hj) as [Hjobset Htask].
      pose proof (periodic_jobset_upto_implies_index_lt_tight
                    T tasks offset jobs H j Hwf Hjobset) as Hlt.
      (* The tight bound is in terms of job_task (jobs j), rewrite via Htask *)
      rewrite Htask in Hlt.
      exact Hlt.
  }
  eapply Nat.le_trans.
  - replace (length l) with (length (map idx l)) by apply List.length_map.
    apply NoDup_incl_length with (l := map idx l) (l' := seq 0 cnt);
      try exact Hnodup_idx.
    exact Hincl.
  - rewrite length_seq. lia.
Qed.

(* ===== Workload bound ===== *)

Lemma periodic_workload_upto_bound :
  forall T tasks offset jobs H τ l,
    well_formed_periodic_tasks_on T tasks ->
    NoDup (map (fun j => job_index (jobs j)) l) ->
    (forall j,
      In j l ->
      periodic_jobset_upto T tasks offset jobs H j /\
      job_task (jobs j) = τ) ->
    total_job_cost jobs l <= periodic_workload_upto tasks τ H.
Proof.
  intros T tasks offset jobs H τ l Hwf Hnodup_idx Hjobs.
  unfold periodic_workload_upto.
  eapply Nat.le_trans.
  - eapply (total_job_cost_le_length_mul jobs l (task_cost (tasks τ))).
    intros j Hj.
    destruct (Hjobs j Hj) as [Hjobset Htask].
    rewrite <- Htask.
    eapply generated_job_cost_bounded.
    exact (periodic_jobset_upto_implies_generated T tasks offset jobs H j Hjobset).
  - unfold periodic_workload_upto.
    pose proof (periodic_jobs_of_task_upto_count_sound
                  T tasks offset jobs H τ l Hwf Hnodup_idx Hjobs) as Hcount.
    apply Nat.mul_le_mono_r.
    exact Hcount.
Qed.

(* ===== Bridge to RBF ===== *)

(* The workload in horizon H is bounded by the periodic RBF. *)
Lemma periodic_workload_le_rbf :
  forall T tasks offset jobs H τ l,
    well_formed_periodic_tasks_on T tasks ->
    NoDup (map (fun j => job_index (jobs j)) l) ->
    (forall j,
      In j l ->
      periodic_jobset_upto T tasks offset jobs H j /\
      job_task (jobs j) = τ) ->
    total_job_cost jobs l <= periodic_rbf tasks τ H.
Proof.
  intros T tasks offset jobs H τ l Hwf Hnodup_idx Hjobs.
  rewrite <- periodic_workload_upto_eq_rbf.
  exact (periodic_workload_upto_bound T tasks offset jobs H τ l
           Hwf Hnodup_idx Hjobs).
Qed.
