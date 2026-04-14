From Stdlib Require Import Arith Arith.PeanoNat Lia List.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Periodic.PeriodicFiniteHorizon.

Import ListNotations.

Fixpoint total_job_cost
    (jobs : JobId -> Job) (l : list JobId) : nat :=
  match l with
  | [] => 0
  | j :: l' => job_cost (jobs j) + total_job_cost jobs l'
  end.

Definition periodic_jobs_of_task_upto_count
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (τ : TaskId)
    (H : Time) : nat :=
  H.

Definition periodic_workload_upto
    (tasks : TaskId -> Task)
    (τ : TaskId)
    (H : Time) : nat :=
  H * task_cost (tasks τ).

Lemma total_job_cost_le_length_mul :
  forall jobs l c,
    (forall j, In j l -> job_cost (jobs j) <= c) ->
    total_job_cost jobs l <= length l * c.
Proof.
  intros jobs l c Hcost.
  induction l as [|j l IH]; simpl.
  - lia.
  - assert (Hhead : job_cost (jobs j) <= c).
    { apply Hcost. now left. }
    assert (Htail : forall j', In j' l -> job_cost (jobs j') <= c).
    { intros j' Hj'. apply Hcost. now right. }
    specialize (IH Htail).
    lia.
Qed.

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
  exact (periodic_jobset_upto_implies_index_lt T tasks offset jobs H j Hwf Hjobset).
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
  pose (idx := fun j => job_index (jobs j)).
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
      pose proof (periodic_job_index_bound_upto T tasks offset jobs H j Hwf Hjobset) as Hlt.
      exact Hlt.
  }
  eapply Nat.le_trans.
  - replace (length l) with (length (map idx l)) by apply List.length_map.
    apply NoDup_incl_length with (l := map idx l) (l' := seq 0 H); try exact Hnodup_idx.
    exact Hincl.
  - rewrite length_seq. lia.
Qed.

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
  - pose proof (periodic_jobs_of_task_upto_count_sound
                  T tasks offset jobs H τ l Hwf Hnodup_idx Hjobs) as Hcount.
    unfold periodic_jobs_of_task_upto_count in Hcount.
    nia.
Qed.
