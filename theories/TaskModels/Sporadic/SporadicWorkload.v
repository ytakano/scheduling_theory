From Stdlib Require Import Arith Arith.PeanoNat Lia List.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Sporadic.SporadicTasks.
From RocqSched Require Import TaskModels.Sporadic.SporadicFiniteHorizon.

Import ListNotations.

Fixpoint total_job_cost
    (jobs : JobId -> Job) (l : list JobId) : nat :=
  match l with
  | [] => 0
  | j :: l' => job_cost (jobs j) + total_job_cost jobs l'
  end.

Definition sporadic_jobs_of_task_upto_bound
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (τ : TaskId)
    (H : Time) : nat :=
  H.

Definition sporadic_workload_upto_bound
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

Lemma nodup_job_indices_of_unique_task_index :
  forall J jobs τ l,
    NoDup l ->
    unique_task_index_on J jobs ->
    (forall j, In j l -> J j /\ job_task (jobs j) = τ) ->
    NoDup (map (fun j => job_index (jobs j)) l).
Proof.
  intros J jobs τ l Hnodup Huniq Hjobs.
  induction Hnodup as [|j l Hnotin Hnodup IH]; simpl.
  - constructor.
  - constructor.
    + intro Hin.
      apply in_map_iff in Hin.
      destruct Hin as [j' [Hidx Hj']].
      destruct (Hjobs j (or_introl eq_refl)) as [HjJ Hjtask].
      destruct (Hjobs j' (or_intror Hj')) as [Hj'J Hj'task].
      assert (j = j').
      { eapply Huniq.
        - exact HjJ.
        - exact Hj'J.
        - rewrite Hjtask, Hj'task. reflexivity.
        - symmetry. exact Hidx. }
      subst j'. contradiction.
    + apply IH.
      intros j' Hj'.
      exact (Hjobs j' (or_intror Hj')).
Qed.

Lemma sporadic_index_bound_from_separation :
  forall T tasks jobs H j,
    well_formed_periodic_tasks_on T tasks ->
    sporadic_separation_on (sporadic_jobset_upto T tasks jobs H) tasks jobs ->
    sporadic_jobset_upto T tasks jobs H j ->
    job_index (jobs j) <
    sporadic_jobs_of_task_upto_bound
      T tasks (job_task (jobs j)) H.
Proof.
  intros T tasks jobs H j Hwf _ Hjobset.
  unfold sporadic_jobs_of_task_upto_bound.
  exact (sporadic_jobset_upto_implies_index_lt T tasks jobs H j Hwf Hjobset).
Qed.

Lemma sporadic_job_count_upto_le :
  forall T tasks jobs H τ l,
    well_formed_periodic_tasks_on T tasks ->
    NoDup l ->
    unique_task_index_on (sporadic_jobset_upto T tasks jobs H) jobs ->
    sporadic_separation_on (sporadic_jobset_upto T tasks jobs H) tasks jobs ->
    (forall j,
      In j l ->
      sporadic_jobset_upto T tasks jobs H j /\
      job_task (jobs j) = τ) ->
    length l <= sporadic_jobs_of_task_upto_bound T tasks τ H.
Proof.
  intros T tasks jobs H τ l Hwf Hnodup Huniq Hsep Hjobs.
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
      pose proof (sporadic_index_bound_from_separation
                    T tasks jobs H j Hwf Hsep Hjobset) as Hlt.
      exact Hlt.
  }
  eapply Nat.le_trans.
  - replace (length l) with (length (map idx l)) by apply List.length_map.
    apply NoDup_incl_length with (l := map idx l) (l' := seq 0 H); try exact Hnodup_idx.
    exact Hincl.
  - rewrite length_seq. lia.
Qed.

Lemma sporadic_workload_upto_le :
  forall T tasks jobs H τ l,
    well_formed_periodic_tasks_on T tasks ->
    NoDup l ->
    unique_task_index_on (sporadic_jobset_upto T tasks jobs H) jobs ->
    sporadic_separation_on (sporadic_jobset_upto T tasks jobs H) tasks jobs ->
    (forall j,
      In j l ->
      sporadic_jobset_upto T tasks jobs H j /\
      job_task (jobs j) = τ) ->
    total_job_cost jobs l <= sporadic_workload_upto_bound tasks τ H.
Proof.
  intros T tasks jobs H τ l Hwf Hnodup Huniq Hsep Hjobs.
  unfold sporadic_workload_upto_bound.
  eapply Nat.le_trans.
  - eapply (total_job_cost_le_length_mul jobs l (task_cost (tasks τ))).
    intros j Hj.
    destruct (Hjobs j Hj) as [Hjobset Htask].
    pose proof (generated_sporadic_implies_valid_job_of_task
                  tasks jobs j
                  (sporadic_jobset_upto_implies_generated T tasks jobs H j Hjobset))
      as Hvalid.
    rewrite <- Htask.
    exact (proj2 Hvalid).
  - pose proof (sporadic_job_count_upto_le
                  T tasks jobs H τ l Hwf Hnodup Huniq Hsep Hjobs) as Hcount.
    unfold sporadic_jobs_of_task_upto_bound in Hcount.
    nia.
Qed.
