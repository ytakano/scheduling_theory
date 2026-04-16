From Stdlib Require Import Arith Arith.PeanoNat Lia List Bool Sorting.Permutation.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Periodic.PeriodicReleaseLemmas.
From RocqSched Require Import Analysis.Common.WorkloadAggregation.

Import ListNotations.

Definition periodic_jobset_deadline_between
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (t1 t2 : Time) : JobId -> Prop :=
  fun j =>
    T (job_task (jobs j)) /\
    generated_by_periodic_task tasks offset jobs j /\
    t1 <= job_release (jobs j) /\
    job_abs_deadline (jobs j) <= t2.

Definition periodic_index_in_window
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (τ : TaskId)
    (t1 t2 : Time)
    (k : nat) : bool :=
  Nat.leb t1 (expected_release tasks offset τ k)
  &&
  Nat.leb (expected_abs_deadline tasks offset τ k) t2.

Definition periodic_dbf_window
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (τ : TaskId)
    (t1 t2 : Time) : nat :=
  length
    (filter
       (periodic_index_in_window tasks offset τ t1 t2)
       (seq 0 (S t2)))
  * task_cost (tasks τ).

Fixpoint taskset_periodic_dbf_window
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (enumT : list TaskId)
    (t1 t2 : Time) : nat :=
  match enumT with
  | [] => 0
  | τ :: enumT' =>
      periodic_dbf_window tasks offset τ t1 t2 +
      taskset_periodic_dbf_window tasks offset enumT' t1 t2
  end.

Lemma periodic_jobset_deadline_between_implies_task_in_scope :
  forall T tasks offset jobs t1 t2 j,
    periodic_jobset_deadline_between T tasks offset jobs t1 t2 j ->
    T (job_task (jobs j)).
Proof.
  intros T tasks offset jobs t1 t2 j [HT _].
  exact HT.
Qed.

Lemma periodic_jobset_deadline_between_implies_generated :
  forall T tasks offset jobs t1 t2 j,
    periodic_jobset_deadline_between T tasks offset jobs t1 t2 j ->
    generated_by_periodic_task tasks offset jobs j.
Proof.
  intros T tasks offset jobs t1 t2 j [_ [Hgen _]].
  exact Hgen.
Qed.

Lemma periodic_jobset_deadline_between_implies_release_ge :
  forall T tasks offset jobs t1 t2 j,
    periodic_jobset_deadline_between T tasks offset jobs t1 t2 j ->
    t1 <= job_release (jobs j).
Proof.
  intros T tasks offset jobs t1 t2 j [_ [_ [Hrel _]]].
  exact Hrel.
Qed.

Lemma periodic_jobset_deadline_between_implies_deadline_le :
  forall T tasks offset jobs t1 t2 j,
    periodic_jobset_deadline_between T tasks offset jobs t1 t2 j ->
    job_abs_deadline (jobs j) <= t2.
Proof.
  intros T tasks offset jobs t1 t2 j [_ [_ [_ Hdl]]].
  exact Hdl.
Qed.

Lemma periodic_jobset_deadline_between_implies_valid :
  forall T tasks offset jobs t1 t2 j,
    periodic_jobset_deadline_between T tasks offset jobs t1 t2 j ->
    valid_job_of_task tasks jobs j.
Proof.
  intros T tasks offset jobs t1 t2 j Hjobset.
  exact (generated_implies_valid_job_of_task tasks offset jobs j
           (periodic_jobset_deadline_between_implies_generated
              T tasks offset jobs t1 t2 j Hjobset)).
Qed.

Lemma periodic_jobset_deadline_between_implies_release_eq_expected :
  forall T tasks offset jobs t1 t2 j,
    periodic_jobset_deadline_between T tasks offset jobs t1 t2 j ->
    job_release (jobs j) =
    expected_release tasks offset (job_task (jobs j)) (job_index (jobs j)).
Proof.
  intros T tasks offset jobs t1 t2 j Hjobset.
  exact (generated_job_release tasks offset jobs j
           (periodic_jobset_deadline_between_implies_generated
              T tasks offset jobs t1 t2 j Hjobset)).
Qed.

Lemma periodic_jobset_deadline_between_implies_deadline_eq_expected :
  forall T tasks offset jobs t1 t2 j,
    periodic_jobset_deadline_between T tasks offset jobs t1 t2 j ->
    job_abs_deadline (jobs j) =
    expected_abs_deadline tasks offset (job_task (jobs j)) (job_index (jobs j)).
Proof.
  intros T tasks offset jobs t1 t2 j Hjobset.
  destruct (periodic_jobset_deadline_between_implies_generated
              T tasks offset jobs t1 t2 j Hjobset) as [_ [Hdl _]].
  exact Hdl.
Qed.

Lemma periodic_jobset_deadline_between_same_task_same_release_implies_same_index :
  forall T tasks offset jobs t1 t2 j1 j2,
    well_formed_periodic_tasks_on T tasks ->
    periodic_jobset_deadline_between T tasks offset jobs t1 t2 j1 ->
    periodic_jobset_deadline_between T tasks offset jobs t1 t2 j2 ->
    job_task (jobs j1) = job_task (jobs j2) ->
    job_release (jobs j1) = job_release (jobs j2) ->
    job_index (jobs j1) = job_index (jobs j2).
Proof.
  intros T tasks offset jobs t1 t2 j1 j2 Hwf Hjob1 Hjob2 Htask Hrel.
  eapply generated_by_periodic_same_task_same_release_implies_same_index; eauto.
  - exact (periodic_jobset_deadline_between_implies_task_in_scope
             T tasks offset jobs t1 t2 j1 Hjob1).
  - exact (periodic_jobset_deadline_between_implies_generated
             T tasks offset jobs t1 t2 j1 Hjob1).
  - exact (periodic_jobset_deadline_between_implies_generated
             T tasks offset jobs t1 t2 j2 Hjob2).
Qed.

Lemma periodic_jobset_deadline_between_same_task_release_le_implies_index_le :
  forall T tasks offset jobs t1 t2 j1 j2,
    well_formed_periodic_tasks_on T tasks ->
    periodic_jobset_deadline_between T tasks offset jobs t1 t2 j1 ->
    periodic_jobset_deadline_between T tasks offset jobs t1 t2 j2 ->
    job_task (jobs j1) = job_task (jobs j2) ->
    job_release (jobs j1) <= job_release (jobs j2) ->
    job_index (jobs j1) <= job_index (jobs j2).
Proof.
  intros T tasks offset jobs t1 t2 j1 j2 Hwf Hjob1 Hjob2 Htask Hrel.
  eapply generated_by_periodic_same_task_release_le_implies_index_le; eauto.
  - exact (periodic_jobset_deadline_between_implies_task_in_scope
             T tasks offset jobs t1 t2 j1 Hjob1).
  - exact (periodic_jobset_deadline_between_implies_generated
             T tasks offset jobs t1 t2 j1 Hjob1).
  - exact (periodic_jobset_deadline_between_implies_generated
             T tasks offset jobs t1 t2 j2 Hjob2).
Qed.

Lemma periodic_jobset_deadline_between_implies_index_le_t2 :
  forall T tasks offset jobs t1 t2 j,
    well_formed_periodic_tasks_on T tasks ->
    periodic_jobset_deadline_between T tasks offset jobs t1 t2 j ->
    job_index (jobs j) <= t2.
Proof.
  intros T tasks offset jobs t1 t2 j Hwf Hjobset.
  pose proof (periodic_jobset_deadline_between_implies_task_in_scope
                T tasks offset jobs t1 t2 j Hjobset) as HT.
  pose proof (periodic_jobset_deadline_between_implies_generated
                T tasks offset jobs t1 t2 j Hjobset) as Hgen.
  pose proof (periodic_jobset_deadline_between_implies_deadline_le
                T tasks offset jobs t1 t2 j Hjobset) as Hdl.
  pose proof (generated_job_deadline tasks offset jobs j Hgen) as Hdl_eq.
  pose proof (generated_job_release tasks offset jobs j Hgen) as Hrel_eq.
  unfold expected_release in Hrel_eq.
  rewrite Hrel_eq in Hdl_eq.
  rewrite Hdl_eq in Hdl.
  specialize (Hwf (job_task (jobs j)) HT).
  nia.
Qed.

Lemma periodic_jobset_deadline_between_implies_index_in_window :
  forall T tasks offset jobs t1 t2 j,
    well_formed_periodic_tasks_on T tasks ->
    periodic_jobset_deadline_between T tasks offset jobs t1 t2 j ->
    In (job_index (jobs j))
       (filter
          (periodic_index_in_window tasks offset (job_task (jobs j)) t1 t2)
          (seq 0 (S t2))).
Proof.
  intros T tasks offset jobs t1 t2 j Hwf Hjobset.
  apply filter_In.
  split.
  - rewrite in_seq.
    split.
    + lia.
    + pose proof (periodic_jobset_deadline_between_implies_index_le_t2
                    T tasks offset jobs t1 t2 j Hwf Hjobset) as Hidx.
      lia.
  - unfold periodic_index_in_window.
    rewrite !andb_true_iff.
    rewrite !Nat.leb_le.
    split.
    + pose proof (periodic_jobset_deadline_between_implies_release_ge
                    T tasks offset jobs t1 t2 j Hjobset) as Hrel.
      rewrite <- (generated_job_release tasks offset jobs j
                    (periodic_jobset_deadline_between_implies_generated
                       T tasks offset jobs t1 t2 j Hjobset)).
      exact Hrel.
    + pose proof (periodic_jobset_deadline_between_implies_deadline_le
                    T tasks offset jobs t1 t2 j Hjobset) as Hdl.
      destruct (periodic_jobset_deadline_between_implies_generated
                  T tasks offset jobs t1 t2 j Hjobset) as [_ [Hdl_eq _]].
      unfold expected_abs_deadline.
      unfold expected_abs_deadline in Hdl_eq.
      rewrite <- Hdl_eq.
      exact Hdl.
Qed.

Lemma periodic_jobs_of_task_deadline_between_count_sound :
  forall T tasks offset jobs t1 t2 τ l,
    well_formed_periodic_tasks_on T tasks ->
    NoDup (map (fun j => job_index (jobs j)) l) ->
    (forall j,
      In j l ->
      periodic_jobset_deadline_between T tasks offset jobs t1 t2 j /\
      job_task (jobs j) = τ) ->
    length l <=
    length (filter (periodic_index_in_window tasks offset τ t1 t2) (seq 0 (S t2))).
Proof.
  intros T tasks offset jobs t1 t2 τ l Hwf Hnodup_idx Hjobs.
  set (idx := fun j => job_index (jobs j)).
  assert (Hincl :
    incl (map idx l)
         (filter (periodic_index_in_window tasks offset τ t1 t2) (seq 0 (S t2)))).
  {
    intros k Hk.
    apply in_map_iff in Hk.
    destruct Hk as [j [Hidx Hj]].
    subst k.
    destruct (Hjobs j Hj) as [Hjobset Htask].
    rewrite <- Htask.
    exact (periodic_jobset_deadline_between_implies_index_in_window
             T tasks offset jobs t1 t2 j Hwf Hjobset).
  }
  replace (length l) with (length (map idx l)) by apply List.length_map.
  eapply NoDup_incl_length; eauto.
Qed.

Lemma periodic_window_demand_le_dbf_window :
  forall T tasks offset jobs t1 t2 τ l,
    well_formed_periodic_tasks_on T tasks ->
    NoDup (map (fun j => job_index (jobs j)) l) ->
    (forall j,
      In j l ->
      periodic_jobset_deadline_between T tasks offset jobs t1 t2 j /\
      job_task (jobs j) = τ) ->
    total_job_cost jobs l <= periodic_dbf_window tasks offset τ t1 t2.
Proof.
  intros T tasks offset jobs t1 t2 τ l Hwf Hnodup_idx Hjobs.
  unfold periodic_dbf_window.
  eapply Nat.le_trans.
  - eapply (total_job_cost_le_length_mul jobs l (task_cost (tasks τ))).
    intros j Hj.
    destruct (Hjobs j Hj) as [Hjobset Htask].
    rewrite <- Htask.
    exact (generated_job_cost_bounded tasks offset jobs j
             (periodic_jobset_deadline_between_implies_generated
                T tasks offset jobs t1 t2 j Hjobset)).
  - apply Nat.mul_le_mono_r.
    eapply periodic_jobs_of_task_deadline_between_count_sound; eauto.
Qed.

Lemma periodic_filter_task_preserves_window_jobset :
  forall T tasks offset jobs t1 t2 τ l j,
    In j (filter (fun j => Nat.eqb (job_task (jobs j)) τ) l) ->
    periodic_jobset_deadline_between T tasks offset jobs t1 t2 j ->
    periodic_jobset_deadline_between T tasks offset jobs t1 t2 j /\
    job_task (jobs j) = τ.
Proof.
  intros T tasks offset jobs t1 t2 τ l j Hin Hjobset.
  apply filter_In in Hin.
  destruct Hin as [_ Heq].
  split; [exact Hjobset|].
  apply Nat.eqb_eq. exact Heq.
Qed.

Lemma periodic_filtered_indices_nodup_window :
  forall (jobs : JobId -> Job) τ l,
    NoDup (map (fun j => (job_task (jobs j), job_index (jobs j))) l) ->
    NoDup (map (fun j => job_index (jobs j))
      (filter (fun j => Nat.eqb (job_task (jobs j)) τ) l)).
Proof.
  intros jobs τ l Hnodup.
  induction l as [|j l IH]; simpl in *.
  - constructor.
  - inversion Hnodup as [|x l' Hnotin Hnodup']; subst.
    destruct (Nat.eqb (job_task (jobs j)) τ) eqn:Heq; simpl.
    + constructor.
      * intro Hin.
        apply in_map_iff in Hin.
        destruct Hin as [j' [Hidx Hin]].
        apply filter_In in Hin.
        destruct Hin as [Hin Heq'].
        apply Hnotin.
        apply in_map_iff.
        exists j'. split.
        -- apply Nat.eqb_eq in Heq.
           apply Nat.eqb_eq in Heq'.
           assert (Htask : job_task (jobs j') = job_task (jobs j)) by lia.
           rewrite Htask.
           rewrite Hidx.
           reflexivity.
        -- exact Hin.
      * exact (IH Hnodup').
    + exact (IH Hnodup').
Qed.

Lemma periodic_filtered_pairs_nodup_window :
  forall (jobs : JobId -> Job) (p : JobId -> bool) l,
    NoDup (map (fun j => (job_task (jobs j), job_index (jobs j))) l) ->
    NoDup (map (fun j => (job_task (jobs j), job_index (jobs j))) (filter p l)).
Proof.
  intros jobs p l Hnodup.
  induction l as [|j l IH]; simpl in *.
  - constructor.
  - inversion Hnodup as [|x l' Hnotin Hnodup']; subst.
    destruct (p j); simpl.
    + constructor.
      * intro Hin. apply Hnotin.
        apply in_map_iff in Hin.
        destruct Hin as [j' [Hp Hin]].
        apply in_map_iff.
        exists j'. split; [exact Hp|].
        apply filter_In in Hin.
        exact (proj1 Hin).
      * exact (IH Hnodup').
    + exact (IH Hnodup').
Qed.

Lemma taskset_periodic_dbf_window_app :
  forall tasks offset enumT1 enumT2 t1 t2,
    taskset_periodic_dbf_window tasks offset (enumT1 ++ enumT2) t1 t2 =
    taskset_periodic_dbf_window tasks offset enumT1 t1 t2 +
    taskset_periodic_dbf_window tasks offset enumT2 t1 t2.
Proof.
  intros tasks offset enumT1 enumT2 t1 t2.
  induction enumT1 as [|τ enumT1 IH]; simpl.
  - reflexivity.
  - rewrite IH. lia.
Qed.

Lemma taskset_periodic_dbf_window_perm :
  forall tasks offset enumT1 enumT2 t1 t2,
    Permutation enumT1 enumT2 ->
    taskset_periodic_dbf_window tasks offset enumT1 t1 t2 =
    taskset_periodic_dbf_window tasks offset enumT2 t1 t2.
Proof.
  intros tasks offset enumT1 enumT2 t1 t2 Hperm.
  induction Hperm; simpl; try lia.
Qed.

Lemma taskset_periodic_dbf_window_nodup_stable :
  forall tasks offset enumT1 enumT2 t1 t2,
    NoDup enumT1 ->
    NoDup enumT2 ->
    (forall τ, In τ enumT1 <-> In τ enumT2) ->
    taskset_periodic_dbf_window tasks offset enumT1 t1 t2 =
    taskset_periodic_dbf_window tasks offset enumT2 t1 t2.
Proof.
  intros tasks offset enumT1 enumT2 t1 t2 Hnd1 Hnd2 Hequiv.
  apply taskset_periodic_dbf_window_perm.
  eapply NoDup_Permutation; eauto.
Qed.

Lemma periodic_total_window_demand_le_taskset_dbf_window :
  forall T tasks offset jobs t1 t2 enumT l,
    well_formed_periodic_tasks_on T tasks ->
    NoDup enumT ->
    NoDup (map (fun j => (job_task (jobs j), job_index (jobs j))) l) ->
    (forall j,
      In j l ->
      periodic_jobset_deadline_between T tasks offset jobs t1 t2 j /\
      In (job_task (jobs j)) enumT) ->
    total_job_cost jobs l <= taskset_periodic_dbf_window tasks offset enumT t1 t2.
Proof.
  intros T tasks offset jobs t1 t2 enumT.
  induction enumT as [|τ enumT IH]; intros l Hwf HnodupT HnodupPairs Hjobs; simpl.
  - destruct l as [|j l'].
    + simpl. lia.
    + exfalso.
      destruct (Hjobs j (or_introl eq_refl)) as [_ Hin].
      simpl in Hin. tauto.
  - inversion HnodupT as [|? ? HnotinT HnodupT']; subst.
    pose (lτ := filter (fun j => Nat.eqb (job_task (jobs j)) τ) l).
    pose (lrest := filter (fun j => negb (Nat.eqb (job_task (jobs j)) τ)) l).
    rewrite (total_job_cost_filter_partition jobs
               (fun j => Nat.eqb (job_task (jobs j)) τ) l).
    apply Nat.add_le_mono.
    + eapply (periodic_window_demand_le_dbf_window T tasks offset jobs t1 t2 τ lτ).
      * exact Hwf.
      * eapply periodic_filtered_indices_nodup_window. exact HnodupPairs.
      * intros j Hj.
        eapply (periodic_filter_task_preserves_window_jobset
                  T tasks offset jobs t1 t2 τ l j); try exact Hj.
        apply filter_In in Hj.
        destruct Hj as [Hin _].
        exact (proj1 (Hjobs j Hin)).
    + eapply (IH lrest).
      * exact Hwf.
      * exact HnodupT'.
      * eapply periodic_filtered_pairs_nodup_window.
        exact HnodupPairs.
      * intros j Hj.
        apply filter_In in Hj.
        destruct Hj as [Hin Hneq].
        destruct (Hjobs j Hin) as [Hjobset HinT].
        split; [exact Hjobset|].
        simpl in HinT.
        destruct HinT as [Heq | HinT']; [|exact HinT'].
        exfalso.
        apply negb_true_iff in Hneq.
        apply Nat.eqb_neq in Hneq.
        subst. contradiction.
Qed.
