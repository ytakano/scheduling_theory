From Stdlib Require Import Arith Arith.PeanoNat Lia List Bool Sorting.Permutation.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Periodic.PeriodicReleaseLemmas.
From RocqSched Require Import TaskModels.Periodic.PeriodicWindowDemandBound.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicTasks.
From RocqSched Require Import Analysis.Common.WorkloadAggregation.

Import ListNotations.

Definition jittered_periodic_jobset_deadline_between
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jitter : TaskId -> Time)
    (jobs : JobId -> Job)
    (t1 t2 : Time) : JobId -> Prop :=
  fun j =>
    T (job_task (jobs j)) /\
    generated_by_jittered_periodic_task tasks offset jitter jobs j /\
    t1 <= job_release (jobs j) /\
    job_abs_deadline (jobs j) <= t2.

Definition jittered_index_may_be_in_window
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jitter : TaskId -> Time)
    (τ : TaskId)
    (t1 t2 : Time)
    (k : nat) : Prop :=
  let nominal := expected_release tasks offset τ k in
  let latest := nominal + jitter τ in
  let deadline_release_latest := t2 - task_relative_deadline (tasks τ) in
  task_relative_deadline (tasks τ) <= t2 /\
  Nat.max t1 nominal <= Nat.min deadline_release_latest latest.

Definition jittered_index_may_be_in_window_b
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jitter : TaskId -> Time)
    (τ : TaskId)
    (t1 t2 : Time)
    (k : nat) : bool :=
  Nat.leb (task_relative_deadline (tasks τ)) t2
  &&
  Nat.leb
    (Nat.max t1 (expected_release tasks offset τ k))
    (Nat.min
       (t2 - task_relative_deadline (tasks τ))
       (expected_release tasks offset τ k + jitter τ)).

Definition jittered_periodic_dbf_window
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jitter : TaskId -> Time)
    (τ : TaskId)
    (t1 t2 : Time) : nat :=
  length
    (filter
       (jittered_index_may_be_in_window_b tasks offset jitter τ t1 t2)
       (seq 0 (S t2)))
  * task_cost (tasks τ).

Fixpoint taskset_jittered_periodic_dbf_window
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jitter : TaskId -> Time)
    (enumT : list TaskId)
    (t1 t2 : Time) : nat :=
  match enumT with
  | [] => 0
  | τ :: enumT' =>
      jittered_periodic_dbf_window tasks offset jitter τ t1 t2 +
      taskset_jittered_periodic_dbf_window tasks offset jitter enumT' t1 t2
  end.

Lemma jittered_periodic_jobset_deadline_between_implies_task_in_scope :
  forall T tasks offset jitter jobs t1 t2 j,
    jittered_periodic_jobset_deadline_between T tasks offset jitter jobs t1 t2 j ->
    T (job_task (jobs j)).
Proof.
  intros T tasks offset jitter jobs t1 t2 j [HT _].
  exact HT.
Qed.

Lemma jittered_periodic_jobset_deadline_between_implies_generated :
  forall T tasks offset jitter jobs t1 t2 j,
    jittered_periodic_jobset_deadline_between T tasks offset jitter jobs t1 t2 j ->
    generated_by_jittered_periodic_task tasks offset jitter jobs j.
Proof.
  intros T tasks offset jitter jobs t1 t2 j [_ [Hgen _]].
  exact Hgen.
Qed.

Lemma jittered_periodic_jobset_deadline_between_implies_release_ge :
  forall T tasks offset jitter jobs t1 t2 j,
    jittered_periodic_jobset_deadline_between T tasks offset jitter jobs t1 t2 j ->
    t1 <= job_release (jobs j).
Proof.
  intros T tasks offset jitter jobs t1 t2 j [_ [_ [Hrel _]]].
  exact Hrel.
Qed.

Lemma jittered_periodic_jobset_deadline_between_implies_deadline_le :
  forall T tasks offset jitter jobs t1 t2 j,
    jittered_periodic_jobset_deadline_between T tasks offset jitter jobs t1 t2 j ->
    job_abs_deadline (jobs j) <= t2.
Proof.
  intros T tasks offset jitter jobs t1 t2 j [_ [_ [_ Hdl]]].
  exact Hdl.
Qed.

Lemma jittered_periodic_jobset_deadline_between_implies_valid :
  forall T tasks offset jitter jobs t1 t2 j,
    jittered_periodic_jobset_deadline_between T tasks offset jitter jobs t1 t2 j ->
    valid_job_of_task tasks jobs j.
Proof.
  intros T tasks offset jitter jobs t1 t2 j Hjobset.
  exact (generated_jittered_implies_valid_job_of_task tasks offset jitter jobs j
           (jittered_periodic_jobset_deadline_between_implies_generated
              T tasks offset jitter jobs t1 t2 j Hjobset)).
Qed.

Lemma jittered_index_may_be_in_window_b_spec :
  forall tasks offset jitter τ t1 t2 k,
    jittered_index_may_be_in_window_b tasks offset jitter τ t1 t2 k = true <->
    jittered_index_may_be_in_window tasks offset jitter τ t1 t2 k.
Proof.
  intros tasks offset jitter τ t1 t2 k.
  unfold jittered_index_may_be_in_window_b,
         jittered_index_may_be_in_window.
  rewrite andb_true_iff, !Nat.leb_le.
  tauto.
Qed.

Lemma jittered_periodic_jobset_deadline_between_implies_index_may_be_in_window :
  forall T tasks offset jitter jobs t1 t2 j,
    jittered_periodic_jobset_deadline_between T tasks offset jitter jobs t1 t2 j ->
    jittered_index_may_be_in_window
      tasks offset jitter (job_task (jobs j)) t1 t2 (job_index (jobs j)).
Proof.
  intros T tasks offset jitter jobs t1 t2 j Hjobset.
  pose proof (jittered_periodic_jobset_deadline_between_implies_generated
                T tasks offset jitter jobs t1 t2 j Hjobset) as Hgen.
  pose proof (generated_by_jittered_periodic_release_lb
                tasks offset jitter jobs j Hgen) as Hlb.
  pose proof (generated_by_jittered_periodic_release_ub
                tasks offset jitter jobs j Hgen) as Hub.
  pose proof (generated_by_jittered_periodic_deadline_eq
                tasks offset jitter jobs j Hgen) as Hdl_eq.
  pose proof (jittered_periodic_jobset_deadline_between_implies_release_ge
                T tasks offset jitter jobs t1 t2 j Hjobset) as Hrel.
  pose proof (jittered_periodic_jobset_deadline_between_implies_deadline_le
                T tasks offset jitter jobs t1 t2 j Hjobset) as Hdl.
  unfold jittered_index_may_be_in_window.
  rewrite Hdl_eq in Hdl.
  split.
  - lia.
  - apply Nat.min_glb.
    + apply Nat.max_lub; lia.
    + apply Nat.max_lub; lia.
Qed.

Lemma jittered_periodic_jobset_deadline_between_implies_index_le_t2 :
  forall T tasks offset jitter jobs t1 t2 j,
    well_formed_periodic_tasks_on T tasks ->
    jittered_periodic_jobset_deadline_between T tasks offset jitter jobs t1 t2 j ->
    job_index (jobs j) <= t2.
Proof.
  intros T tasks offset jitter jobs t1 t2 j Hwf Hjobset.
  pose proof (jittered_periodic_jobset_deadline_between_implies_task_in_scope
                T tasks offset jitter jobs t1 t2 j Hjobset) as HT.
  pose proof (jittered_periodic_jobset_deadline_between_implies_generated
                T tasks offset jitter jobs t1 t2 j Hjobset) as Hgen.
  pose proof (generated_by_jittered_periodic_release_lb
                tasks offset jitter jobs j Hgen) as Hlb.
  pose proof (jittered_periodic_jobset_deadline_between_implies_deadline_le
                T tasks offset jitter jobs t1 t2 j Hjobset) as Hdl.
  pose proof (generated_by_jittered_periodic_deadline_eq
                tasks offset jitter jobs j Hgen) as Hdl_eq.
  rewrite Hdl_eq in Hdl.
  specialize (Hwf (job_task (jobs j)) HT).
  unfold expected_release in Hlb.
  nia.
Qed.

Lemma jittered_periodic_jobset_deadline_between_implies_index_in_window :
  forall T tasks offset jitter jobs t1 t2 j,
    well_formed_periodic_tasks_on T tasks ->
    jittered_periodic_jobset_deadline_between T tasks offset jitter jobs t1 t2 j ->
    In (job_index (jobs j))
       (filter
          (jittered_index_may_be_in_window_b
             tasks offset jitter (job_task (jobs j)) t1 t2)
          (seq 0 (S t2))).
Proof.
  intros T tasks offset jitter jobs t1 t2 j Hwf Hjobset.
  apply filter_In.
  split.
  - rewrite in_seq.
    split.
    + lia.
    + pose proof (jittered_periodic_jobset_deadline_between_implies_index_le_t2
                    T tasks offset jitter jobs t1 t2 j Hwf Hjobset) as Hidx.
      lia.
  - apply jittered_index_may_be_in_window_b_spec.
    exact (jittered_periodic_jobset_deadline_between_implies_index_may_be_in_window
             T tasks offset jitter jobs t1 t2 j Hjobset).
Qed.

Lemma jittered_periodic_jobs_of_task_deadline_between_count_sound :
  forall T tasks offset jitter jobs t1 t2 τ l,
    well_formed_periodic_tasks_on T tasks ->
    NoDup (map (fun j => job_index (jobs j)) l) ->
    (forall j,
      In j l ->
      jittered_periodic_jobset_deadline_between T tasks offset jitter jobs t1 t2 j /\
      job_task (jobs j) = τ) ->
    length l <=
    length
      (filter
         (jittered_index_may_be_in_window_b tasks offset jitter τ t1 t2)
         (seq 0 (S t2))).
Proof.
  intros T tasks offset jitter jobs t1 t2 τ l Hwf Hnodup_idx Hjobs.
  set (idx := fun j => job_index (jobs j)).
  assert (Hincl :
    incl (map idx l)
         (filter
            (jittered_index_may_be_in_window_b tasks offset jitter τ t1 t2)
            (seq 0 (S t2)))).
  {
    intros k Hk.
    apply in_map_iff in Hk.
    destruct Hk as [j [Hidx Hj]].
    subst k.
    destruct (Hjobs j Hj) as [Hjobset Htask].
    rewrite <- Htask.
    exact (jittered_periodic_jobset_deadline_between_implies_index_in_window
             T tasks offset jitter jobs t1 t2 j Hwf Hjobset).
  }
  replace (length l) with (length (map idx l)) by apply List.length_map.
  eapply NoDup_incl_length; eauto.
Qed.

Lemma jittered_periodic_window_demand_le_dbf_window :
  forall T tasks offset jitter jobs t1 t2 τ l,
    well_formed_periodic_tasks_on T tasks ->
    NoDup (map (fun j => job_index (jobs j)) l) ->
    (forall j,
      In j l ->
      jittered_periodic_jobset_deadline_between T tasks offset jitter jobs t1 t2 j /\
      job_task (jobs j) = τ) ->
    total_job_cost jobs l <= jittered_periodic_dbf_window tasks offset jitter τ t1 t2.
Proof.
  intros T tasks offset jitter jobs t1 t2 τ l Hwf Hnodup_idx Hjobs.
  unfold jittered_periodic_dbf_window.
  eapply Nat.le_trans.
  - eapply (total_job_cost_le_length_mul jobs l (task_cost (tasks τ))).
    intros j Hj.
    destruct (Hjobs j Hj) as [Hjobset Htask].
    rewrite <- Htask.
    exact (generated_by_jittered_periodic_cost_le tasks offset jitter jobs j
             (jittered_periodic_jobset_deadline_between_implies_generated
                T tasks offset jitter jobs t1 t2 j Hjobset)).
  - apply Nat.mul_le_mono_r.
    eapply jittered_periodic_jobs_of_task_deadline_between_count_sound; eauto.
Qed.

Lemma jittered_periodic_filter_task_preserves_window_jobset :
  forall T tasks offset jitter jobs t1 t2 τ l j,
    In j (filter (fun j => Nat.eqb (job_task (jobs j)) τ) l) ->
    jittered_periodic_jobset_deadline_between T tasks offset jitter jobs t1 t2 j ->
    jittered_periodic_jobset_deadline_between T tasks offset jitter jobs t1 t2 j /\
    job_task (jobs j) = τ.
Proof.
  intros T tasks offset jitter jobs t1 t2 τ l j Hin Hjobset.
  apply filter_In in Hin.
  destruct Hin as [_ Heq].
  split; [exact Hjobset|].
  apply Nat.eqb_eq. exact Heq.
Qed.

Lemma jittered_periodic_filtered_indices_nodup_window :
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

Lemma jittered_periodic_filtered_pairs_nodup_window :
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

Lemma taskset_jittered_periodic_dbf_window_app :
  forall tasks offset jitter enumT1 enumT2 t1 t2,
    taskset_jittered_periodic_dbf_window tasks offset jitter (enumT1 ++ enumT2) t1 t2 =
    taskset_jittered_periodic_dbf_window tasks offset jitter enumT1 t1 t2 +
    taskset_jittered_periodic_dbf_window tasks offset jitter enumT2 t1 t2.
Proof.
  intros tasks offset jitter enumT1 enumT2 t1 t2.
  induction enumT1 as [|τ enumT1 IH]; simpl.
  - reflexivity.
  - rewrite IH. lia.
Qed.

Lemma taskset_jittered_periodic_dbf_window_perm :
  forall tasks offset jitter enumT1 enumT2 t1 t2,
    Permutation enumT1 enumT2 ->
    taskset_jittered_periodic_dbf_window tasks offset jitter enumT1 t1 t2 =
    taskset_jittered_periodic_dbf_window tasks offset jitter enumT2 t1 t2.
Proof.
  intros tasks offset jitter enumT1 enumT2 t1 t2 Hperm.
  induction Hperm; simpl; try lia.
Qed.

Lemma taskset_jittered_periodic_dbf_window_nodup_stable :
  forall tasks offset jitter enumT1 enumT2 t1 t2,
    NoDup enumT1 ->
    NoDup enumT2 ->
    (forall τ, In τ enumT1 <-> In τ enumT2) ->
    taskset_jittered_periodic_dbf_window tasks offset jitter enumT1 t1 t2 =
    taskset_jittered_periodic_dbf_window tasks offset jitter enumT2 t1 t2.
Proof.
  intros tasks offset jitter enumT1 enumT2 t1 t2 Hnd1 Hnd2 Hequiv.
  apply taskset_jittered_periodic_dbf_window_perm.
  eapply NoDup_Permutation; eauto.
Qed.

Lemma jittered_periodic_total_window_demand_le_taskset_dbf_window :
  forall T tasks offset jitter jobs t1 t2 enumT l,
    well_formed_periodic_tasks_on T tasks ->
    NoDup enumT ->
    NoDup (map (fun j => (job_task (jobs j), job_index (jobs j))) l) ->
    (forall j,
      In j l ->
      jittered_periodic_jobset_deadline_between T tasks offset jitter jobs t1 t2 j /\
      In (job_task (jobs j)) enumT) ->
    total_job_cost jobs l <=
    taskset_jittered_periodic_dbf_window tasks offset jitter enumT t1 t2.
Proof.
  intros T tasks offset jitter jobs t1 t2 enumT.
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
    + eapply (jittered_periodic_window_demand_le_dbf_window
                T tasks offset jitter jobs t1 t2 τ lτ).
      * exact Hwf.
      * eapply jittered_periodic_filtered_indices_nodup_window. exact HnodupPairs.
      * intros j Hj.
        eapply (jittered_periodic_filter_task_preserves_window_jobset
                  T tasks offset jitter jobs t1 t2 τ l j); try exact Hj.
        apply filter_In in Hj.
        destruct Hj as [Hin _].
        exact (proj1 (Hjobs j Hin)).
    + eapply (IH lrest).
      * exact Hwf.
      * exact HnodupT'.
      * eapply jittered_periodic_filtered_pairs_nodup_window.
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

Lemma jittered_index_may_be_in_window_zero_jitter_iff_periodic :
  forall tasks offset τ t1 t2 k,
    jittered_index_may_be_in_window tasks offset (fun _ => 0) τ t1 t2 k <->
    periodic_index_in_window tasks offset τ t1 t2 k = true.
Proof.
  intros tasks offset τ t1 t2 k.
  unfold jittered_index_may_be_in_window, periodic_index_in_window.
  rewrite andb_true_iff, !Nat.leb_le.
  split.
  - intros [Hdl Hwin].
    split.
    + lia.
    + unfold expected_abs_deadline.
      lia.
  - intros [Hrel Hdl].
    split.
    + unfold expected_abs_deadline in Hdl. lia.
    + unfold expected_abs_deadline in Hdl. lia.
Qed.

Lemma jittered_index_may_be_in_window_b_zero_jitter_eq_periodic :
  forall tasks offset τ t1 t2 k,
    jittered_index_may_be_in_window_b tasks offset (fun _ => 0) τ t1 t2 k =
    periodic_index_in_window tasks offset τ t1 t2 k.
Proof.
  intros tasks offset τ t1 t2 k.
  destruct (jittered_index_may_be_in_window_b tasks offset (fun _ => 0) τ t1 t2 k) eqn:Hjit;
  destruct (periodic_index_in_window tasks offset τ t1 t2 k) eqn:Hper; try reflexivity.
  - apply jittered_index_may_be_in_window_b_spec in Hjit.
    apply jittered_index_may_be_in_window_zero_jitter_iff_periodic in Hjit.
    congruence.
  - apply not_true_iff_false in Hjit.
    exfalso. apply Hjit.
    apply jittered_index_may_be_in_window_b_spec.
    apply jittered_index_may_be_in_window_zero_jitter_iff_periodic.
    exact Hper.
Qed.

Lemma jittered_periodic_dbf_window_zero_jitter_eq_periodic :
  forall tasks offset τ t1 t2,
    jittered_periodic_dbf_window tasks offset (fun _ => 0) τ t1 t2 =
    periodic_dbf_window tasks offset τ t1 t2.
Proof.
  intros tasks offset τ t1 t2.
  unfold jittered_periodic_dbf_window, periodic_dbf_window.
  apply f_equal2; [|reflexivity].
  apply f_equal.
  apply filter_ext.
  intros k.
  apply jittered_index_may_be_in_window_b_zero_jitter_eq_periodic.
Qed.

Lemma taskset_jittered_periodic_dbf_window_zero_jitter_eq_periodic :
  forall tasks offset enumT t1 t2,
    taskset_jittered_periodic_dbf_window tasks offset (fun _ => 0) enumT t1 t2 =
    taskset_periodic_dbf_window tasks offset enumT t1 t2.
Proof.
  intros tasks offset enumT t1 t2.
  induction enumT as [|τ enumT IH]; simpl.
  - reflexivity.
  - rewrite jittered_periodic_dbf_window_zero_jitter_eq_periodic.
    rewrite IH. reflexivity.
Qed.

Lemma jittered_index_may_be_in_window_right_monotone :
  forall tasks offset jitter τ t1 t2 t3 k,
    t2 <= t3 ->
    jittered_index_may_be_in_window tasks offset jitter τ t1 t2 k ->
    jittered_index_may_be_in_window tasks offset jitter τ t1 t3 k.
Proof.
  intros tasks offset jitter τ t1 t2 t3 k Hle [Hdl Hwin].
  unfold jittered_index_may_be_in_window in *.
  split; [lia|].
  apply Nat.min_glb.
  - pose proof (Nat.min_glb_l _ _ _ Hwin) as Hrel.
    lia.
  - pose proof (Nat.min_glb_r _ _ _ Hwin) as Hjit.
    exact Hjit.
Qed.

Lemma jittered_index_may_be_in_window_left_weaken :
  forall tasks offset jitter τ t0 t1 t2 k,
    t0 <= t1 ->
    jittered_index_may_be_in_window tasks offset jitter τ t1 t2 k ->
    jittered_index_may_be_in_window tasks offset jitter τ t0 t2 k.
Proof.
  intros tasks offset jitter τ t0 t1 t2 k Hle [Hdl Hwin].
  unfold jittered_index_may_be_in_window in *.
  split; [exact Hdl|].
  eapply Nat.le_trans; [|exact Hwin].
  apply Nat.max_lub.
  - eapply Nat.le_trans; [exact Hle|].
    apply Nat.le_max_l.
  - apply Nat.le_max_r.
Qed.

Lemma jittered_index_may_be_in_window_b_right_monotone :
  forall tasks offset jitter τ t1 t2 t3 k,
    t2 <= t3 ->
    jittered_index_may_be_in_window_b tasks offset jitter τ t1 t2 k = true ->
    jittered_index_may_be_in_window_b tasks offset jitter τ t1 t3 k = true.
Proof.
  intros tasks offset jitter τ t1 t2 t3 k Hle Hwin.
  apply jittered_index_may_be_in_window_b_spec.
  apply (jittered_index_may_be_in_window_right_monotone
           tasks offset jitter τ t1 t2 t3 k Hle).
  apply jittered_index_may_be_in_window_b_spec.
  exact Hwin.
Qed.

Lemma jittered_index_may_be_in_window_b_left_weaken :
  forall tasks offset jitter τ t0 t1 t2 k,
    t0 <= t1 ->
    jittered_index_may_be_in_window_b tasks offset jitter τ t1 t2 k = true ->
    jittered_index_may_be_in_window_b tasks offset jitter τ t0 t2 k = true.
Proof.
  intros tasks offset jitter τ t0 t1 t2 k Hle Hwin.
  apply jittered_index_may_be_in_window_b_spec.
  apply (jittered_index_may_be_in_window_left_weaken
           tasks offset jitter τ t0 t1 t2 k Hle).
  apply jittered_index_may_be_in_window_b_spec.
  exact Hwin.
Qed.

Lemma jittered_periodic_dbf_window_right_monotone :
  forall tasks offset jitter τ t1 t2 t3,
    t2 <= t3 ->
    jittered_periodic_dbf_window tasks offset jitter τ t1 t2 <=
    jittered_periodic_dbf_window tasks offset jitter τ t1 t3.
Proof.
  intros tasks offset jitter τ t1 t2 t3 Hle.
  unfold jittered_periodic_dbf_window.
  apply Nat.mul_le_mono_r.
  eapply NoDup_incl_length.
  - apply NoDup_filter.
    apply seq_NoDup.
  - intros k Hk.
    apply filter_In in Hk.
    destruct Hk as [Hin Hwin].
    apply filter_In.
    split.
    + rewrite in_seq in *.
      lia.
    + eapply jittered_index_may_be_in_window_b_right_monotone; eauto.
Qed.

Lemma jittered_periodic_dbf_window_left_weaken :
  forall tasks offset jitter τ t0 t1 t2,
    t0 <= t1 ->
    jittered_periodic_dbf_window tasks offset jitter τ t1 t2 <=
    jittered_periodic_dbf_window tasks offset jitter τ t0 t2.
Proof.
  intros tasks offset jitter τ t0 t1 t2 Hle.
  unfold jittered_periodic_dbf_window.
  apply Nat.mul_le_mono_r.
  eapply NoDup_incl_length.
  - apply NoDup_filter.
    apply seq_NoDup.
  - intros k Hk.
    apply filter_In in Hk.
    destruct Hk as [Hin Hwin].
    apply filter_In.
    split; [exact Hin|].
    eapply jittered_index_may_be_in_window_b_left_weaken; eauto.
Qed.

Lemma taskset_jittered_periodic_dbf_window_right_monotone :
  forall tasks offset jitter enumT t1 t2 t3,
    t2 <= t3 ->
    taskset_jittered_periodic_dbf_window tasks offset jitter enumT t1 t2 <=
    taskset_jittered_periodic_dbf_window tasks offset jitter enumT t1 t3.
Proof.
  intros tasks offset jitter enumT t1 t2 t3 Hle.
  induction enumT as [|τ enumT IH]; simpl.
  - lia.
  - pose proof (jittered_periodic_dbf_window_right_monotone
                  tasks offset jitter τ t1 t2 t3 Hle) as Hdbf.
    lia.
Qed.

Lemma taskset_jittered_periodic_dbf_window_left_weaken :
  forall tasks offset jitter enumT t0 t1 t2,
    t0 <= t1 ->
    taskset_jittered_periodic_dbf_window tasks offset jitter enumT t1 t2 <=
    taskset_jittered_periodic_dbf_window tasks offset jitter enumT t0 t2.
Proof.
  intros tasks offset jitter enumT t0 t1 t2 Hle.
  induction enumT as [|τ enumT IH]; simpl.
  - lia.
  - pose proof (jittered_periodic_dbf_window_left_weaken
                  tasks offset jitter τ t0 t1 t2 Hle) as Hdbf.
    lia.
Qed.
