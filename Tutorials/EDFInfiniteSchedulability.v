From Stdlib Require Import Arith Arith.PeanoNat Lia List Bool.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Analysis.Uniprocessor.ProcessorDemand.
From RocqSched Require Import Uniprocessor.Policies.EDF.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Periodic.PeriodicInfinite.
From RocqSched Require Import TaskModels.Periodic.PeriodicCodec.
From RocqSched Require Import TaskModels.Periodic.PeriodicClassicDBF.
From RocqSched Require Import TaskModels.Periodic.PeriodicConcreteAnalysis.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFInfiniteBridge.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFAnalysisEntryPoints.

Import ListNotations.

(* ================================================================ *)
(* 1. A concrete periodic task set                                  *)
(* ================================================================ *)

Definition task0_ex : Task := mkTask 1 5 2.
Definition task1_ex : Task := mkTask 1 7 3.

Definition tasks_ex (tau : TaskId) : Task :=
  match tau with
  | 0 => task0_ex
  | 1 => task1_ex
  | _ => mkTask 1 100 100
  end.

Definition T_ex (tau : TaskId) : Prop := tau = 0 \/ tau = 1.

Definition offset_ex (_ : TaskId) : Time := 0.

Definition enumT_ex : list TaskId := [0; 1].

(* ================================================================ *)
(* 2. Concrete infinite jobs                                         *)
(* ================================================================ *)

(* We encode all jobs of task 0 as even JobIds and all jobs of task 1
   as odd JobIds. This yields a total global codec on (task, index). *)

Definition job_id_of_ex (tau : TaskId) (k : nat) : JobId :=
  match tau with
  | 0 => 2 * k
  | 1 => S (2 * k)
  | _ => 0
  end.

Definition jobs_ex (j : JobId) : Job :=
  if Nat.even j then
    mkJob 0 (Nat.div2 j) (5 * Nat.div2 j) 1 (5 * Nat.div2 j + 2)
  else
    mkJob 1 (Nat.div2 j) (7 * Nat.div2 j) 1 (7 * Nat.div2 j + 3).

Lemma generated_job0_ex :
  generated_by_periodic_task tasks_ex offset_ex jobs_ex (job_id_of_ex 0 0).
Proof.
  unfold generated_by_periodic_task, job_id_of_ex, jobs_ex, tasks_ex, offset_ex.
  simpl.
  repeat split; lia.
Qed.

Lemma generated_job1_ex :
  generated_by_periodic_task tasks_ex offset_ex jobs_ex (job_id_of_ex 1 0).
Proof.
  unfold generated_by_periodic_task, job_id_of_ex, jobs_ex, tasks_ex, offset_ex.
  simpl.
  repeat split; lia.
Qed.

Lemma tasks_ex_well_formed :
  well_formed_periodic_tasks_on T_ex tasks_ex.
Proof.
  intros tau Htau.
  destruct Htau as [-> | ->]; simpl; lia.
Qed.

Lemma enumT_ex_nodup :
  NoDup enumT_ex.
Proof.
  unfold enumT_ex.
  constructor.
  - simpl. intros [H | []]. discriminate.
  - constructor.
    + simpl. tauto.
    + constructor.
Qed.

Lemma enumT_ex_complete :
  forall tau, T_ex tau -> In tau enumT_ex.
Proof.
  intros tau Htau.
  destruct Htau as [-> | ->]; simpl; tauto.
Qed.

Lemma enumT_ex_sound :
  forall tau, In tau enumT_ex -> T_ex tau.
Proof.
  intros tau Htau.
  simpl in Htau.
  destruct Htau as [Htau | [Htau | []]]; subst tau.
  - left; reflexivity.
  - right; reflexivity.
Qed.

Lemma jobs_ex_task0 :
  forall k,
    jobs_ex (2 * k) = mkJob 0 k (5 * k) 1 (5 * k + 2).
Proof.
  intros k.
  unfold jobs_ex.
  rewrite Nat.even_mul.
  simpl.
  replace (Nat.div2 (k + (k + 0))) with k.
  2:{ replace (k + (k + 0)) with (2 * k) by lia.
      symmetry; apply Nat.div2_double. }
  reflexivity.
Qed.

Lemma jobs_ex_task1 :
  forall k,
    jobs_ex (S (2 * k)) = mkJob 1 k (7 * k) 1 (7 * k + 3).
Proof.
  intros k.
  unfold jobs_ex.
  rewrite Nat.even_succ.
  rewrite Nat.odd_mul.
  simpl.
  replace
    match k + (k + 0) with
    | 0 => 0
    | S n' => S (Nat.div2 n')
    end
  with k.
  2:{
    replace
      (match k + (k + 0) with
       | 0 => 0
       | S n' => S (Nat.div2 n')
       end)
    with (Nat.div2 (S (k + (k + 0)))) by reflexivity.
    replace (S (k + (k + 0))) with (S (2 * k)) by lia.
    symmetry; apply Nat.div2_succ_double.
  }
  reflexivity.
Qed.

(* ================================================================ *)
(* 3. A concrete global codec                                        *)
(* ================================================================ *)

Lemma codec_ex_sound :
  forall tau k,
    T_ex tau ->
    let j := job_id_of_ex tau k in
    job_task (jobs_ex j) = tau /\
    job_index (jobs_ex j) = k /\
    generated_by_periodic_task tasks_ex offset_ex jobs_ex j.
Proof.
  intros tau k Htau.
  destruct Htau as [-> | ->].
  - unfold job_id_of_ex.
    split.
    + rewrite jobs_ex_task0. reflexivity.
    + split.
      * rewrite jobs_ex_task0. reflexivity.
      * unfold generated_by_periodic_task, expected_release, expected_abs_deadline.
        unfold tasks_ex, offset_ex.
        rewrite jobs_ex_task0.
        unfold expected_release.
        simpl.
        split.
        -- rewrite Nat.mul_comm. reflexivity.
        -- split.
           ++ nia.
           ++ lia.
  - unfold job_id_of_ex.
    split.
    + rewrite jobs_ex_task1. reflexivity.
    + split.
      * rewrite jobs_ex_task1. reflexivity.
      * unfold generated_by_periodic_task, expected_release, expected_abs_deadline.
        unfold tasks_ex, offset_ex.
        rewrite jobs_ex_task1.
        unfold expected_release.
        simpl.
        split.
        -- rewrite Nat.mul_comm. reflexivity.
        -- split.
           ++ nia.
           ++ lia.
Qed.

Lemma codec_ex_complete :
  forall j,
    periodic_jobset T_ex tasks_ex offset_ex jobs_ex j ->
    j = job_id_of_ex (job_task (jobs_ex j)) (job_index (jobs_ex j)).
Proof.
  intros j _.
  destruct (Nat.even j) eqn:Heven.
  - apply Nat.even_spec in Heven.
    destruct Heven as [k ->].
    unfold job_id_of_ex.
    rewrite jobs_ex_task0.
    reflexivity.
  - assert (Hodd : Nat.odd j = true).
    { rewrite <- Nat.negb_even. rewrite Heven. reflexivity. }
    apply Nat.odd_spec in Hodd.
    destruct Hodd as [k Hk].
    subst j.
    replace (2 * k + 1) with (S (2 * k)) by lia.
    unfold job_id_of_ex.
    rewrite jobs_ex_task1.
    reflexivity.
Qed.

Definition codec_ex : PeriodicCodec T_ex tasks_ex offset_ex jobs_ex :=
  mkPeriodicCodec
    T_ex tasks_ex offset_ex jobs_ex
    job_id_of_ex
    codec_ex_sound
    codec_ex_complete.

(* ================================================================ *)
(* 4. The generated schedules and user obligations                   *)
(* ================================================================ *)

Definition sched_inf_ex : Schedule :=
  generated_periodic_edf_schedule
    T_ex tasks_ex offset_ex jobs_ex enumT_ex codec_ex.

Lemma sched_inf_ex_scheduler_rel :
  scheduler_rel
    (edf_scheduler
       (periodic_candidates_before
          T_ex tasks_ex offset_ex jobs_ex enumT_ex codec_ex))
    jobs_ex 1 sched_inf_ex.
Proof.
  unfold sched_inf_ex.
  exact
    (generated_periodic_edf_schedule_scheduler_rel
       T_ex tasks_ex offset_ex jobs_ex enumT_ex codec_ex).
Qed.

Lemma sched_inf_ex_valid :
  valid_schedule jobs_ex 1 sched_inf_ex.
Proof.
  unfold sched_inf_ex.
  exact
    (generated_periodic_edf_schedule_valid
       T_ex tasks_ex offset_ex jobs_ex enumT_ex codec_ex).
Qed.

Lemma sched_upto_ex_completed_iff_sched_inf_ex :
  forall H j t,
    t < H ->
    completed
      jobs_ex 1
      (generated_periodic_edf_schedule_upto
         T_ex tasks_ex offset_ex jobs_ex H enumT_ex codec_ex)
      j t <->
    completed jobs_ex 1 sched_inf_ex j t.
Proof.
  intros H j t Ht.
  unfold sched_inf_ex.
  exact
    (generated_periodic_edf_schedule_upto_completed_iff_generated_before
       T_ex tasks_ex offset_ex jobs_ex enumT_ex codec_ex
       H j t
       tasks_ex_well_formed
       enumT_ex_complete
       enumT_ex_sound
       Ht).
Qed.

Lemma hyperperiod_load_ex :
  hyperperiod_load tasks_ex enumT_ex 35 = 12.
Proof.
  reflexivity.
Qed.

Lemma periodic_classical_dbf_upto_38_ex :
  forall t,
    t <= 38 ->
    taskset_periodic_dbf tasks_ex enumT_ex t <= t.
Proof.
  intros t Ht.
  do 39 (
    destruct t as [| t];
    [cbn; lia |]
  ).
  lia.
Qed.

Lemma periodic_classical_dbf_from_cutoff_ex :
  forall t,
    taskset_periodic_dbf tasks_ex enumT_ex t <= t.
Proof.
  intros t.
  destruct (le_gt_dec t 38) as [Hle | Hgt].
  - exact (periodic_classical_dbf_upto_38_ex t Hle).
  - set (delta := t - 3).
    set (q := delta / 35).
    set (r := delta mod 35).
    set (base := 3 + r).
    assert (Hbase_ge : 3 <= base).
    { unfold base. lia. }
    assert (Hbase_le : base <= 38).
    {
      assert (Hr_lt : r < 35).
      {
        unfold r.
        apply Nat.mod_upper_bound.
        lia.
      }
      unfold base.
      lia.
    }
    assert (Hbase_eq : t = base + q * 35).
    {
      unfold base, q, r, delta.
      pose proof (Nat.div_mod (t - 3) 35) as Hdivmod.
      assert (Hneq : 35 <> 0) by lia.
      specialize (Hdivmod Hneq).
      lia.
    }
    assert (Hbase_dbf :
      taskset_periodic_dbf tasks_ex enumT_ex base <= base).
    {
      apply periodic_classical_dbf_upto_38_ex.
      exact Hbase_le.
    }
    assert (Hperiodic :
      taskset_periodic_dbf tasks_ex enumT_ex t =
      taskset_periodic_dbf tasks_ex enumT_ex base +
      q * hyperperiod_load tasks_ex enumT_ex 35).
    {
      rewrite Hbase_eq.
      eapply (taskset_periodic_dbf_add_hyperperiod_after_deadline_n
                tasks_ex enumT_ex base 35 q).
      - intros τ Hin.
        simpl in Hin.
        destruct Hin as [Hin | [Hin | []]]; subst τ; simpl.
        + lia.
        + exact Hbase_ge.
      - intros τ Hin.
        apply tasks_ex_well_formed.
        apply enumT_ex_sound.
        exact Hin.
      - intros τ Hin.
        simpl in Hin.
        destruct Hin as [Hin | [Hin | []]]; subst τ.
        + exists 7. reflexivity.
        + exists 5. reflexivity.
    }
    rewrite Hperiodic.
    rewrite hyperperiod_load_ex.
    nia.
Qed.

Lemma periodic_window_dbf_from_cutoff_ex :
  forall t1 t2,
    t1 <= t2 ->
    taskset_periodic_dbf_window tasks_ex offset_ex enumT_ex t1 t2 <= t2 - t1.
Proof.
  intros t1 t2 Hle.
  eapply Nat.le_trans.
  - eapply zero_offset_taskset_window_dbf_le_classical_dbf.
    + intros τ Hin. reflexivity.
    + intros τ Hin.
      apply tasks_ex_well_formed.
      apply enumT_ex_sound.
      exact Hin.
  - apply periodic_classical_dbf_from_cutoff_ex.
Qed.

Definition periodic_window_dbf_bound_ex : Prop :=
  forall t1 t2,
    t1 <= t2 ->
    taskset_periodic_dbf_window tasks_ex offset_ex enumT_ex t1 t2 <= t2 - t1.

Definition generated_edf_busy_prefix_no_carry_in_bridge_ex : Prop :=
  forall j,
    periodic_jobset T_ex tasks_ex offset_ex jobs_ex j ->
    periodic_edf_busy_prefix_no_carry_in_bridge
      T_ex tasks_ex offset_ex jobs_ex
      (S (job_abs_deadline (jobs_ex j)))
      (generated_periodic_edf_schedule_upto
         T_ex tasks_ex offset_ex jobs_ex
         (S (job_abs_deadline (jobs_ex j)))
         enumT_ex codec_ex)
      j.

Section TutorialProof.
  Hypothesis Hbridge : generated_edf_busy_prefix_no_carry_in_bridge_ex.

  Theorem tutorial_periodic_edf_job0_no_deadline_miss :
    ~ missed_deadline jobs_ex 1 sched_inf_ex (job_id_of_ex 0 0).
  Proof.
    apply periodic_edf_no_deadline_miss_from_window_dbf_with_no_carry_in_bridge.
    - exact tasks_ex_well_formed.
    - exact enumT_ex_nodup.
    - exact enumT_ex_complete.
    - exact enumT_ex_sound.
    - unfold periodic_jobset, T_ex.
      split.
      + left. reflexivity.
      + exact generated_job0_ex.
    - apply Hbridge.
      unfold periodic_jobset, T_ex.
      split.
      + left. reflexivity.
      + exact generated_job0_ex.
    - exact periodic_window_dbf_from_cutoff_ex.
  Qed.

  Theorem tutorial_periodic_edf_schedulable :
    schedulable_by_on
      (periodic_jobset T_ex tasks_ex offset_ex jobs_ex)
      (edf_scheduler
         (periodic_candidates_before
            T_ex tasks_ex offset_ex jobs_ex enumT_ex codec_ex))
      jobs_ex 1.
  Proof.
    eapply periodic_edf_schedulable_by_on_with_no_carry_in_bridge.
    1: exact tasks_ex_well_formed.
    1: exact enumT_ex_nodup.
    1: exact enumT_ex_complete.
    1: exact enumT_ex_sound.
    1: apply Hbridge.
    1: exact periodic_window_dbf_from_cutoff_ex.
  Qed.

End TutorialProof.

Section TutorialClassicalProof.
  Hypothesis Hbridge : generated_edf_busy_prefix_no_carry_in_bridge_ex.

  Theorem tutorial_periodic_edf_job0_no_deadline_miss_by_classical_dbf :
    ~ missed_deadline jobs_ex 1 sched_inf_ex (job_id_of_ex 0 0).
  Proof.
    apply periodic_edf_no_deadline_miss_from_classical_dbf_with_no_carry_in_bridge.
    - exact tasks_ex_well_formed.
    - exact enumT_ex_nodup.
    - exact enumT_ex_complete.
    - exact enumT_ex_sound.
    - intros τ Hin. reflexivity.
    - unfold periodic_jobset, T_ex.
      split.
      + left. reflexivity.
      + exact generated_job0_ex.
    - apply Hbridge.
      unfold periodic_jobset, T_ex.
      split.
      + left. reflexivity.
      + exact generated_job0_ex.
    - exact periodic_classical_dbf_from_cutoff_ex.
  Qed.

  Theorem tutorial_periodic_edf_schedulable_by_classical_dbf :
    schedulable_by_on
      (periodic_jobset T_ex tasks_ex offset_ex jobs_ex)
      (edf_scheduler
         (periodic_candidates_before
            T_ex tasks_ex offset_ex jobs_ex enumT_ex codec_ex))
      jobs_ex 1.
  Proof.
    eapply periodic_edf_schedulable_by_classical_dbf_with_no_carry_in_bridge.
    1: exact tasks_ex_well_formed.
    1: exact enumT_ex_nodup.
    1: exact enumT_ex_complete.
    1: exact enumT_ex_sound.
    1: intros τ Hin; reflexivity.
    1: apply Hbridge.
    1: exact periodic_classical_dbf_from_cutoff_ex.
  Qed.
End TutorialClassicalProof.
