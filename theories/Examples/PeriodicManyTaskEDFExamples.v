From Stdlib Require Import Arith Arith.PeanoNat Lia List Bool.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.EnumCandidates.
From RocqSched Require Import Uniprocessor.Policies.EDF.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Periodic.PeriodicCodec.
From RocqSched Require Import TaskModels.Periodic.PeriodicInfinite.
From RocqSched Require Import TaskModels.Periodic.PeriodicFiniteHorizon.
From RocqSched Require Import TaskModels.Periodic.PeriodicEnumeration.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFAnalysisEntryPoints.

Import ListNotations.

Definition task0_many : Task := mkTask 1 10 4.
Definition task1_many : Task := mkTask 1 11 4.
Definition task2_many : Task := mkTask 1 12 4.

Definition tasks_many (tau : TaskId) : Task :=
  match tau with
  | 0 => task0_many
  | 1 => task1_many
  | 2 => task2_many
  | _ => mkTask 1 100 100
  end.

Definition T_many (tau : TaskId) : Prop := tau = 0 \/ tau = 1 \/ tau = 2.

Definition offset_many (_ : TaskId) : Time := 0.

Definition H_many : Time := 5.

Definition enumT_many : list TaskId := [0; 1; 2].

Definition jobs_many (j : JobId) : Job :=
  match Nat.modulo j 3 with
  | 0 => mkJob 0 (j / 3) ((j / 3) * 10) 1 ((j / 3) * 10 + 4)
  | 1 => mkJob 1 (j / 3) ((j / 3) * 11) 1 ((j / 3) * 11 + 4)
  | _ => mkJob 2 (j / 3) ((j / 3) * 12) 1 ((j / 3) * 12 + 4)
  end.

Lemma jobs_many_task0 :
  forall k,
    jobs_many (3 * k) = mkJob 0 k (k * 10) 1 (k * 10 + 4).
Proof.
  intro k.
  unfold jobs_many.
  replace (3 * k) with (k * 3) by lia.
  rewrite Nat.mod_mul by lia.
  rewrite Nat.div_mul by lia.
  reflexivity.
Qed.

Lemma jobs_many_task1 :
  forall k,
    jobs_many (S (3 * k)) = mkJob 1 k (k * 11) 1 (k * 11 + 4).
Proof.
  intro k.
  replace (S (3 * k)) with (1 + 3 * k) by lia.
  unfold jobs_many.
  assert (Hmod : Nat.modulo (1 + 3 * k) 3 = 1).
  {
    rewrite Nat.add_mod by lia.
    replace ((3 * k) mod 3) with 0.
    2:{
      symmetry.
      rewrite Nat.mul_comm.
      apply Nat.mod_mul.
      lia.
    }
    simpl.
    reflexivity.
  }
  rewrite Hmod.
  assert (Hdiv : (1 + 3 * k) / 3 = k).
  {
    pose proof (Nat.div_mod (1 + 3 * k) 3) as H.
    specialize (H ltac:(lia)).
    rewrite Hmod in H.
    lia.
  }
  rewrite Hdiv.
  reflexivity.
Qed.

Lemma jobs_many_task2 :
  forall k,
    jobs_many (S (S (3 * k))) = mkJob 2 k (k * 12) 1 (k * 12 + 4).
Proof.
  intro k.
  replace (S (S (3 * k))) with (2 + 3 * k) by lia.
  unfold jobs_many.
  assert (Hmod : Nat.modulo (2 + 3 * k) 3 = 2).
  {
    rewrite Nat.add_mod by lia.
    replace ((3 * k) mod 3) with 0.
    2:{
      symmetry.
      rewrite Nat.mul_comm.
      apply Nat.mod_mul.
      lia.
    }
    simpl.
    reflexivity.
  }
  rewrite Hmod.
  assert (Hdiv : (2 + 3 * k) / 3 = k).
  {
    pose proof (Nat.div_mod (2 + 3 * k) 3) as H.
    specialize (H ltac:(lia)).
    rewrite Hmod in H.
    lia.
  }
  rewrite Hdiv.
  reflexivity.
Qed.

Lemma tasks_many_well_formed :
  well_formed_periodic_tasks_on T_many tasks_many.
Proof.
  intros tau Htau.
  destruct Htau as [-> | [-> | ->]]; simpl; lia.
Qed.

Lemma enumT_many_nodup :
  NoDup enumT_many.
Proof.
  unfold enumT_many.
  constructor.
  - simpl. intuition congruence.
  - constructor.
    + simpl. intuition congruence.
    + constructor.
      * simpl. intuition congruence.
      * constructor.
Qed.

Lemma T_many_in_enumT_many :
  forall tau, T_many tau -> In tau enumT_many.
Proof.
  intros tau Htau.
  destruct Htau as [-> | [-> | ->]]; simpl; tauto.
Qed.

Lemma in_enumT_many_implies_T_many :
  forall tau, In tau enumT_many -> T_many tau.
Proof.
  intros tau Hin.
  simpl in Hin.
  destruct Hin as [H | [H | [H | []]]].
  - subst tau. now left.
  - subst tau. now right; left.
  - subst tau. now right; right.
Qed.

Definition job_id_many (tau : TaskId) (k : nat) : JobId :=
  match tau with
  | 0 => k + (k + (k + 0))
  | 1 => S (k + (k + (k + 0)))
  | _ => S (S (k + (k + (k + 0))))
  end.

Lemma codec_many_sound :
  forall tau k,
    T_many tau ->
    let j := job_id_many tau k in
    job_task (jobs_many j) = tau /\
    job_index (jobs_many j) = k /\
    generated_by_periodic_task tasks_many offset_many jobs_many j.
Proof.
  intros tau k Htau.
  destruct Htau as [-> | [-> | ->]].
  - cbn [job_id_many].
    replace (k + (k + (k + 0))) with (3 * k) by lia.
    split.
    + rewrite jobs_many_task0. reflexivity.
    + split.
      * rewrite jobs_many_task0. reflexivity.
      * unfold generated_by_periodic_task, offset_many, expected_release, expected_abs_deadline.
        rewrite jobs_many_task0.
        simpl.
        split; [reflexivity | split; [reflexivity | lia]].
  - cbn [job_id_many].
    replace (S (k + (k + (k + 0)))) with (S (3 * k)) by lia.
    split.
    + rewrite jobs_many_task1. reflexivity.
    + split.
      * rewrite jobs_many_task1. reflexivity.
      * unfold generated_by_periodic_task, offset_many, expected_release, expected_abs_deadline.
        rewrite jobs_many_task1.
        simpl.
        split; [reflexivity | split; [reflexivity | lia]].
  - cbn [job_id_many].
    replace (S (S (k + (k + (k + 0))))) with (S (S (3 * k))) by lia.
    split.
    + rewrite jobs_many_task2. reflexivity.
    + split.
      * rewrite jobs_many_task2. reflexivity.
      * unfold generated_by_periodic_task, offset_many, expected_release, expected_abs_deadline.
        rewrite jobs_many_task2.
        simpl.
        split; [reflexivity | split; [reflexivity | lia]].
Qed.

Lemma codec_many_complete :
  forall j,
    periodic_jobset T_many tasks_many offset_many jobs_many j ->
    j = job_id_many (job_task (jobs_many j)) (job_index (jobs_many j)).
Proof.
  intros j _.
  destruct (Nat.modulo j 3) as [| [| n]] eqn:Hmod.
  - assert (Hjrep : j = 3 * (j / 3)).
    { pose proof (Nat.div_mod j 3) as Hdiv.
      specialize (Hdiv ltac:(lia)).
      rewrite Hmod in Hdiv.
      lia. }
    rewrite Hjrep.
    rewrite jobs_many_task0.
    cbn [job_id_many].
    replace (3 * (j / 3)) with ((j / 3) + ((j / 3) + ((j / 3) + 0))) by lia.
    reflexivity.
  - assert (Hjrep : j = S (3 * (j / 3))).
    { pose proof (Nat.div_mod j 3) as Hdiv.
      specialize (Hdiv ltac:(lia)).
      rewrite Hmod in Hdiv.
      replace (S (3 * (j / 3))) with (3 * (j / 3) + 1) by lia.
      exact Hdiv. }
    rewrite Hjrep.
    rewrite jobs_many_task1.
    cbn [job_id_many].
    replace (3 * (j / 3)) with ((j / 3) + ((j / 3) + ((j / 3) + 0))) by lia.
    reflexivity.
  - assert (n = 0).
    { pose proof (Nat.mod_upper_bound j 3 ltac:(lia)) as Hlt.
      rewrite Hmod in Hlt.
      lia. }
    subst n.
    assert (Hjrep : j = S (S (3 * (j / 3)))).
    { pose proof (Nat.div_mod j 3) as Hdiv.
      specialize (Hdiv ltac:(lia)).
      rewrite Hmod in Hdiv.
      replace (S (S (3 * (j / 3)))) with (3 * (j / 3) + 2) by lia.
      exact Hdiv. }
    rewrite Hjrep.
    rewrite jobs_many_task2.
    cbn [job_id_many].
    replace (3 * (j / 3)) with ((j / 3) + ((j / 3) + ((j / 3) + 0))) by lia.
    reflexivity.
Qed.

Definition codec_many :
  PeriodicCodec T_many tasks_many offset_many jobs_many :=
  mkPeriodicCodec
    T_many tasks_many offset_many jobs_many
    job_id_many
    codec_many_sound
    codec_many_complete.

Definition finite_codec_many :
  PeriodicFiniteHorizonCodec T_many tasks_many offset_many jobs_many H_many :=
  zero_offset_periodic_finite_horizon_codec_of
    T_many tasks_many jobs_many H_many codec_many.

Example many_task_window_dbf_test :
  window_dbf_test_upto tasks_many offset_many enumT_many H_many = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

Example many_task_dbf_test_by_cutoff :
  dbf_test_by_cutoff tasks_many enumT_many = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma many_task_deadline_and_no_carry_in :
  forall j,
    periodic_jobset_upto T_many tasks_many offset_many jobs_many H_many j ->
    job_abs_deadline (jobs_many j) <= H_many /\
    periodic_edf_busy_prefix_no_carry_in_bridge
      T_many tasks_many offset_many jobs_many H_many
      (generated_periodic_edf_schedule_on_finite_horizon
         T_many tasks_many offset_many jobs_many H_many enumT_many finite_codec_many)
      j.
Proof.
  intros j Hj.
  pose proof (periodic_jobset_upto_implies_task_in_scope T_many tasks_many offset_many jobs_many H_many j Hj)
    as Htau.
  pose proof (periodic_jobset_upto_expected_release_lt T_many tasks_many offset_many jobs_many H_many j Hj)
    as Hrel_lt.
  pose proof (periodic_job_id_of_complete
                T_many tasks_many offset_many jobs_many H_many finite_codec_many j Hj)
    as Hjcodec.
  assert (Hk0 : job_index (jobs_many j) = 0).
  {
    pose proof (periodic_jobset_upto_implies_index_lt_tight
                  T_many tasks_many offset_many jobs_many H_many j
                  tasks_many_well_formed Hj) as Hidx.
    destruct Htau as [Htau | [Htau | Htau]];
      rewrite Htau in Hidx;
      unfold H_many, tasks_many, task0_many, task1_many, task2_many in Hidx;
      simpl in Hidx;
      lia.
  }
  rewrite Hk0 in Hjcodec.
  destruct Htau as [Htau | [Htau | Htau]]; subst.
  - rewrite Htau in Hjcodec. simpl in Hjcodec. subst j.
    split; [vm_compute; lia|].
    eapply periodic_edf_busy_prefix_no_carry_in_if_release_zero.
    reflexivity.
  - rewrite Htau in Hjcodec. simpl in Hjcodec. subst j.
    split; [vm_compute; lia|].
    eapply periodic_edf_busy_prefix_no_carry_in_if_release_zero.
    reflexivity.
  - rewrite Htau in Hjcodec. simpl in Hjcodec. subst j.
    split; [vm_compute; lia|].
    eapply periodic_edf_busy_prefix_no_carry_in_if_release_zero.
    reflexivity.
Qed.

Definition many_task_window_obligations :
  PeriodicEDFConcreteWindowObligations
    T_many tasks_many offset_many jobs_many H_many enumT_many finite_codec_many.
Proof.
  refine
    {| periodic_edf_concrete_tasks_wf := tasks_many_well_formed;
       periodic_edf_concrete_enumT_nodup := enumT_many_nodup;
       periodic_edf_concrete_enumT_complete := T_many_in_enumT_many;
       periodic_edf_concrete_enumT_sound := in_enumT_many_implies_T_many;
       periodic_edf_concrete_deadline_and_no_carry_in := many_task_deadline_and_no_carry_in;
       periodic_edf_concrete_window_dbf_test := many_task_window_dbf_test |}.
Qed.

Definition many_task_classical_obligations :
  PeriodicEDFConcreteClassicalObligations
    T_many tasks_many jobs_many H_many enumT_many finite_codec_many.
Proof.
  refine
    {| periodic_edf_concrete_window_base := many_task_window_obligations;
       periodic_edf_concrete_dbf_test_by_cutoff := many_task_dbf_test_by_cutoff |}.
Qed.

Theorem many_task_schedulable_by_window_package_on_finite_horizon :
  schedulable_by_on
    (periodic_jobset_upto T_many tasks_many offset_many jobs_many H_many)
    (edf_scheduler
       (enum_candidates_of
          (generated_periodic_edf_finite_enumJ
             T_many tasks_many offset_many jobs_many H_many enumT_many finite_codec_many)))
    jobs_many 1.
Proof.
  apply periodic_edf_schedulable_by_window_dbf_on_finite_horizon_generated_from_obligations.
  exact many_task_window_obligations.
Qed.

Theorem many_task_schedulable_by_classical_package_on_finite_horizon :
  schedulable_by_on
    (periodic_jobset_upto T_many tasks_many offset_many jobs_many H_many)
    (edf_scheduler
       (enum_candidates_of
          (generated_periodic_edf_finite_enumJ
             T_many tasks_many offset_many jobs_many H_many enumT_many finite_codec_many)))
    jobs_many 1.
Proof.
  apply periodic_edf_schedulable_by_classical_dbf_on_finite_horizon_generated_from_obligations.
  exact many_task_classical_obligations.
Qed.
