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

Definition jobs_many : JobId -> Job :=
  canonical_periodic_jobs_from_enumT tasks_many offset_many enumT_many.

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

Definition codec_many :
  PeriodicCodec T_many tasks_many offset_many jobs_many :=
  zero_offset_periodic_codec_of_tasks
    T_many tasks_many enumT_many
    enumT_many_nodup
    T_many_in_enumT_many
    in_enumT_many_implies_T_many
    ltac:(vm_compute; lia).

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

Section InfiniteManyTaskEDFExample.

  Hypothesis many_task_infinite_no_carry_in_bridge :
    forall j,
      periodic_jobset T_many tasks_many offset_many jobs_many j ->
      periodic_edf_busy_prefix_no_carry_in_bridge
        T_many tasks_many offset_many jobs_many
        (S (job_abs_deadline (jobs_many j)))
        (generated_periodic_edf_schedule_upto
           T_many tasks_many offset_many jobs_many
           (S (job_abs_deadline (jobs_many j)))
           enumT_many codec_many)
        j.

  Definition many_task_infinite_classical_obligations :
    PeriodicEDFConcreteInfiniteClassicalObligations
      T_many tasks_many offset_many jobs_many enumT_many codec_many.
  Proof.
    refine
      {| periodic_edf_concrete_infinite_tasks_wf := tasks_many_well_formed;
         periodic_edf_concrete_infinite_enumT_nodup := enumT_many_nodup;
         periodic_edf_concrete_infinite_enumT_complete := T_many_in_enumT_many;
         periodic_edf_concrete_infinite_enumT_sound := in_enumT_many_implies_T_many;
         periodic_edf_concrete_infinite_offset_zero := _;
         periodic_edf_concrete_infinite_no_carry_in_bridge :=
           many_task_infinite_no_carry_in_bridge;
         periodic_edf_concrete_infinite_dbf_test_by_cutoff :=
           many_task_dbf_test_by_cutoff |}.
    intros τ _.
    reflexivity.
  Qed.

  Theorem many_task_schedulable_by_classical_package_infinite :
    schedulable_by_on
      (periodic_jobset T_many tasks_many offset_many jobs_many)
      (edf_scheduler
         (periodic_candidates_before
            T_many tasks_many offset_many jobs_many enumT_many codec_many))
      jobs_many 1.
  Proof.
    apply periodic_edf_schedulable_by_classical_dbf_generated_from_infinite_obligations.
    exact many_task_infinite_classical_obligations.
  Qed.

End InfiniteManyTaskEDFExample.
