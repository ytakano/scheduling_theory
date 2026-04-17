From Stdlib Require Import Arith Arith.PeanoNat Lia List Bool.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.EnumCandidates.
From RocqSched Require Import Uniprocessor.Policies.EDF.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Periodic.PeriodicFiniteHorizon.
From RocqSched Require Import TaskModels.Periodic.PeriodicEnumeration.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFAnalysisEntryPoints.

Import ListNotations.

(* ================================================================ *)
(* 1. A many-task periodic task set                                  *)
(* ================================================================ *)

(* We use three zero-offset periodic tasks. Since all periods exceed the
   finite horizon H_many = 5, only the first job of each task appears inside
   the horizon. This keeps the many-task tutorial concrete while exercising
   the package-based analysis path. *)

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

(* ================================================================ *)
(* 2. Concrete jobs                                                   *)
(* ================================================================ *)

Definition job0_many : Job := mkJob 0 0 0 1 4.
Definition job1_many : Job := mkJob 1 0 0 1 4.
Definition job2_many : Job := mkJob 2 0 0 1 4.

Definition other_job_many : Job := mkJob 3 0 20 1 120.

Definition jobs_many (j : JobId) : Job :=
  match j with
  | 0 => job0_many
  | 1 => job1_many
  | 2 => job2_many
  | _ => other_job_many
  end.

Lemma generated_job0_many :
  generated_by_periodic_task tasks_many offset_many jobs_many 0.
Proof.
  unfold generated_by_periodic_task, jobs_many, job0_many, tasks_many, task0_many, offset_many.
  simpl.
  repeat split; lia.
Qed.

Lemma generated_job1_many :
  generated_by_periodic_task tasks_many offset_many jobs_many 1.
Proof.
  unfold generated_by_periodic_task, jobs_many, job1_many, tasks_many, task1_many, offset_many.
  simpl.
  repeat split; lia.
Qed.

Lemma generated_job2_many :
  generated_by_periodic_task tasks_many offset_many jobs_many 2.
Proof.
  unfold generated_by_periodic_task, jobs_many, job2_many, tasks_many, task2_many, offset_many.
  simpl.
  repeat split; lia.
Qed.

(* ================================================================ *)
(* 3. A finite-horizon codec                                          *)
(* ================================================================ *)

(* Because each task releases only its 0-th job inside the horizon, the codec
   simply maps task IDs 0,1,2 to job IDs 0,1,2. *)

Definition job_id_many (tau : TaskId) (_ : nat) : JobId := tau.

Lemma codec_many_sound :
  forall tau k,
    T_many tau ->
    expected_release tasks_many offset_many tau k < H_many ->
    let j := job_id_many tau k in
    job_task (jobs_many j) = tau /\
    job_index (jobs_many j) = k /\
    generated_by_periodic_task tasks_many offset_many jobs_many j.
Proof.
  intros tau k Htau Hrel.
  destruct Htau as [-> | [-> | ->]].
  - assert (k = 0).
    { unfold expected_release, tasks_many, task0_many, offset_many, H_many in Hrel. simpl in Hrel. lia. }
    subst k.
    simpl.
    split; [reflexivity | split; [reflexivity | exact generated_job0_many]].
  - assert (k = 0).
    { unfold expected_release, tasks_many, task1_many, offset_many, H_many in Hrel. simpl in Hrel. lia. }
    subst k.
    simpl.
    split; [reflexivity | split; [reflexivity | exact generated_job1_many]].
  - assert (k = 0).
    { unfold expected_release, tasks_many, task2_many, offset_many, H_many in Hrel. simpl in Hrel. lia. }
    subst k.
    simpl.
    split; [reflexivity | split; [reflexivity | exact generated_job2_many]].
Qed.

Lemma codec_many_complete :
  forall j,
    periodic_jobset_upto T_many tasks_many offset_many jobs_many H_many j ->
    j = job_id_many (job_task (jobs_many j)) (job_index (jobs_many j)).
Proof.
  intros j Hj.
  destruct j as [| [| [| j']]]; simpl; try reflexivity.
  unfold periodic_jobset_upto, jobs_many, other_job_many, H_many in Hj.
  simpl in Hj.
  destruct Hj as [_ [_ Hrel]].
  lia.
Qed.

Definition finite_codec_many :
  PeriodicFiniteHorizonCodec T_many tasks_many offset_many jobs_many H_many :=
  mkPeriodicFiniteHorizonCodec
    T_many tasks_many offset_many jobs_many H_many
    job_id_many
    codec_many_sound
    codec_many_complete.

(* ================================================================ *)
(* 4. Checker results                                                 *)
(* ================================================================ *)

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

(* ================================================================ *)
(* 5. Per-job bridge obligations                                      *)
(* ================================================================ *)

(* In this example every in-horizon job is released at time 0, so the
   no-carry-in bridge is immediate from the generic release-zero lemma. *)

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
  destruct j as [| [| [| j']]].
  - split; [vm_compute; lia|].
    eapply periodic_edf_busy_prefix_no_carry_in_if_release_zero.
    reflexivity.
  - split; [vm_compute; lia|].
    eapply periodic_edf_busy_prefix_no_carry_in_if_release_zero.
    reflexivity.
  - split; [vm_compute; lia|].
    eapply periodic_edf_busy_prefix_no_carry_in_if_release_zero.
    reflexivity.
  - exfalso.
    unfold periodic_jobset_upto, jobs_many, other_job_many, H_many in Hj.
    simpl in Hj.
    destruct Hj as [_ [_ Hrel]].
    lia.
Qed.

(* ================================================================ *)
(* 6. Obligation packages                                             *)
(* ================================================================ *)

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

(* ================================================================ *)
(* 7. Final theorems                                                  *)
(* ================================================================ *)

(* First choice: zero-offset classical DBF. *)

Theorem tutorial_many_task_schedulable_by_classical_package_on_finite_horizon :
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

(* Fallback path: explicit window-DBF checker package. *)

Theorem tutorial_many_task_schedulable_by_window_package_on_finite_horizon :
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
