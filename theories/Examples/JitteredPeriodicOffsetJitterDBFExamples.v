From Stdlib Require Import Arith Arith.PeanoNat Lia List.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicWindowDemandBound.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicOffsetWindowCutoff.
Import ListNotations.

Definition task_oj_ex : Task := mkTask 1 4 2.

Definition tasks_oj_ex (tau : TaskId) : Task :=
  match tau with
  | 0 => task_oj_ex
  | _ => mkTask 1 1 1
  end.

Definition T_oj_ex (tau : TaskId) : Prop := tau = 0.

Definition enumT_oj_ex : list TaskId := [0].

Definition offset_oj_ex (tau : TaskId) : Time :=
  match tau with
  | 0 => 1
  | _ => 0
  end.

Definition jitter_oj_ex (tau : TaskId) : Time :=
  match tau with
  | 0 => 1
  | _ => 0
  end.

Lemma tasks_oj_ex_well_formed :
  well_formed_periodic_tasks_on T_oj_ex tasks_oj_ex.
Proof.
  intros tau Htau.
  unfold T_oj_ex in Htau.
  subst tau.
  unfold tasks_oj_ex, task_oj_ex.
  simpl.
  lia.
Qed.

Lemma enumT_oj_ex_nodup : NoDup enumT_oj_ex.
Proof.
  repeat constructor; simpl; lia.
Qed.

Lemma T_oj_ex_in_enumT_oj_ex :
  forall tau, T_oj_ex tau -> In tau enumT_oj_ex.
Proof.
  intros tau Htau.
  unfold T_oj_ex in Htau.
  subst tau.
  simpl.
  tauto.
Qed.

Lemma in_enumT_oj_ex_implies_T_oj_ex :
  forall tau, In tau enumT_oj_ex -> T_oj_ex tau.
Proof.
  intros tau Hin.
  unfold T_oj_ex.
  simpl in Hin.
  destruct Hin as [Hin | []].
  symmetry.
  exact Hin.
Qed.

Lemma tasks_oj_ex_positive_period :
  forall tau, In tau enumT_oj_ex -> 0 < task_period (tasks_oj_ex tau).
Proof.
  intros tau Hin.
  apply tasks_oj_ex_well_formed.
  apply in_enumT_oj_ex_implies_T_oj_ex.
  exact Hin.
Qed.

Example jittered_offset_jitter_dbf_test_by_cutoff_ex :
  jittered_offset_window_dbf_test_by_cutoff
    tasks_oj_ex offset_oj_ex jitter_oj_ex enumT_oj_ex = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma jittered_offset_jitter_window_dbf_ex :
  forall t1 t2,
    t1 <= t2 ->
    taskset_jittered_periodic_dbf_window
      tasks_oj_ex offset_oj_ex jitter_oj_ex enumT_oj_ex t1 t2 <= t2 - t1.
Proof.
  apply jittered_offset_window_dbf_check_by_cutoff.
  - exact tasks_oj_ex_positive_period.
  - exact jittered_offset_jitter_dbf_test_by_cutoff_ex.
Qed.

Example jittered_offset_jitter_window_exercises_jitter_ex :
  jittered_periodic_dbf_window
    tasks_oj_ex offset_oj_ex jitter_oj_ex 0 2 4 = 1.
Proof.
  vm_compute.
  reflexivity.
Qed.
