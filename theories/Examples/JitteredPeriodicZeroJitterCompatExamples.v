From Stdlib Require Import Arith Arith.PeanoNat Lia List.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import TaskModels.Periodic.PeriodicWindowDemandBound.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicWindowDemandBound.
From RocqSched Require Import Examples.JitteredPeriodicOffsetJitterDBFExamples.
Import ListNotations.

Lemma jittered_zero_jitter_window_dbf_eq_periodic_ex :
  forall t1 t2,
    taskset_jittered_periodic_dbf_window
      tasks_oj_ex offset_oj_ex (fun _ => 0) enumT_oj_ex t1 t2 =
    taskset_periodic_dbf_window
      tasks_oj_ex offset_oj_ex enumT_oj_ex t1 t2.
Proof.
  intros t1 t2.
  apply taskset_jittered_periodic_dbf_window_zero_jitter_eq_periodic.
Qed.

Example jittered_zero_jitter_offset_window_ex :
  taskset_jittered_periodic_dbf_window
    tasks_oj_ex offset_oj_ex (fun _ => 0) enumT_oj_ex 1 3 =
  taskset_periodic_dbf_window
    tasks_oj_ex offset_oj_ex enumT_oj_ex 1 3.
Proof.
  apply jittered_zero_jitter_window_dbf_eq_periodic_ex.
Qed.
