From Stdlib Require Import Arith Arith.PeanoNat Lia List Bool.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.EnumCandidates.
From RocqSched Require Import Uniprocessor.Policies.EDF.
From RocqSched Require Import TaskModels.Periodic.PeriodicFiniteHorizon.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFBridge.
From RocqSched Require Import TaskModels.Periodic.PeriodicEnumeration.
From RocqSched Require Import TaskModels.Periodic.PeriodicWindowDemandBound.
From RocqSched Require Import Examples.PeriodicExamples.

Import ListNotations.

Example periodic_window_dbf_task0_ex :
  periodic_dbf_window tasks_ex offset_ex 0 0 4 = 2.
Proof. reflexivity. Qed.

Example periodic_window_dbf_task1_ex :
  periodic_dbf_window tasks_ex offset_ex 1 0 4 = 1.
Proof. reflexivity. Qed.

Example periodic_window_dbf_taskset_ex :
  taskset_periodic_dbf_window tasks_ex offset_ex enumT_ex 0 4 = 3.
Proof. reflexivity. Qed.

Lemma periodic_window_dbf_test :
  forall t1 t2,
    t1 <= t2 ->
    t2 <= H_ex ->
    taskset_periodic_dbf_window tasks_ex offset_ex enumT_ex t1 t2 <= t2 - t1.
Proof.
  intros t1 t2 Hle1 Hle2.
  unfold H_ex in Hle2.
  assert (t1 <= 4) by lia.
  destruct t1 as [| [| [| [| [| t1']]]]]; try lia;
    destruct t2 as [| [| [| [| [| t2']]]]]; try lia;
    cbn in *; lia.
Qed.

Theorem periodic_example_edf_schedulable_by_window_dbf_auto :
  schedulable_by_on
    (periodic_jobset_upto T_ex tasks_ex offset_ex jobs_ex H_ex)
    (edf_scheduler
       (enum_candidates_of
          (enum_periodic_jobs_upto T_ex tasks_ex offset_ex jobs_ex H_ex enumT_ex codec_ex)))
    jobs_ex 1.
Proof.
  apply periodic_edf_schedulable_by_window_dbf_on_finite_horizon_auto
    with (enumT := enumT_ex).
  - exact tasks_ex_well_formed.
  - intros τ Hτ.
    destruct Hτ as [Hτ | Hτ]; subst τ; simpl; tauto.
  - intros τ Hτ.
    simpl in Hτ.
    destruct Hτ as [Hτ | [Hτ | []]]; subst τ.
    + left. reflexivity.
    + right. reflexivity.
  - exact periodic_window_dbf_test.
Qed.
