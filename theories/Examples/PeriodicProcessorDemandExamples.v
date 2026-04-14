From Stdlib Require Import Arith Arith.PeanoNat Lia List Bool.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.EnumCandidates.
From RocqSched Require Import Uniprocessor.Policies.EDF.
From RocqSched Require Import Analysis.Uniprocessor.BusyWindowSearch.
From RocqSched Require Import TaskModels.Periodic.PeriodicFiniteHorizon.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFBridge.
From RocqSched Require Import TaskModels.Periodic.PeriodicEnumeration.
From RocqSched Require Import TaskModels.Periodic.PeriodicWindowDemandBound.
From RocqSched Require Import Semantics.Schedule.
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

Theorem periodic_example_edf_no_deadline_miss_by_window_dbf_auto :
  forall sched j t1 t2,
    scheduler_rel
      (edf_scheduler
         (enum_candidates_of
            (enum_periodic_jobs_upto T_ex tasks_ex offset_ex jobs_ex H_ex enumT_ex codec_ex)))
      jobs_ex 1 sched ->
    periodic_jobset_upto T_ex tasks_ex offset_ex jobs_ex H_ex j ->
    busy_window_witness sched (job_abs_deadline (jobs_ex j)) t1 t2 ->
    t1 <= job_release (jobs_ex j) ->
    job_abs_deadline (jobs_ex j) <= H_ex ->
    (forall t j_run,
      job_release (jobs_ex j) <= t < job_abs_deadline (jobs_ex j) ->
      sched t 0 = Some j_run ->
      periodic_jobset_deadline_between T_ex tasks_ex offset_ex jobs_ex
        t1 (job_abs_deadline (jobs_ex j)) j_run ->
      job_release (jobs_ex j) <= job_release (jobs_ex j_run)) ->
    ~ missed_deadline jobs_ex 1 sched j.
Proof.
  intros sched j t1 t2 Hsched Hj Hwit Ht1rel Hj_H Hcarry_free.
  eapply periodic_edf_no_deadline_miss_from_window_dbf_on_finite_horizon_auto
    with (enumT := enumT_ex); eauto.
  - exact tasks_ex_well_formed.
  - exact enumT_ex_nodup.
  - intros τ Hτ.
    destruct Hτ as [Hτ | Hτ]; subst τ; simpl; tauto.
  - intros τ Hτ.
    simpl in Hτ.
    destruct Hτ as [Hτ | [Hτ | []]]; subst τ.
    + left. reflexivity.
    + right. reflexivity.
  - exact periodic_window_dbf_test.
Qed.

Theorem periodic_example_edf_schedulable_by_window_dbf_auto :
  forall sched,
    scheduler_rel
      (edf_scheduler
         (enum_candidates_of
            (enum_periodic_jobs_upto T_ex tasks_ex offset_ex jobs_ex H_ex enumT_ex codec_ex)))
      jobs_ex 1 sched ->
    (forall j,
      periodic_jobset_upto T_ex tasks_ex offset_ex jobs_ex H_ex j ->
      job_abs_deadline (jobs_ex j) <= H_ex /\
      exists t1 t2,
        busy_window_witness sched (job_abs_deadline (jobs_ex j)) t1 t2 /\
        t1 <= job_release (jobs_ex j) /\
        (forall t j_run,
          job_release (jobs_ex j) <= t < job_abs_deadline (jobs_ex j) ->
          sched t 0 = Some j_run ->
          periodic_jobset_deadline_between T_ex tasks_ex offset_ex jobs_ex
            t1 (job_abs_deadline (jobs_ex j)) j_run ->
          job_release (jobs_ex j) <= job_release (jobs_ex j_run))) ->
    schedulable_by_on
      (periodic_jobset_upto T_ex tasks_ex offset_ex jobs_ex H_ex)
      (edf_scheduler
         (enum_candidates_of
            (enum_periodic_jobs_upto T_ex tasks_ex offset_ex jobs_ex H_ex enumT_ex codec_ex)))
      jobs_ex 1.
Proof.
  intros sched Hsched Hjob_bridge.
  eapply periodic_edf_schedulable_by_window_dbf_on_finite_horizon_auto
    with (sched := sched) (enumT := enumT_ex); eauto.
  - exact tasks_ex_well_formed.
  - exact enumT_ex_nodup.
  - intros τ Hτ.
    destruct Hτ as [Hτ | Hτ]; subst τ; simpl; tauto.
  - intros τ Hτ.
    simpl in Hτ.
    destruct Hτ as [Hτ | [Hτ | []]]; subst τ.
    + left. reflexivity.
    + right. reflexivity.
  - exact periodic_window_dbf_test.
Qed.
