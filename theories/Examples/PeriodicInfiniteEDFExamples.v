From Stdlib Require Import Arith Arith.PeanoNat Lia List Bool.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Analysis.Uniprocessor.ProcessorDemand.
From RocqSched Require Import Analysis.Uniprocessor.EDFProcessorDemand.
From RocqSched Require Import Uniprocessor.Policies.EDF.
From RocqSched Require Import TaskModels.Periodic.PeriodicCodec.
From RocqSched Require Import TaskModels.Periodic.PeriodicInfinite.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFAnalysisEntryPoints.
From RocqSched Require Import Examples.PeriodicExamples.
From RocqSched Require Import Examples.PeriodicProcessorDemandExamples.
Import ListNotations.

(* Example downstream client of the infinite-time periodic EDF entry points.
   This file keeps the example lightweight: the finite example task set is
   reused, while the global codec/prefix-coherence obligations are exposed as
   hypotheses. *)

Example periodic_infinite_example_dbf_test_by_cutoff :
  dbf_test_by_cutoff tasks_ex enumT_ex = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma periodic_infinite_example_classical_dbf :
  forall t,
    taskset_periodic_dbf tasks_ex enumT_ex t <= t.
Proof.
  apply dbf_check_by_cutoff.
  - exact enumT_ex_nodup.
  - intros τ Hin.
    apply tasks_ex_well_formed.
    apply in_enumT_ex_implies_T_ex.
    exact Hin.
  - exact periodic_infinite_example_dbf_test_by_cutoff.
Qed.

Section InfinitePeriodicEDFExample.

  Variable codec_inf_ex : PeriodicCodec T_ex tasks_ex offset_ex jobs_ex.

  Hypothesis busy_prefix_bridge_ex :
    forall j,
      periodic_jobset T_ex tasks_ex offset_ex jobs_ex j ->
      periodic_edf_busy_prefix_bridge
        T_ex tasks_ex offset_ex jobs_ex
        (S (job_abs_deadline (jobs_ex j)))
        (generated_periodic_edf_schedule_upto
           T_ex tasks_ex offset_ex jobs_ex
           (S (job_abs_deadline (jobs_ex j)))
           enumT_ex codec_inf_ex)
        j.

  Hypothesis periodic_window_dbf_ex :
    forall t1 t2,
      t1 <= t2 ->
      taskset_periodic_dbf_window tasks_ex offset_ex enumT_ex t1 t2 <= t2 - t1.

  Hypothesis offset_zero_ex :
    forall τ, In τ enumT_ex -> offset_ex τ = 0.

  Example periodic_infinite_example_job0_no_deadline_miss :
    ~ missed_deadline jobs_ex 1
        (generated_periodic_edf_schedule
           T_ex tasks_ex offset_ex jobs_ex enumT_ex codec_inf_ex)
        0.
  Proof.
    apply periodic_edf_no_deadline_miss_from_window_dbf.
    - exact tasks_ex_well_formed.
    - exact enumT_ex_nodup.
    - exact T_ex_in_enumT_ex.
    - exact in_enumT_ex_implies_T_ex.
    - unfold periodic_jobset, T_ex.
      split.
      + left. reflexivity.
      + exact generated_job0_ex.
    - apply busy_prefix_bridge_ex.
      unfold periodic_jobset, T_ex.
      split.
      + left. reflexivity.
      + exact generated_job0_ex.
    - exact periodic_window_dbf_ex.
  Qed.

  Example periodic_infinite_example_schedulable_by_window_dbf_on :
    schedulable_by_on
      (periodic_jobset T_ex tasks_ex offset_ex jobs_ex)
      (edf_scheduler
         (periodic_candidates_before
            T_ex tasks_ex offset_ex jobs_ex enumT_ex codec_inf_ex))
      jobs_ex 1.
  Proof.
    eapply periodic_edf_schedulable_by_on.
    1: exact tasks_ex_well_formed.
    1: exact enumT_ex_nodup.
    1: exact T_ex_in_enumT_ex.
    1: exact in_enumT_ex_implies_T_ex.
    1: apply busy_prefix_bridge_ex.
    1: exact periodic_window_dbf_ex.
  Qed.

  Example periodic_infinite_example_schedulable_by_classical_dbf_on :
    schedulable_by_on
      (periodic_jobset T_ex tasks_ex offset_ex jobs_ex)
      (edf_scheduler
         (periodic_candidates_before
            T_ex tasks_ex offset_ex jobs_ex enumT_ex codec_inf_ex))
      jobs_ex 1.
  Proof.
    eapply periodic_edf_schedulable_by_classical_dbf_on.
    1: exact tasks_ex_well_formed.
    1: exact enumT_ex_nodup.
    1: exact T_ex_in_enumT_ex.
    1: exact in_enumT_ex_implies_T_ex.
    1: exact offset_zero_ex.
    1: apply busy_prefix_bridge_ex.
    1: exact periodic_infinite_example_classical_dbf.
  Qed.

  Example periodic_infinite_example_job0_no_deadline_miss_by_classical_dbf :
    ~ missed_deadline jobs_ex 1
        (generated_periodic_edf_schedule
           T_ex tasks_ex offset_ex jobs_ex enumT_ex codec_inf_ex)
        0.
  Proof.
    apply periodic_edf_no_deadline_miss_from_classical_dbf.
    - exact tasks_ex_well_formed.
    - exact enumT_ex_nodup.
    - exact T_ex_in_enumT_ex.
    - exact in_enumT_ex_implies_T_ex.
    - exact offset_zero_ex.
    - unfold periodic_jobset, T_ex.
      split.
      + left. reflexivity.
      + exact generated_job0_ex.
    - apply busy_prefix_bridge_ex.
      unfold periodic_jobset, T_ex.
      split.
      + left. reflexivity.
      + exact generated_job0_ex.
    - exact periodic_infinite_example_classical_dbf.
  Qed.

End InfinitePeriodicEDFExample.
