From Stdlib Require Import Arith Arith.PeanoNat Lia List Bool.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Analysis.Uniprocessor.ProcessorDemand.
From RocqSched Require Import Uniprocessor.Policies.LLF.
From RocqSched Require Import TaskModels.Periodic.PeriodicCodec.
From RocqSched Require Import TaskModels.Periodic.PeriodicInfinite.
From RocqSched Require Import TaskModels.Periodic.PeriodicFiniteHorizon.
From RocqSched Require Import TaskModels.Periodic.PeriodicLLFAnalysisEntryPoints.
From RocqSched Require Import Examples.PeriodicExamples.
From RocqSched Require Import Examples.PeriodicProcessorDemandExamples.
Import ListNotations.

Section InfinitePeriodicLLFExample.

  Variable codec_inf_ex : PeriodicCodec T_ex tasks_ex offset_ex jobs_ex.

  Hypothesis busy_prefix_bridge_ex :
    forall H j,
      periodic_jobset_upto
        T_ex tasks_ex offset_ex jobs_ex H j ->
      job_abs_deadline (jobs_ex j) <= H /\
      exists t1 t2,
        busy_prefix_witness
          (generated_periodic_edf_schedule_upto
             T_ex tasks_ex offset_ex jobs_ex H enumT_ex codec_inf_ex)
          (job_abs_deadline (jobs_ex j)) t1 t2 /\
        periodic_edf_busy_prefix_bridge
          T_ex tasks_ex offset_ex jobs_ex
          H
          (generated_periodic_edf_schedule_upto
             T_ex tasks_ex offset_ex jobs_ex H enumT_ex codec_inf_ex)
          j.

  Hypothesis periodic_window_dbf_ex :
    forall t1 t2,
      t1 <= t2 ->
      taskset_periodic_dbf_window tasks_ex offset_ex enumT_ex t1 t2 <= t2 - t1.

  Hypothesis offset_zero_ex :
    forall τ, In τ enumT_ex -> offset_ex τ = 0.

  Hypothesis periodic_classical_dbf_ex :
    forall t,
      taskset_periodic_dbf tasks_ex enumT_ex t <= t.

  Example periodic_infinite_llf_example_job0_no_deadline_miss :
    ~ missed_deadline jobs_ex 1
        (generated_periodic_llf_schedule
           T_ex tasks_ex offset_ex jobs_ex enumT_ex codec_inf_ex)
        0.
  Proof.
    apply periodic_llf_no_deadline_miss_from_window_dbf.
    - exact tasks_ex_well_formed.
    - exact enumT_ex_nodup.
    - exact T_ex_in_enumT_ex.
    - exact in_enumT_ex_implies_T_ex.
    - unfold periodic_jobset, T_ex.
      split.
      + left. reflexivity.
      + exact generated_job0_ex.
    - exact busy_prefix_bridge_ex.
    - exact periodic_window_dbf_ex.
  Qed.

  Example periodic_infinite_llf_example_schedulable_by_classical_dbf_on :
    schedulable_by_on
      (periodic_jobset T_ex tasks_ex offset_ex jobs_ex)
      (llf_scheduler
         (periodic_candidates_before
            T_ex tasks_ex offset_ex jobs_ex enumT_ex codec_inf_ex))
      jobs_ex 1.
  Proof.
    eapply periodic_llf_schedulable_by_on.
    1: exact tasks_ex_well_formed.
    1: exact enumT_ex_nodup.
    1: exact T_ex_in_enumT_ex.
    1: exact in_enumT_ex_implies_T_ex.
    1: exact offset_zero_ex.
    1: exact busy_prefix_bridge_ex.
    1: exact periodic_classical_dbf_ex.
  Qed.

  Example periodic_infinite_llf_example_job0_no_deadline_miss_by_classical_dbf :
    ~ missed_deadline jobs_ex 1
        (generated_periodic_llf_schedule
           T_ex tasks_ex offset_ex jobs_ex enumT_ex codec_inf_ex)
        0.
  Proof.
    apply periodic_llf_no_deadline_miss_from_classical_dbf.
    - exact tasks_ex_well_formed.
    - exact enumT_ex_nodup.
    - exact T_ex_in_enumT_ex.
    - exact in_enumT_ex_implies_T_ex.
    - exact offset_zero_ex.
    - unfold periodic_jobset, T_ex.
      split.
      + left. reflexivity.
      + exact generated_job0_ex.
    - exact busy_prefix_bridge_ex.
    - exact periodic_classical_dbf_ex.
  Qed.

  Example periodic_infinite_llf_example_schedulable_by_window_dbf_on :
    schedulable_by_on
      (periodic_jobset T_ex tasks_ex offset_ex jobs_ex)
      (llf_scheduler
         (periodic_candidates_before
            T_ex tasks_ex offset_ex jobs_ex enumT_ex codec_inf_ex))
      jobs_ex 1.
  Proof.
    eapply periodic_llf_schedulable_by_window_dbf_on; eauto.
    - exact tasks_ex_well_formed.
    - exact enumT_ex_nodup.
    - exact T_ex_in_enumT_ex.
    - exact in_enumT_ex_implies_T_ex.
  Qed.

End InfinitePeriodicLLFExample.
