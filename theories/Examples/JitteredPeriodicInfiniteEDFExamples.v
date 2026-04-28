From Stdlib Require Import Arith Arith.PeanoNat Lia List.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Uniprocessor.Policies.EDF.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicCodec.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicInfiniteJobset.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicPrefixCoherence.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicEDFAnalysisEntryPoints.
From RocqSched Require Import Examples.JitteredPeriodicOffsetJitterDBFExamples.
Import ListNotations.

Section InfiniteJitteredEDFExample.

  Variable jobs_oj_ex : JobId -> Job.
  Variable codec_oj_ex :
    JitteredPeriodicCodec
      T_oj_ex tasks_oj_ex offset_oj_ex jitter_oj_ex jobs_oj_ex.

  Hypothesis jittered_nonblocking_oj_ex :
    forall j t,
      jittered_periodic_jobset
        T_oj_ex tasks_oj_ex offset_oj_ex jitter_oj_ex jobs_oj_ex j ->
      ~ blocked jobs_oj_ex j t.

  Hypothesis jittered_edf_no_carry_in_bridge_oj_ex :
    forall j,
      jittered_periodic_jobset
        T_oj_ex tasks_oj_ex offset_oj_ex jitter_oj_ex jobs_oj_ex j ->
      jittered_periodic_edf_busy_prefix_no_carry_in_bridge
        T_oj_ex tasks_oj_ex offset_oj_ex jitter_oj_ex jobs_oj_ex
        (S (job_abs_deadline (jobs_oj_ex j)))
        (generated_jittered_periodic_edf_schedule_upto
           T_oj_ex tasks_oj_ex offset_oj_ex jitter_oj_ex jobs_oj_ex
           (S (job_abs_deadline (jobs_oj_ex j))) enumT_oj_ex codec_oj_ex)
        j.

  Example jittered_periodic_infinite_edf_example_schedulable_by_window_dbf_on :
    schedulable_by_on
      (jittered_periodic_jobset
         T_oj_ex tasks_oj_ex offset_oj_ex jitter_oj_ex jobs_oj_ex)
      (edf_scheduler
         (jittered_periodic_candidates_before
            T_oj_ex tasks_oj_ex offset_oj_ex jitter_oj_ex jobs_oj_ex
            enumT_oj_ex codec_oj_ex))
      jobs_oj_ex 1.
  Proof.
    eapply jittered_periodic_edf_schedulable_by_window_dbf_on.
    - exact tasks_oj_ex_well_formed.
    - exact jittered_nonblocking_oj_ex.
    - exact enumT_oj_ex_nodup.
    - exact T_oj_ex_in_enumT_oj_ex.
    - exact in_enumT_oj_ex_implies_T_oj_ex.
    - exact jittered_edf_no_carry_in_bridge_oj_ex.
    - exact jittered_offset_jitter_window_dbf_ex.
  Qed.

End InfiniteJitteredEDFExample.
