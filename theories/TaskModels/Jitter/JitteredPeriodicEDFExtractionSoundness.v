From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicCodec.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicEDFExtractionDecision.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicEDFExtractionTypes.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicEDFInfiniteBridge.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicEDFWindowBridge.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicInfiniteJobset.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicPrefixCoherence.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicTasks.
From RocqSched Require Import Uniprocessor.Policies.EDF.

Import ListNotations.

(** Semantic wrapper for the extraction-facing jittered checker.

    The executable function proves the conservative jittered window-DBF
    condition.  EDF schedulability remains parameterized by the external job
    model, codec, nonblocking proof, and no-carry-in bridge. *)

Definition extracted_jittered_task_scope
    (ts : list ExtractedJitteredPeriodicTask) : TaskId -> Prop :=
  fun τ => τ < length ts.

Definition extracted_jittered_tasks
    (ts : list ExtractedJitteredPeriodicTask) : TaskId -> Task :=
  jittered_tasks_of_extracted_list ts.

Definition extracted_jittered_offsets
    (ts : list ExtractedJitteredPeriodicTask) : TaskId -> Time :=
  jittered_offset_of_extracted_list ts.

Definition extracted_jittered_release_jitter
    (ts : list ExtractedJitteredPeriodicTask) : TaskId -> Time :=
  jitter_of_extracted_list ts.

Lemma extracted_jittered_enum_complete :
  forall ts τ,
    extracted_jittered_task_scope ts τ ->
    In τ (jittered_enumT_of_extracted_list ts).
Proof.
  intros ts τ Hτ.
  apply jittered_enumT_of_extracted_list_complete.
  exact Hτ.
Qed.

Lemma extracted_jittered_enum_sound :
  forall ts τ,
    In τ (jittered_enumT_of_extracted_list ts) ->
    extracted_jittered_task_scope ts τ.
Proof.
  intros ts τ Hin.
  apply jittered_enumT_of_extracted_list_sound.
  exact Hin.
Qed.

Theorem extracted_jittered_schedulability_decide_window_dbf_sound :
  forall ts,
    extracted_jittered_offset_window_dbf_decide_by_cutoff ts = true ->
    extracted_jittered_offset_window_dbf_ok_global ts.
Proof.
  apply extracted_jittered_offset_window_dbf_decide_by_cutoff_true_ok.
Qed.

Theorem extracted_jittered_schedulability_decide_schedulable_by_on
    (ts : list ExtractedJitteredPeriodicTask)
    (jobs : JobId -> Job)
    (codec :
      JitteredPeriodicCodec
        (extracted_jittered_task_scope ts)
        (extracted_jittered_tasks ts)
        (extracted_jittered_offsets ts)
        (extracted_jittered_release_jitter ts)
        jobs) :
  extracted_jittered_taskset_wf ts = true ->
  (forall j t,
    jittered_periodic_jobset
      (extracted_jittered_task_scope ts)
      (extracted_jittered_tasks ts)
      (extracted_jittered_offsets ts)
      (extracted_jittered_release_jitter ts)
      jobs j ->
    ~ blocked jobs j t) ->
  (forall j,
    jittered_periodic_jobset
      (extracted_jittered_task_scope ts)
      (extracted_jittered_tasks ts)
      (extracted_jittered_offsets ts)
      (extracted_jittered_release_jitter ts)
      jobs j ->
    jittered_periodic_edf_busy_prefix_no_carry_in_bridge
      (extracted_jittered_task_scope ts)
      (extracted_jittered_tasks ts)
      (extracted_jittered_offsets ts)
      (extracted_jittered_release_jitter ts)
      jobs
      (S (job_abs_deadline (jobs j)))
      (generated_jittered_periodic_edf_schedule_upto
         (extracted_jittered_task_scope ts)
         (extracted_jittered_tasks ts)
         (extracted_jittered_offsets ts)
         (extracted_jittered_release_jitter ts)
         jobs
         (S (job_abs_deadline (jobs j)))
         (jittered_enumT_of_extracted_list ts)
         codec)
      j) ->
  extracted_jittered_offset_window_dbf_decide_by_cutoff ts = true ->
  schedulable_by_on
    (jittered_periodic_jobset
      (extracted_jittered_task_scope ts)
      (extracted_jittered_tasks ts)
      (extracted_jittered_offsets ts)
      (extracted_jittered_release_jitter ts)
      jobs)
    (edf_scheduler
       (jittered_periodic_candidates_before
          (extracted_jittered_task_scope ts)
          (extracted_jittered_tasks ts)
          (extracted_jittered_offsets ts)
          (extracted_jittered_release_jitter ts)
          jobs
          (jittered_enumT_of_extracted_list ts)
          codec))
    jobs
    1.
Proof.
  intros Hwf Hnonblocked Hbridge Hdec.
  eapply jittered_periodic_edf_schedulable_by_window_dbf_on.
  - apply extracted_jittered_tasks_well_formed_on_enum.
    exact Hwf.
  - exact Hnonblocked.
  - apply jittered_enumT_of_extracted_list_nodup.
  - apply extracted_jittered_enum_complete.
  - apply extracted_jittered_enum_sound.
  - exact Hbridge.
  - apply extracted_jittered_offset_window_dbf_decide_by_cutoff_true_ok.
    exact Hdec.
Qed.
