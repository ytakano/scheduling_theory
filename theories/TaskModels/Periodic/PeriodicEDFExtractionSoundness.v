From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Analysis.Uniprocessor.EDFProcessorDemand.
From RocqSched Require Import TaskModels.Periodic.PeriodicCodec.
From RocqSched Require Import TaskModels.Periodic.PeriodicConcreteAnalysis.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFExtractionDecision.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFExtractionTypes.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFInfiniteBridge.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFPrefixCoherence.
From RocqSched Require Import TaskModels.Periodic.PeriodicInfinite.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import Uniprocessor.Policies.EDF.

Import ListNotations.

(** Semantic wrapper for the extraction-facing checker.

    The executable function proves the classical DBF condition.  The final EDF
    schedulability theorem intentionally keeps the no-carry-in bridge explicit,
    matching the existing periodic EDF public interface and avoiding runtime
    details in this extraction layer. *)

Definition extracted_task_scope (ts : list ExtractedPeriodicTask) : TaskId -> Prop :=
  fun τ => τ < length ts.

Definition extracted_periodic_tasks (ts : list ExtractedPeriodicTask) : TaskId -> Task :=
  tasks_of_extracted_list ts.

Definition extracted_periodic_jobs (ts : list ExtractedPeriodicTask) : JobId -> Job :=
  canonical_periodic_jobs_from_enumT
    (extracted_periodic_tasks ts)
    (fun _ => 0)
    (enumT_of_extracted_list ts).

Lemma extracted_enum_complete :
  forall ts τ,
    extracted_task_scope ts τ ->
    In τ (enumT_of_extracted_list ts).
Proof.
  intros ts τ Hτ.
  apply enumT_of_extracted_list_complete.
  exact Hτ.
Qed.

Lemma extracted_enum_sound :
  forall ts τ,
    In τ (enumT_of_extracted_list ts) ->
    extracted_task_scope ts τ.
Proof.
  intros ts τ Hin.
  apply enumT_of_extracted_list_sound.
  exact Hin.
Qed.

Lemma extracted_zero_offset :
  forall ts τ,
    In τ (enumT_of_extracted_list ts) ->
    (fun _ : TaskId => 0) τ = 0.
Proof.
  intros. reflexivity.
Qed.

Lemma extracted_periodic_nonblocking :
  forall ts j t,
    periodic_jobset
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      j ->
    ~ blocked (extracted_periodic_jobs ts) j t.
Proof.
  intros ts j t _ Hblocked.
  unfold blocked in Hblocked.
  unfold extracted_periodic_jobs, canonical_periodic_jobs_from_enumT in Hblocked.
  destruct (decode_job_id_from_enumT (enumT_of_extracted_list ts) j) as [pos k].
  destruct (nth_error (enumT_of_extracted_list ts) pos) as [τ|]; cbn in Hblocked;
    discriminate.
Qed.

Theorem edf_schedulability_decide_classical_dbf_sound :
  forall ts,
    edf_schedulability_decide ts = true ->
    extracted_taskset_global_dbf_ok ts.
Proof.
  apply edf_schedulability_decide_true_global_dbf_ok.
Qed.

Theorem edf_schedulability_decide_schedulable_by_on
    (ts : list ExtractedPeriodicTask)
    (codec :
      PeriodicCodec
        (extracted_task_scope ts)
        (extracted_periodic_tasks ts)
        (fun _ => 0)
        (extracted_periodic_jobs ts)) :
  extracted_taskset_wf ts = true ->
  (forall j,
    periodic_jobset
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      j ->
    periodic_edf_busy_prefix_no_carry_in_bridge
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (S (job_abs_deadline (extracted_periodic_jobs ts j)))
      (generated_periodic_edf_schedule_upto
         (extracted_task_scope ts)
         (extracted_periodic_tasks ts)
         (fun _ => 0)
         (extracted_periodic_jobs ts)
         (S (job_abs_deadline (extracted_periodic_jobs ts j)))
         (enumT_of_extracted_list ts)
         codec)
      j) ->
  edf_schedulability_decide ts = true ->
  schedulable_by_on
    (periodic_jobset
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts))
    (edf_scheduler
       (periodic_candidates_before
          (extracted_task_scope ts)
          (extracted_periodic_tasks ts)
          (fun _ => 0)
          (extracted_periodic_jobs ts)
          (enumT_of_extracted_list ts)
          codec))
    (extracted_periodic_jobs ts)
    1.
Proof.
  intros Hwf Hbridge Hdec.
  eapply periodic_edf_schedulable_by_classical_dbf_with_no_carry_in_bridge.
  - apply extracted_tasks_well_formed_on_enum.
    exact Hwf.
  - apply extracted_periodic_nonblocking.
  - apply enumT_of_extracted_list_nodup.
  - apply extracted_enum_complete.
  - apply extracted_enum_sound.
  - apply extracted_zero_offset.
  - exact Hbridge.
  - apply edf_schedulability_decide_true_global_dbf_ok.
    exact Hdec.
Qed.

Theorem edf_schedulability_decide_false_has_dbf_overload :
  forall ts,
    extracted_taskset_wf ts = true ->
    edf_schedulability_decide ts = false ->
    extracted_taskset_has_bounded_dbf_overload ts.
Proof.
  apply edf_schedulability_decide_false_overload.
Qed.
