From Stdlib Require Import List Arith Arith.PeanoNat Bool Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFExtractionTypes.

Import ListNotations.

(** Extraction-facing finite jittered-periodic task inputs.

    This layer exposes only task-generation metadata.  Task identifiers are
    positions in the input list; actual job releases are supplied by the
    semantic job model, not reconstructed here. *)

Record ExtractedJitteredPeriodicTask : Type := mkExtractedJitteredPeriodicTask {
  ejp_cost : nat;
  ejp_period : nat;
  ejp_relative_deadline : nat;
  ejp_offset : nat;
  ejp_release_jitter : nat
}.

Definition task_of_extracted_jittered
    (τ : ExtractedJitteredPeriodicTask) : Task :=
  mkTask τ.(ejp_cost) τ.(ejp_period) τ.(ejp_relative_deadline).

Definition default_extracted_jittered_periodic_task
    : ExtractedJitteredPeriodicTask :=
  mkExtractedJitteredPeriodicTask 1 1 1 0 0.

Definition extracted_periodic_as_jittered_zero_jitter
    (τ : ExtractedPeriodicTask) : ExtractedJitteredPeriodicTask :=
  mkExtractedJitteredPeriodicTask
    τ.(extracted_task_cost)
    τ.(extracted_task_period)
    τ.(extracted_task_relative_deadline)
    τ.(extracted_task_offset)
    0.

Definition jittered_tasks_of_extracted_list
    (ts : list ExtractedJitteredPeriodicTask) : TaskId -> Task :=
  fun τ => task_of_extracted_jittered
             (nth τ ts default_extracted_jittered_periodic_task).

Definition jittered_offset_of_extracted_list
    (ts : list ExtractedJitteredPeriodicTask) : TaskId -> Time :=
  fun τ => ejp_offset (nth τ ts default_extracted_jittered_periodic_task).

Definition jitter_of_extracted_list
    (ts : list ExtractedJitteredPeriodicTask) : TaskId -> Time :=
  fun τ => ejp_release_jitter
             (nth τ ts default_extracted_jittered_periodic_task).

Definition jittered_enumT_of_extracted_list
    (ts : list ExtractedJitteredPeriodicTask) : list TaskId :=
  seq 0 (length ts).

Definition extracted_jittered_task_wf
    (τ : ExtractedJitteredPeriodicTask) : bool :=
  Nat.ltb 0 τ.(ejp_cost)
  && Nat.ltb 0 τ.(ejp_period)
  && Nat.ltb 0 τ.(ejp_relative_deadline).

Definition extracted_jittered_taskset_wf
    (ts : list ExtractedJitteredPeriodicTask) : bool :=
  forallb extracted_jittered_task_wf ts.

Lemma extracted_jittered_taskset_wf_forall :
  forall ts τ,
    extracted_jittered_taskset_wf ts = true ->
    In τ ts ->
    extracted_jittered_task_wf τ = true.
Proof.
  intros ts τ Hwf Hin.
  unfold extracted_jittered_taskset_wf in Hwf.
  eapply forallb_forall; eauto.
Qed.

Lemma extracted_jittered_task_wf_period_positive :
  forall τ,
    extracted_jittered_task_wf τ = true ->
    0 < task_period (task_of_extracted_jittered τ).
Proof.
  intros τ Hwf.
  unfold extracted_jittered_task_wf in Hwf.
  apply andb_true_iff in Hwf as [Hrest _].
  apply andb_true_iff in Hrest as [_ Hperiod].
  cbn.
  apply Nat.ltb_lt.
  exact Hperiod.
Qed.

Lemma extracted_jittered_task_wf_cost_positive :
  forall τ,
    extracted_jittered_task_wf τ = true ->
    0 < task_cost (task_of_extracted_jittered τ).
Proof.
  intros τ Hwf.
  unfold extracted_jittered_task_wf in Hwf.
  apply andb_true_iff in Hwf as [Hrest _].
  apply andb_true_iff in Hrest as [Hcost _].
  cbn.
  apply Nat.ltb_lt.
  exact Hcost.
Qed.

Lemma extracted_jittered_task_wf_deadline_positive :
  forall τ,
    extracted_jittered_task_wf τ = true ->
    0 < task_relative_deadline (task_of_extracted_jittered τ).
Proof.
  intros τ Hwf.
  unfold extracted_jittered_task_wf in Hwf.
  apply andb_true_iff in Hwf as [_ Hdeadline].
  cbn.
  apply Nat.ltb_lt.
  exact Hdeadline.
Qed.

Lemma jittered_enumT_of_extracted_list_nodup :
  forall ts,
    NoDup (jittered_enumT_of_extracted_list ts).
Proof.
  intros ts.
  unfold jittered_enumT_of_extracted_list.
  apply seq_NoDup.
Qed.

Lemma jittered_enumT_of_extracted_list_complete :
  forall ts τ,
    τ < length ts ->
    In τ (jittered_enumT_of_extracted_list ts).
Proof.
  intros ts τ Hlt.
  unfold jittered_enumT_of_extracted_list.
  rewrite in_seq.
  lia.
Qed.

Lemma jittered_enumT_of_extracted_list_sound :
  forall ts τ,
    In τ (jittered_enumT_of_extracted_list ts) ->
    τ < length ts.
Proof.
  intros ts τ Hin.
  unfold jittered_enumT_of_extracted_list in Hin.
  rewrite in_seq in Hin.
  lia.
Qed.

Lemma nth_in_extracted_jittered_list :
  forall ts τ,
    τ < length ts ->
    In (nth τ ts default_extracted_jittered_periodic_task) ts.
Proof.
  intros ts τ Hlt.
  apply nth_In.
  exact Hlt.
Qed.

Lemma extracted_jittered_tasks_well_formed_on_enum :
  forall ts,
    extracted_jittered_taskset_wf ts = true ->
    well_formed_periodic_tasks_on
      (fun τ => τ < length ts)
      (jittered_tasks_of_extracted_list ts).
Proof.
  intros ts Hwf τ Hτ.
  unfold jittered_tasks_of_extracted_list.
  apply extracted_jittered_task_wf_period_positive.
  eapply extracted_jittered_taskset_wf_forall.
  - exact Hwf.
  - apply nth_in_extracted_jittered_list.
    exact Hτ.
Qed.

Lemma extracted_periodic_as_jittered_zero_jitter_task :
  forall τ,
    task_of_extracted_jittered
      (extracted_periodic_as_jittered_zero_jitter τ) =
    task_of_extracted τ.
Proof.
  intros τ.
  destruct τ.
  reflexivity.
Qed.

Lemma extracted_periodic_as_jittered_zero_jitter_offset :
  forall τ,
    ejp_offset (extracted_periodic_as_jittered_zero_jitter τ) =
    extracted_task_offset τ.
Proof.
  intros τ.
  destruct τ.
  reflexivity.
Qed.

Lemma extracted_periodic_as_jittered_zero_jitter_jitter :
  forall τ,
    ejp_release_jitter (extracted_periodic_as_jittered_zero_jitter τ) = 0.
Proof.
  intros τ.
  destruct τ.
  reflexivity.
Qed.

Lemma jittered_enumT_map_periodic_zero_jitter :
  forall ts,
    jittered_enumT_of_extracted_list
      (map extracted_periodic_as_jittered_zero_jitter ts) =
    enumT_of_extracted_list ts.
Proof.
  intros ts.
  unfold jittered_enumT_of_extracted_list, enumT_of_extracted_list.
  now rewrite length_map.
Qed.

Lemma jittered_tasks_map_periodic_zero_jitter :
  forall ts τ,
    τ < length ts ->
    jittered_tasks_of_extracted_list
      (map extracted_periodic_as_jittered_zero_jitter ts) τ =
    tasks_of_extracted_list ts τ.
Proof.
  intros ts τ Hτ.
  unfold jittered_tasks_of_extracted_list, tasks_of_extracted_list.
  assert (Hnth :
    nth τ
      (map extracted_periodic_as_jittered_zero_jitter ts)
      default_extracted_jittered_periodic_task =
    nth τ
      (map extracted_periodic_as_jittered_zero_jitter ts)
      (extracted_periodic_as_jittered_zero_jitter
         default_extracted_periodic_task)).
  {
    apply nth_indep.
    now rewrite length_map.
  }
  rewrite Hnth.
  rewrite map_nth.
  apply extracted_periodic_as_jittered_zero_jitter_task.
Qed.

Lemma jittered_offsets_map_periodic_zero_jitter :
  forall ts τ,
    τ < length ts ->
    jittered_offset_of_extracted_list
      (map extracted_periodic_as_jittered_zero_jitter ts) τ =
    offset_of_extracted_list ts τ.
Proof.
  intros ts τ Hτ.
  unfold jittered_offset_of_extracted_list, offset_of_extracted_list.
  assert (Hnth :
    nth τ
      (map extracted_periodic_as_jittered_zero_jitter ts)
      default_extracted_jittered_periodic_task =
    nth τ
      (map extracted_periodic_as_jittered_zero_jitter ts)
      (extracted_periodic_as_jittered_zero_jitter
         default_extracted_periodic_task)).
  {
    apply nth_indep.
    now rewrite length_map.
  }
  rewrite Hnth.
  rewrite map_nth.
  apply extracted_periodic_as_jittered_zero_jitter_offset.
Qed.

Lemma jitter_map_periodic_zero_jitter :
  forall ts τ,
    τ < length ts ->
    jitter_of_extracted_list
      (map extracted_periodic_as_jittered_zero_jitter ts) τ = 0.
Proof.
  intros ts τ Hτ.
  unfold jitter_of_extracted_list.
  assert (Hnth :
    nth τ
      (map extracted_periodic_as_jittered_zero_jitter ts)
      default_extracted_jittered_periodic_task =
    nth τ
      (map extracted_periodic_as_jittered_zero_jitter ts)
      (extracted_periodic_as_jittered_zero_jitter
         default_extracted_periodic_task)).
  {
    apply nth_indep.
    now rewrite length_map.
  }
  rewrite Hnth.
  rewrite map_nth.
  apply extracted_periodic_as_jittered_zero_jitter_jitter.
Qed.
