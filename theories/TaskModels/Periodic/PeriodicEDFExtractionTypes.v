From Stdlib Require Import List Arith Arith.PeanoNat Bool Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.

Import ListNotations.

(** Extraction-facing finite periodic task inputs.

    This layer intentionally exposes only task parameters.  Task identifiers
    are their positions in the input list, and jobs are later supplied by the
    existing canonical periodic codec. *)

Record ExtractedPeriodicTask : Type := mkExtractedPeriodicTask {
  extracted_task_cost : nat;
  extracted_task_period : nat;
  extracted_task_relative_deadline : nat
}.

Definition task_of_extracted (τ : ExtractedPeriodicTask) : Task :=
  mkTask
    τ.(extracted_task_cost)
    τ.(extracted_task_period)
    τ.(extracted_task_relative_deadline).

Definition default_extracted_periodic_task : ExtractedPeriodicTask :=
  mkExtractedPeriodicTask 1 1 1.

Definition default_periodic_task : Task :=
  task_of_extracted default_extracted_periodic_task.

Definition tasks_of_extracted_list
    (ts : list ExtractedPeriodicTask) : TaskId -> Task :=
  fun τ => task_of_extracted (nth τ ts default_extracted_periodic_task).

Definition enumT_of_extracted_list
    (ts : list ExtractedPeriodicTask) : list TaskId :=
  seq 0 (length ts).

Definition extracted_task_wf (τ : ExtractedPeriodicTask) : bool :=
  Nat.ltb 0 τ.(extracted_task_cost)
  && Nat.ltb 0 τ.(extracted_task_period)
  && Nat.ltb 0 τ.(extracted_task_relative_deadline).

Definition extracted_taskset_wf (ts : list ExtractedPeriodicTask) : bool :=
  forallb extracted_task_wf ts.

Lemma extracted_taskset_wf_forall :
  forall ts τ,
    extracted_taskset_wf ts = true ->
    In τ ts ->
    extracted_task_wf τ = true.
Proof.
  intros ts τ Hwf Hin.
  unfold extracted_taskset_wf in Hwf.
  eapply forallb_forall; eauto.
Qed.

Lemma extracted_task_wf_period_positive :
  forall τ,
    extracted_task_wf τ = true ->
    0 < task_period (task_of_extracted τ).
Proof.
  intros τ Hwf.
  unfold extracted_task_wf in Hwf.
  apply andb_true_iff in Hwf as [Hrest _].
  apply andb_true_iff in Hrest as [_ Hperiod].
  cbn.
  apply Nat.ltb_lt.
  exact Hperiod.
Qed.

Lemma extracted_task_wf_cost_positive :
  forall τ,
    extracted_task_wf τ = true ->
    0 < task_cost (task_of_extracted τ).
Proof.
  intros τ Hwf.
  unfold extracted_task_wf in Hwf.
  apply andb_true_iff in Hwf as [Hrest _].
  apply andb_true_iff in Hrest as [Hcost _].
  cbn.
  apply Nat.ltb_lt.
  exact Hcost.
Qed.

Lemma extracted_task_wf_deadline_positive :
  forall τ,
    extracted_task_wf τ = true ->
    0 < task_relative_deadline (task_of_extracted τ).
Proof.
  intros τ Hwf.
  unfold extracted_task_wf in Hwf.
  apply andb_true_iff in Hwf as [_ Hdeadline].
  cbn.
  apply Nat.ltb_lt.
  exact Hdeadline.
Qed.

Lemma enumT_of_extracted_list_nodup :
  forall ts,
    NoDup (enumT_of_extracted_list ts).
Proof.
  intros ts.
  unfold enumT_of_extracted_list.
  apply seq_NoDup.
Qed.

Lemma enumT_of_extracted_list_complete :
  forall ts τ,
    τ < length ts ->
    In τ (enumT_of_extracted_list ts).
Proof.
  intros ts τ Hlt.
  unfold enumT_of_extracted_list.
  rewrite in_seq.
  lia.
Qed.

Lemma enumT_of_extracted_list_sound :
  forall ts τ,
    In τ (enumT_of_extracted_list ts) ->
    τ < length ts.
Proof.
  intros ts τ Hin.
  unfold enumT_of_extracted_list in Hin.
  rewrite in_seq in Hin.
  lia.
Qed.

Lemma nth_in_extracted_list :
  forall ts τ,
    τ < length ts ->
    In (nth τ ts default_extracted_periodic_task) ts.
Proof.
  intros ts τ Hlt.
  apply nth_In.
  exact Hlt.
Qed.

Lemma extracted_tasks_well_formed_on_enum :
  forall ts,
    extracted_taskset_wf ts = true ->
    well_formed_periodic_tasks_on
      (fun τ => τ < length ts)
      (tasks_of_extracted_list ts).
Proof.
  intros ts Hwf τ Hτ.
  unfold tasks_of_extracted_list.
  apply extracted_task_wf_period_positive.
  eapply extracted_taskset_wf_forall.
  - exact Hwf.
  - apply nth_in_extracted_list.
    exact Hτ.
Qed.
