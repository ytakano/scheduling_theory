From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicConcreteAnalysis.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicEDFExtractionTypes.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicOffsetWindowCutoff.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicWindowDemandBound.

Import ListNotations.

(** Executable EDF schedulability decision for extracted jittered-periodic
    task sets.  The computation is the conservative cutoff window-DBF test
    guarded by an extraction-facing well-formedness check. *)

Definition extracted_jittered_offset_window_dbf_cutoff_bound
    (ts : list ExtractedJitteredPeriodicTask) : Time :=
  jittered_offset_window_dbf_cutoff_bound
    (jittered_tasks_of_extracted_list ts)
    (jittered_offset_of_extracted_list ts)
    (jitter_of_extracted_list ts)
    (jittered_enumT_of_extracted_list ts).

Definition extracted_jittered_offset_window_dbf_test_by_cutoff
    (ts : list ExtractedJitteredPeriodicTask) : bool :=
  jittered_offset_window_dbf_test_by_cutoff
    (jittered_tasks_of_extracted_list ts)
    (jittered_offset_of_extracted_list ts)
    (jitter_of_extracted_list ts)
    (jittered_enumT_of_extracted_list ts).

Definition extracted_jittered_offset_window_dbf_counterexample_by_cutoff
    (ts : list ExtractedJitteredPeriodicTask) : option (Time * Time) :=
  first_jittered_window_dbf_overload_upto
    (jittered_tasks_of_extracted_list ts)
    (jittered_offset_of_extracted_list ts)
    (jitter_of_extracted_list ts)
    (jittered_enumT_of_extracted_list ts)
    (extracted_jittered_offset_window_dbf_cutoff_bound ts).

Definition extracted_jittered_offset_window_dbf_decide_by_cutoff
    (ts : list ExtractedJitteredPeriodicTask) : bool :=
  extracted_jittered_taskset_wf ts
  && extracted_jittered_offset_window_dbf_test_by_cutoff ts.

Definition jittered_periodic_offset_window_schedulability_cutoff_bound
    (ts : list ExtractedJitteredPeriodicTask) : Time :=
  extracted_jittered_offset_window_dbf_cutoff_bound ts.

Definition jittered_periodic_offset_window_schedulability_decide
    (ts : list ExtractedJitteredPeriodicTask) : bool :=
  extracted_jittered_offset_window_dbf_decide_by_cutoff ts.

Definition jittered_periodic_offset_window_schedulability_counterexample
    (ts : list ExtractedJitteredPeriodicTask) : option (Time * Time) :=
  extracted_jittered_offset_window_dbf_counterexample_by_cutoff ts.

Definition extracted_jittered_offset_window_dbf_ok_global
    (ts : list ExtractedJitteredPeriodicTask) : Prop :=
  forall t1 t2,
    t1 <= t2 ->
    taskset_jittered_periodic_dbf_window
      (jittered_tasks_of_extracted_list ts)
      (jittered_offset_of_extracted_list ts)
      (jitter_of_extracted_list ts)
      (jittered_enumT_of_extracted_list ts)
      t1 t2 <= t2 - t1.

Theorem extracted_jittered_offset_window_dbf_test_by_cutoff_sound :
  forall ts,
    extracted_jittered_taskset_wf ts = true ->
    extracted_jittered_offset_window_dbf_test_by_cutoff ts = true ->
    extracted_jittered_offset_window_dbf_ok_global ts.
Proof.
  intros ts Hwf Htest.
  unfold extracted_jittered_offset_window_dbf_ok_global.
  intros t1 t2 Hle12.
  unfold extracted_jittered_offset_window_dbf_test_by_cutoff in Htest.
  eapply jittered_offset_window_dbf_check_by_cutoff.
  - intros τ Hin.
    eapply extracted_jittered_tasks_well_formed_on_enum.
    + exact Hwf.
    + apply jittered_enumT_of_extracted_list_sound.
      exact Hin.
  - exact Htest.
  - exact Hle12.
Qed.

Lemma extracted_jittered_offset_window_dbf_decide_by_cutoff_true_ok :
  forall ts,
    extracted_jittered_offset_window_dbf_decide_by_cutoff ts = true ->
    extracted_jittered_offset_window_dbf_ok_global ts.
Proof.
  intros ts Hdec.
  unfold extracted_jittered_offset_window_dbf_decide_by_cutoff in Hdec.
  apply andb_true_iff in Hdec.
  destruct Hdec as [Hwf Htest].
  eapply extracted_jittered_offset_window_dbf_test_by_cutoff_sound; eauto.
Qed.

Lemma extracted_jittered_offset_window_dbf_counterexample_by_cutoff_sound :
  forall ts t1 t2,
    extracted_jittered_offset_window_dbf_counterexample_by_cutoff ts =
    Some (t1, t2) ->
    t2 - t1 <
    taskset_jittered_periodic_dbf_window
      (jittered_tasks_of_extracted_list ts)
      (jittered_offset_of_extracted_list ts)
      (jitter_of_extracted_list ts)
      (jittered_enumT_of_extracted_list ts)
      t1 t2.
Proof.
  intros ts t1 t2 Hcex.
  unfold extracted_jittered_offset_window_dbf_counterexample_by_cutoff in Hcex.
  eapply first_jittered_window_dbf_overload_upto_some.
  exact Hcex.
Qed.

Lemma jittered_periodic_offset_window_schedulability_decide_true_ok :
  forall ts,
    jittered_periodic_offset_window_schedulability_decide ts = true ->
    extracted_jittered_offset_window_dbf_ok_global ts.
Proof.
  intros ts Hdec.
  unfold jittered_periodic_offset_window_schedulability_decide in Hdec.
  apply extracted_jittered_offset_window_dbf_decide_by_cutoff_true_ok.
  exact Hdec.
Qed.

Lemma jittered_periodic_offset_window_schedulability_counterexample_sound :
  forall ts t1 t2,
    jittered_periodic_offset_window_schedulability_counterexample ts =
    Some (t1, t2) ->
    t2 - t1 <
    taskset_jittered_periodic_dbf_window
      (jittered_tasks_of_extracted_list ts)
      (jittered_offset_of_extracted_list ts)
      (jitter_of_extracted_list ts)
      (jittered_enumT_of_extracted_list ts)
      t1 t2.
Proof.
  intros ts t1 t2 Hcex.
  unfold jittered_periodic_offset_window_schedulability_counterexample in Hcex.
  apply extracted_jittered_offset_window_dbf_counterexample_by_cutoff_sound.
  exact Hcex.
Qed.
