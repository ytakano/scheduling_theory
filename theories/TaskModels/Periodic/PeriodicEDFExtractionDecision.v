From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Analysis.Uniprocessor.ProcessorDemand.
From RocqSched Require Import TaskModels.Periodic.PeriodicConcreteAnalysis.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFExtractionTypes.
From RocqSched Require Import TaskModels.Periodic.PeriodicOffsetWindowCutoff.
From RocqSched Require Import TaskModels.Periodic.PeriodicWindowDemandBound.

Import ListNotations.

(** Executable EDF schedulability decision for finite zero-offset periodic
    task sets.  The computation is the classical bounded DBF test guarded by
    an extraction-facing well-formedness check. *)

Definition extracted_taskset_dbf_test (ts : list ExtractedPeriodicTask) : bool :=
  dbf_test_by_cutoff
    (tasks_of_extracted_list ts)
    (enumT_of_extracted_list ts).

Definition edf_schedulability_decide
    (ts : list ExtractedPeriodicTask) : bool :=
  extracted_taskset_wf ts && extracted_taskset_dbf_test ts.

Definition edf_schedulability_counterexample
    (ts : list ExtractedPeriodicTask) : option Time :=
  first_dbf_overload_upto
    (tasks_of_extracted_list ts)
    (enumT_of_extracted_list ts)
    (scalar_dbf_cutoff_bound
       (tasks_of_extracted_list ts)
       (enumT_of_extracted_list ts)).

Definition extracted_offset_window_dbf_test_upto
    (ts : list ExtractedPeriodicTask)
    (H : Time) : bool :=
  window_dbf_test_upto
    (tasks_of_extracted_list ts)
    (offset_of_extracted_list ts)
    (enumT_of_extracted_list ts)
    H.

Definition extracted_offset_window_dbf_counterexample
    (ts : list ExtractedPeriodicTask)
    (H : Time) : option (Time * Time) :=
  first_window_dbf_overload_upto
    (tasks_of_extracted_list ts)
    (offset_of_extracted_list ts)
    (enumT_of_extracted_list ts)
    H.

Definition extracted_offset_window_dbf_decide
    (ts : list ExtractedPeriodicTask)
    (H : Time) : bool :=
  extracted_taskset_wf ts && extracted_offset_window_dbf_test_upto ts H.

Definition extracted_offset_window_dbf_cutoff_bound
    (ts : list ExtractedPeriodicTask) : Time :=
  offset_window_dbf_cutoff_bound
    (tasks_of_extracted_list ts)
    (offset_of_extracted_list ts)
    (enumT_of_extracted_list ts).

Definition extracted_offset_window_dbf_test_by_cutoff
    (ts : list ExtractedPeriodicTask) : bool :=
  offset_window_dbf_test_by_cutoff
    (tasks_of_extracted_list ts)
    (offset_of_extracted_list ts)
    (enumT_of_extracted_list ts).

Definition extracted_offset_window_dbf_counterexample_by_cutoff
    (ts : list ExtractedPeriodicTask) : option (Time * Time) :=
  extracted_offset_window_dbf_counterexample
    ts
    (extracted_offset_window_dbf_cutoff_bound ts).

Definition extracted_offset_window_dbf_decide_by_cutoff
    (ts : list ExtractedPeriodicTask) : bool :=
  extracted_taskset_wf ts && extracted_offset_window_dbf_test_by_cutoff ts.

Definition extracted_taskset_global_dbf_ok
    (ts : list ExtractedPeriodicTask) : Prop :=
  forall t,
    taskset_periodic_dbf
      (tasks_of_extracted_list ts)
      (enumT_of_extracted_list ts)
      t <= t.

Definition extracted_taskset_has_bounded_dbf_overload
    (ts : list ExtractedPeriodicTask) : Prop :=
  exists t,
    In t
      (critical_dbf_points_upto
         (tasks_of_extracted_list ts)
         (fun _ => 0)
         (enumT_of_extracted_list ts)
         (scalar_dbf_cutoff_bound
            (tasks_of_extracted_list ts)
            (enumT_of_extracted_list ts)))
    /\
    t <
    taskset_periodic_dbf
      (tasks_of_extracted_list ts)
      (enumT_of_extracted_list ts)
      t.

Definition extracted_offset_window_dbf_ok_upto
    (ts : list ExtractedPeriodicTask)
    (H : Time) : Prop :=
  forall t1 t2,
    t1 <= t2 ->
    t2 <= H ->
    taskset_periodic_dbf_window
      (tasks_of_extracted_list ts)
      (offset_of_extracted_list ts)
      (enumT_of_extracted_list ts)
      t1 t2 <= t2 - t1.

Definition extracted_offset_window_dbf_ok_global
    (ts : list ExtractedPeriodicTask) : Prop :=
  forall t1 t2,
    t1 <= t2 ->
    taskset_periodic_dbf_window
      (tasks_of_extracted_list ts)
      (offset_of_extracted_list ts)
      (enumT_of_extracted_list ts)
      t1 t2 <= t2 - t1.

Lemma extracted_taskset_dbf_test_sound :
  forall ts,
    extracted_taskset_wf ts = true ->
    extracted_taskset_dbf_test ts = true ->
    extracted_taskset_global_dbf_ok ts.
Proof.
  intros ts Hwf Htest.
  unfold extracted_taskset_global_dbf_ok.
  intros t.
  unfold extracted_taskset_dbf_test in Htest.
  eapply dbf_check_by_cutoff.
  - apply enumT_of_extracted_list_nodup.
  - intros τ Hin.
    eapply extracted_tasks_well_formed_on_enum.
    + exact Hwf.
    + apply enumT_of_extracted_list_sound.
      exact Hin.
  - exact Htest.
Qed.

Lemma edf_schedulability_decide_true_global_dbf_ok :
  forall ts,
    edf_schedulability_decide ts = true ->
    extracted_taskset_global_dbf_ok ts.
Proof.
  intros ts Hdec.
  unfold edf_schedulability_decide in Hdec.
  apply andb_true_iff in Hdec.
  destruct Hdec as [Hwf Htest].
  eapply extracted_taskset_dbf_test_sound; eauto.
Qed.

Lemma extracted_taskset_dbf_test_false_overload :
  forall ts,
    extracted_taskset_dbf_test ts = false ->
    extracted_taskset_has_bounded_dbf_overload ts.
Proof.
  intros ts Htest.
  unfold extracted_taskset_has_bounded_dbf_overload.
  unfold extracted_taskset_dbf_test in Htest.
  apply dbf_test_upto_false_overload.
  exact Htest.
Qed.

Lemma edf_schedulability_decide_false_overload :
  forall ts,
    extracted_taskset_wf ts = true ->
    edf_schedulability_decide ts = false ->
    extracted_taskset_has_bounded_dbf_overload ts.
Proof.
  intros ts Hwf Hdec.
  unfold edf_schedulability_decide in Hdec.
  rewrite Hwf in Hdec.
  simpl in Hdec.
  apply extracted_taskset_dbf_test_false_overload.
  exact Hdec.
Qed.

Lemma edf_schedulability_counterexample_sound :
  forall ts t,
    edf_schedulability_counterexample ts = Some t ->
    t <
    taskset_periodic_dbf
      (tasks_of_extracted_list ts)
      (enumT_of_extracted_list ts)
      t.
Proof.
  intros ts t Hcex.
  unfold edf_schedulability_counterexample in Hcex.
  apply first_dbf_overload_upto_some in Hcex.
  exact (proj2 Hcex).
Qed.

Theorem extracted_offset_window_dbf_test_upto_sound :
  forall ts H,
    extracted_taskset_wf ts = true ->
    extracted_offset_window_dbf_test_upto ts H = true ->
    extracted_offset_window_dbf_ok_upto ts H.
Proof.
  intros ts H _Hwf Htest.
  unfold extracted_offset_window_dbf_ok_upto.
  intros t1 t2 Hle12 Hle2H.
  unfold extracted_offset_window_dbf_test_upto in Htest.
  eapply window_dbf_test_upto_true_implies_bounded_window_dbf; eauto.
Qed.

Lemma extracted_offset_window_dbf_decide_true_ok :
  forall ts H,
    extracted_offset_window_dbf_decide ts H = true ->
    extracted_offset_window_dbf_ok_upto ts H.
Proof.
  intros ts H Hdec.
  unfold extracted_offset_window_dbf_decide in Hdec.
  apply andb_true_iff in Hdec.
  destruct Hdec as [Hwf Htest].
  eapply extracted_offset_window_dbf_test_upto_sound; eauto.
Qed.

Lemma extracted_offset_window_dbf_counterexample_sound :
  forall ts H t1 t2,
    extracted_offset_window_dbf_counterexample ts H = Some (t1, t2) ->
    t2 - t1 <
    taskset_periodic_dbf_window
      (tasks_of_extracted_list ts)
      (offset_of_extracted_list ts)
      (enumT_of_extracted_list ts)
      t1 t2.
Proof.
  intros ts H t1 t2 Hcex.
  unfold extracted_offset_window_dbf_counterexample in Hcex.
  eapply first_window_dbf_overload_upto_some.
  exact Hcex.
Qed.

Theorem extracted_offset_window_dbf_test_by_cutoff_sound :
  forall ts,
    extracted_taskset_wf ts = true ->
    extracted_offset_window_dbf_test_by_cutoff ts = true ->
    extracted_offset_window_dbf_ok_global ts.
Proof.
  intros ts Hwf Htest.
  unfold extracted_offset_window_dbf_ok_global.
  intros t1 t2 Hle12.
  unfold extracted_offset_window_dbf_test_by_cutoff in Htest.
  eapply offset_window_dbf_check_by_cutoff.
  - intros τ Hin.
    eapply extracted_tasks_well_formed_on_enum.
    + exact Hwf.
    + apply enumT_of_extracted_list_sound.
      exact Hin.
  - exact Htest.
  - exact Hle12.
Qed.

Lemma extracted_offset_window_dbf_decide_by_cutoff_true_ok :
  forall ts,
    extracted_offset_window_dbf_decide_by_cutoff ts = true ->
    extracted_offset_window_dbf_ok_global ts.
Proof.
  intros ts Hdec.
  unfold extracted_offset_window_dbf_decide_by_cutoff in Hdec.
  apply andb_true_iff in Hdec.
  destruct Hdec as [Hwf Htest].
  eapply extracted_offset_window_dbf_test_by_cutoff_sound; eauto.
Qed.

Lemma extracted_offset_window_dbf_counterexample_by_cutoff_sound :
  forall ts t1 t2,
    extracted_offset_window_dbf_counterexample_by_cutoff ts = Some (t1, t2) ->
    t2 - t1 <
    taskset_periodic_dbf_window
      (tasks_of_extracted_list ts)
      (offset_of_extracted_list ts)
      (enumT_of_extracted_list ts)
      t1 t2.
Proof.
  intros ts t1 t2 Hcex.
  unfold extracted_offset_window_dbf_counterexample_by_cutoff in Hcex.
  eapply extracted_offset_window_dbf_counterexample_sound.
  exact Hcex.
Qed.

Theorem edf_schedulability_decide_iff_global_dbf :
  forall ts,
    extracted_taskset_wf ts = true ->
    edf_schedulability_decide ts = true <->
    extracted_taskset_global_dbf_ok ts.
Proof.
  intros ts Hwf.
  split.
  - apply edf_schedulability_decide_true_global_dbf_ok.
  - intros Hdbf.
    unfold edf_schedulability_decide.
    rewrite Hwf.
    simpl.
    unfold extracted_taskset_dbf_test.
    unfold dbf_test_by_cutoff, dbf_test_upto.
    apply forallb_forall.
    intros t _.
    apply Nat.leb_le.
    exact (Hdbf t).
Qed.
