From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Analysis.Uniprocessor.ProcessorDemand.
From RocqSched Require Import TaskModels.Periodic.PeriodicConcreteAnalysis.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFExtractionTypes.

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
