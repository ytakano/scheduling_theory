From Stdlib Require Import List Bool Arith Arith.PeanoNat.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import TaskModels.Periodic.PeriodicConcreteAnalysis.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicConcreteAnalysis.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicEDFCertificate.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicEDFExtractionDecision.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicEDFExtractionTypes.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicOffsetWindowCutoff.

Import ListNotations.

(** Top-level checked jittered EDF certificate wrapper.

    The first jittered certificate boundary is DBF-only.  The checker validates
    the task-set well-formedness, recomputes the cutoff and critical windows,
    and then reuses the existing cutoff DBF decision. *)

Definition jittered_edf_dbf_certificate_expected_cutoff
    (ts : list ExtractedJitteredPeriodicTask) : Time :=
  extracted_jittered_offset_window_dbf_cutoff_bound ts.

Definition jittered_edf_dbf_certificate_expected_windows
    (ts : list ExtractedJitteredPeriodicTask) : list (Time * Time) :=
  critical_dbf_windows_upto
    (jittered_tasks_of_extracted_list ts)
    (jittered_offset_of_extracted_list ts)
    (jittered_enumT_of_extracted_list ts)
    (jittered_edf_dbf_certificate_expected_cutoff ts).

Definition check_jittered_edf_dbf_certificate_extracted
    (ts : list ExtractedJitteredPeriodicTask)
    (cert : JitteredEDFDbfCertificate) : bool :=
  extracted_jittered_taskset_wf ts
  && check_jittered_edf_dbf_certificate_fields
       (jittered_edf_dbf_certificate_expected_cutoff ts)
       (jittered_edf_dbf_certificate_expected_windows ts)
       cert
  && extracted_jittered_offset_window_dbf_test_by_cutoff ts.

Lemma check_jittered_edf_dbf_certificate_extracted_fields :
  forall ts cert,
    check_jittered_edf_dbf_certificate_extracted ts cert = true ->
    extracted_jittered_taskset_wf ts = true
    /\ check_jittered_edf_dbf_certificate_fields
         (jittered_edf_dbf_certificate_expected_cutoff ts)
         (jittered_edf_dbf_certificate_expected_windows ts)
         cert = true
    /\ extracted_jittered_offset_window_dbf_test_by_cutoff ts = true.
Proof.
  intros ts cert Hcheck.
  unfold check_jittered_edf_dbf_certificate_extracted in Hcheck.
  apply andb_true_iff in Hcheck as [Hrest Hdbf].
  apply andb_true_iff in Hrest as [Hwf Hfields].
  repeat split; assumption.
Qed.

Lemma check_jittered_edf_dbf_certificate_extracted_certificate_fields :
  forall ts cert,
    check_jittered_edf_dbf_certificate_extracted ts cert = true ->
    cert.(jedf_cutoff) =
      jittered_edf_dbf_certificate_expected_cutoff ts
    /\ cert.(jedf_checked_windows) =
      jittered_edf_dbf_certificate_expected_windows ts
    /\ cert.(jedf_all_windows_checked) = true.
Proof.
  intros ts cert Hcheck.
  destruct
    (check_jittered_edf_dbf_certificate_extracted_fields ts cert Hcheck)
    as [_ [Hfields _]].
  apply check_jittered_edf_dbf_certificate_fields_sound.
  exact Hfields.
Qed.

Theorem check_jittered_edf_dbf_certificate_extracted_sound :
  forall ts cert,
    check_jittered_edf_dbf_certificate_extracted ts cert = true ->
    extracted_jittered_offset_window_dbf_ok_global ts.
Proof.
  intros ts cert Hcheck.
  destruct
    (check_jittered_edf_dbf_certificate_extracted_fields ts cert Hcheck)
    as [Hwf [_ Hdbf]].
  eapply extracted_jittered_offset_window_dbf_test_by_cutoff_sound; eauto.
Qed.
