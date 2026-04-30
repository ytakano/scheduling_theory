From Stdlib Require Import List Bool Arith Arith.PeanoNat.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import TaskModels.Periodic.PeriodicConcreteAnalysis.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicConcreteAnalysis.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicCompactDBF.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicEDFCertificate.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicEDFExtractionDecision.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicEDFExtractionTypes.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicNDBF.
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

Definition jittered_edf_compact_dbf_certificate_expected_cutoff
    (ts : list ExtractedJitteredPeriodicTask) : Time :=
  extracted_jittered_offset_window_dbf_cutoff_bound ts.

Definition jittered_edf_compact_dbf_certificate_expected_basis
    (ts : list ExtractedJitteredPeriodicTask) : JitteredCompactDbfBasis :=
  jittered_reduced_compact_basis_upto
    (jittered_tasks_of_extracted_list ts)
    (jittered_offset_of_extracted_list ts)
    (jitter_of_extracted_list ts)
    (jittered_enumT_of_extracted_list ts)
    (jittered_edf_compact_dbf_certificate_expected_cutoff ts).

Definition jittered_fast_compact_basis_ndbf_test
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jitter : TaskId -> Time)
    (enumT : list TaskId)
    (basis : JitteredCompactDbfBasis) : bool :=
  forallb
    (fun w =>
       let '(t1, t2) := w in
       (t1 <=? t2)
       &&
       jittered_periodic_fast_dbf_window_ok_N_b
         tasks offset jitter enumT t1 t2)
    (jittered_compact_basis_windows basis).

Definition check_jittered_edf_dbf_certificate_extracted
    (ts : list ExtractedJitteredPeriodicTask)
    (cert : JitteredEDFDbfCertificate) : bool :=
  extracted_jittered_taskset_wf ts
  && check_jittered_edf_dbf_certificate_fields
       (jittered_edf_dbf_certificate_expected_cutoff ts)
       (jittered_edf_dbf_certificate_expected_windows ts)
       cert
  && extracted_jittered_offset_window_dbf_test_by_cutoff ts.

Definition check_jittered_edf_compact_dbf_certificate_extracted
    (ts : list ExtractedJitteredPeriodicTask)
    (cert : JitteredEDFCompactDbfCertificate) : bool :=
  extracted_jittered_taskset_wf ts
  && check_jittered_edf_compact_dbf_certificate_fields
       (jittered_edf_compact_dbf_certificate_expected_cutoff ts)
       (jittered_edf_compact_dbf_certificate_expected_basis ts)
       cert
  && jittered_fast_compact_basis_ndbf_test
       (jittered_tasks_of_extracted_list ts)
       (jittered_offset_of_extracted_list ts)
       (jitter_of_extracted_list ts)
       (jittered_enumT_of_extracted_list ts)
       cert.(jedf_compact_basis).

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

Lemma check_jittered_edf_compact_dbf_certificate_extracted_fields :
  forall ts cert,
    check_jittered_edf_compact_dbf_certificate_extracted ts cert = true ->
    extracted_jittered_taskset_wf ts = true
    /\ check_jittered_edf_compact_dbf_certificate_fields
         (jittered_edf_compact_dbf_certificate_expected_cutoff ts)
         (jittered_edf_compact_dbf_certificate_expected_basis ts)
         cert = true
    /\ jittered_fast_compact_basis_ndbf_test
         (jittered_tasks_of_extracted_list ts)
         (jittered_offset_of_extracted_list ts)
         (jitter_of_extracted_list ts)
         (jittered_enumT_of_extracted_list ts)
         cert.(jedf_compact_basis) = true.
Proof.
  intros ts cert Hcheck.
  unfold check_jittered_edf_compact_dbf_certificate_extracted in Hcheck.
  apply andb_true_iff in Hcheck as [Hrest Hdbf].
  apply andb_true_iff in Hrest as [Hwf Hfields].
  repeat split; assumption.
Qed.

Lemma jittered_fast_compact_basis_ndbf_test_eq :
  forall tasks offset jitter enumT basis,
    jittered_fast_compact_basis_ndbf_test tasks offset jitter enumT basis =
    jittered_fast_compact_basis_dbf_test tasks offset jitter enumT basis.
Proof.
  intros tasks offset jitter enumT basis.
  unfold jittered_fast_compact_basis_ndbf_test,
         jittered_fast_compact_basis_dbf_test.
  generalize (jittered_compact_basis_windows basis).
  intros windows.
  induction windows as [|[t1 t2] windows IH]; simpl.
  - reflexivity.
  - rewrite jittered_periodic_fast_dbf_window_ok_N_b_eq_nat.
    rewrite IH.
    reflexivity.
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

Lemma check_jittered_edf_compact_dbf_certificate_extracted_certificate_fields :
  forall ts cert,
    check_jittered_edf_compact_dbf_certificate_extracted ts cert = true ->
    cert.(jedf_compact_cutoff) =
      jittered_edf_compact_dbf_certificate_expected_cutoff ts
    /\ cert.(jedf_compact_basis) =
      jittered_edf_compact_dbf_certificate_expected_basis ts
    /\ cert.(jedf_all_basis_checked) = true.
Proof.
  intros ts cert Hcheck.
  destruct
    (check_jittered_edf_compact_dbf_certificate_extracted_fields ts cert Hcheck)
    as [_ [Hfields _]].
  apply check_jittered_edf_compact_dbf_certificate_fields_sound.
  exact Hfields.
Qed.

Lemma jittered_fast_compact_basis_dbf_test_to_cutoff_test :
  forall tasks offset jitter enumT H basis,
    jittered_compact_basis_covers_upto tasks offset jitter enumT H basis ->
    jittered_fast_compact_basis_ndbf_test tasks offset jitter enumT basis = true ->
    jittered_window_dbf_test_upto tasks offset jitter enumT H = true.
Proof.
  intros tasks offset jitter enumT H basis Hcovers Hcompact.
  rewrite jittered_fast_compact_basis_ndbf_test_eq in Hcompact.
  unfold jittered_window_dbf_test_upto.
  apply forallb_forall.
  intros [t1 t2] Hin.
  apply Nat.leb_le.
  destruct
    (critical_dbf_windows_upto_bounds tasks offset enumT H t1 t2 Hin)
    as [Hle12 Hle2H].
  eapply jittered_fast_compact_basis_dbf_test_sound; eauto.
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

Theorem check_jittered_edf_compact_dbf_certificate_extracted_sound :
  forall ts cert,
    check_jittered_edf_compact_dbf_certificate_extracted ts cert = true ->
    extracted_jittered_offset_window_dbf_ok_global ts.
Proof.
  intros ts cert Hcheck.
  destruct
    (check_jittered_edf_compact_dbf_certificate_extracted_fields ts cert Hcheck)
    as [Hwf [Hfields Hcompact]].
  destruct
    (check_jittered_edf_compact_dbf_certificate_fields_sound
       (jittered_edf_compact_dbf_certificate_expected_cutoff ts)
       (jittered_edf_compact_dbf_certificate_expected_basis ts)
       cert Hfields)
    as [_ [Hbasis _]].
  unfold extracted_jittered_offset_window_dbf_ok_global.
  eapply jittered_offset_window_dbf_check_by_cutoff.
  - intros τ Hin.
    eapply extracted_jittered_tasks_well_formed_on_enum.
    + exact Hwf.
    + apply jittered_enumT_of_extracted_list_sound.
      exact Hin.
  - unfold extracted_jittered_offset_window_dbf_test_by_cutoff.
    apply
      (jittered_fast_compact_basis_dbf_test_to_cutoff_test
         (jittered_tasks_of_extracted_list ts)
         (jittered_offset_of_extracted_list ts)
         (jitter_of_extracted_list ts)
         (jittered_enumT_of_extracted_list ts)
         (extracted_jittered_offset_window_dbf_cutoff_bound ts)
         cert.(jedf_compact_basis)).
    + rewrite Hbasis.
      unfold jittered_edf_compact_dbf_certificate_expected_basis,
             jittered_edf_compact_dbf_certificate_expected_cutoff,
             extracted_jittered_offset_window_dbf_cutoff_bound.
      apply jittered_reduced_compact_basis_covers_upto.
    + exact Hcompact.
Qed.
