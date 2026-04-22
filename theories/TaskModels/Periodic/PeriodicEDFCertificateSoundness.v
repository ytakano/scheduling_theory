From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFCertificate.

Import ListNotations.

(* Structural lemmas for the generic certificate/checker layer.
   This file intentionally stops short of schedule semantics: its purpose is to
   stabilize the extraction-friendly lookup facts that later semantic soundness
   theorems will consume. *)

Lemma prefix_completed_by_index_in_basis :
  forall Job (c : EDFPrefixCert Job) i t,
    check_prefix_cert c = true ->
    nth_error c.(prefix_completed_by) i = Some t ->
    i < length c.(prefix_basis_jobs).
Proof.
  intros Job c i t Hcheck Hnth.
  pose proof (check_prefix_cert_fields Job c Hcheck)
    as [_ [Hcompleted [_ _]]].
  rewrite <- Hcompleted.
  apply nth_error_Some.
  intro Hnone.
  rewrite Hnth in Hnone.
  discriminate.
Qed.

Lemma prefix_backlog_row_lookup_sound :
  forall Job (c : EDFPrefixCert Job) i row,
    check_prefix_cert c = true ->
    nth_error c.(prefix_backlog_free_matrix) i = Some row ->
    i < length c.(prefix_basis_jobs)
    /\ length row = length c.(prefix_basis_jobs).
Proof.
  intros Job c i row Hcheck Hnth.
  pose proof (check_prefix_cert_fields Job c Hcheck)
    as [_ [_ [Hmatrix Hrows]]].
  split.
  - rewrite <- Hmatrix.
    apply nth_error_Some.
    intro Hnone.
    rewrite Hnth in Hnone.
    discriminate.
  - apply Hrows.
    eapply nth_error_In.
    exact Hnth.
Qed.

Lemma prefix_backlog_cell_lookup_sound :
  forall Job (c : EDFPrefixCert Job) i j row b,
    check_prefix_cert c = true ->
    nth_error c.(prefix_backlog_free_matrix) i = Some row ->
    nth_error row j = Some b ->
    i < length c.(prefix_basis_jobs)
    /\ j < length c.(prefix_basis_jobs).
Proof.
  intros Job c i j row b Hcheck Hrow Hcell.
  pose proof (prefix_backlog_row_lookup_sound Job c i row Hcheck Hrow)
    as [Hi Hrowlen].
  split; [exact Hi|].
  rewrite <- Hrowlen.
  apply nth_error_Some.
  intro Hnone.
  rewrite Hcell in Hnone.
  discriminate.
Qed.

Lemma transport_job_class_lookup_sound :
  forall Job (c : EDFTransportCert Job) i class_id,
    check_transport_cert c = true ->
    nth_error c.(transport_job_class) i = Some class_id ->
    i < length c.(transport_basis_jobs)
    /\ class_id < length c.(transport_classes).
Proof.
  intros Job c i class_id Hcheck Hnth.
  pose proof (check_transport_cert_fields Job c Hcheck)
    as [Hperiod [Hclass_len [_ Hclass_bound]]].
  split.
  - rewrite <- Hclass_len.
    apply nth_error_Some.
    intro Hnone.
    rewrite Hnth in Hnone.
    discriminate.
  - apply Hclass_bound.
    eapply nth_error_In.
    exact Hnth.
Qed.

Lemma transport_job_shift_lookup_sound :
  forall Job (c : EDFTransportCert Job) i shift,
    check_transport_cert c = true ->
    nth_error c.(transport_job_shift) i = Some shift ->
    i < length c.(transport_basis_jobs).
Proof.
  intros Job c i shift Hcheck Hnth.
  pose proof (check_transport_cert_fields Job c Hcheck)
    as [_ [_ [Hshift_len _]]].
  rewrite <- Hshift_len.
  apply nth_error_Some.
  intro Hnone.
  rewrite Hnth in Hnone.
  discriminate.
Qed.

Lemma dbf_ok_table_lookup_sound :
  forall c t b,
    check_dbf_cert c = true ->
    nth_error c.(dbf_ok_table) t = Some b ->
    t <= c.(dbf_cutoff)
    /\ b = true.
Proof.
  intros c t b Hcheck Hnth.
  pose proof (check_dbf_cert_fields c Hcheck) as [Hlen Hall].
  split.
  - assert (Ht : t < length c.(dbf_ok_table)).
    {
      apply nth_error_Some.
      intro Hnone.
      rewrite Hnth in Hnone.
      discriminate.
    }
    rewrite Hlen in Ht.
    lia.
  - apply Hall.
    eapply nth_error_In.
    exact Hnth.
Qed.
