From Stdlib Require Import List Bool Arith Arith.PeanoNat.
From RocqSched Require Import Foundation.Base.

Import ListNotations.

(** Extraction-friendly DBF certificate for jittered-periodic EDF.

    This certificate is intentionally DBF-only.  It records the finite cutoff
    and the bounded critical windows claimed to have been checked; the checker
    still recomputes both from the task set before trusting the certificate. *)

Record JitteredEDFDbfCertificate := {
  jedf_cutoff : Time;
  jedf_checked_windows : list (Time * Time);
  jedf_all_windows_checked : bool
}.

Definition time_pair_eqb (w1 w2 : Time * Time) : bool :=
  let '(a1, b1) := w1 in
  let '(a2, b2) := w2 in
  Nat.eqb a1 a2 && Nat.eqb b1 b2.

Fixpoint time_pair_list_eqb
    (xs ys : list (Time * Time)) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' =>
      time_pair_eqb x y && time_pair_list_eqb xs' ys'
  | _, _ => false
  end.

Definition check_jittered_edf_dbf_certificate_fields
    (expected_cutoff : Time)
    (expected_windows : list (Time * Time))
    (cert : JitteredEDFDbfCertificate) : bool :=
  Nat.eqb cert.(jedf_cutoff) expected_cutoff
  && time_pair_list_eqb cert.(jedf_checked_windows) expected_windows
  && cert.(jedf_all_windows_checked).

Lemma time_pair_eqb_true :
  forall w1 w2,
    time_pair_eqb w1 w2 = true ->
    w1 = w2.
Proof.
  intros [a1 b1] [a2 b2] Heq.
  unfold time_pair_eqb in Heq.
  apply andb_true_iff in Heq as [Ha Hb].
  apply Nat.eqb_eq in Ha.
  apply Nat.eqb_eq in Hb.
  subst.
  reflexivity.
Qed.

Lemma time_pair_list_eqb_true :
  forall xs ys,
    time_pair_list_eqb xs ys = true ->
    xs = ys.
Proof.
  induction xs as [|x xs IH]; intros ys Heq.
  - destruct ys; cbn in Heq; congruence.
  - destruct ys as [|y ys]; cbn in Heq; try discriminate.
    apply andb_true_iff in Heq as [Hxy Htail].
    apply time_pair_eqb_true in Hxy.
    apply IH in Htail.
    subst.
    reflexivity.
Qed.

Lemma check_jittered_edf_dbf_certificate_fields_sound :
  forall expected_cutoff expected_windows cert,
    check_jittered_edf_dbf_certificate_fields
      expected_cutoff expected_windows cert = true ->
    cert.(jedf_cutoff) = expected_cutoff
    /\ cert.(jedf_checked_windows) = expected_windows
    /\ cert.(jedf_all_windows_checked) = true.
Proof.
  intros expected_cutoff expected_windows cert Hcheck.
  unfold check_jittered_edf_dbf_certificate_fields in Hcheck.
  apply andb_true_iff in Hcheck as [Hrest Hall].
  apply andb_true_iff in Hrest as [Hcutoff Hwindows].
  apply Nat.eqb_eq in Hcutoff.
  apply time_pair_list_eqb_true in Hwindows.
  repeat split; assumption.
Qed.
