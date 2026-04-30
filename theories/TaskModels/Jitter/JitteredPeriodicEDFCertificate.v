From Stdlib Require Import List Bool Arith Arith.PeanoNat.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicCompactDBF.

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

Record JitteredEDFCompactDbfCertificate := {
  jedf_compact_cutoff : Time;
  jedf_compact_basis : JitteredCompactDbfBasis;
  jedf_all_basis_checked : bool
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

Fixpoint time_list_eqb (xs ys : list Time) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => Nat.eqb x y && time_list_eqb xs' ys'
  | _, _ => false
  end.

Definition compact_dbf_basis_row_eqb
    (r1 r2 : Time * list Time) : bool :=
  let '(t2_1, left_edges1) := r1 in
  let '(t2_2, left_edges2) := r2 in
  Nat.eqb t2_1 t2_2 && time_list_eqb left_edges1 left_edges2.

Fixpoint compact_dbf_basis_eqb
    (xs ys : JitteredCompactDbfBasis) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' =>
      compact_dbf_basis_row_eqb x y && compact_dbf_basis_eqb xs' ys'
  | _, _ => false
  end.

Definition compact_dbf_basis_blocks_eqb
    (actual_blocks expected_blocks : list JitteredCompactDbfBasis) : bool :=
  compact_dbf_basis_eqb (concat actual_blocks) (concat expected_blocks).

Definition check_jittered_edf_compact_dbf_certificate_block_basis
    (actual_blocks expected_blocks : list JitteredCompactDbfBasis)
    (cert : JitteredEDFCompactDbfCertificate) : bool :=
  compact_dbf_basis_eqb cert.(jedf_compact_basis) (concat actual_blocks)
  && compact_dbf_basis_blocks_eqb actual_blocks expected_blocks.

Definition check_jittered_edf_compact_dbf_certificate_block_basis_for_expected
    (expected_basis : JitteredCompactDbfBasis)
    (actual_blocks expected_blocks : list JitteredCompactDbfBasis)
    (cert : JitteredEDFCompactDbfCertificate) : bool :=
  compact_dbf_basis_eqb expected_basis (concat expected_blocks)
  && check_jittered_edf_compact_dbf_certificate_block_basis
       actual_blocks expected_blocks cert.

Definition check_jittered_edf_dbf_certificate_fields
    (expected_cutoff : Time)
    (expected_windows : list (Time * Time))
    (cert : JitteredEDFDbfCertificate) : bool :=
  Nat.eqb cert.(jedf_cutoff) expected_cutoff
  && time_pair_list_eqb cert.(jedf_checked_windows) expected_windows
  && cert.(jedf_all_windows_checked).

Definition check_jittered_edf_compact_dbf_certificate_fields
    (expected_cutoff : Time)
    (expected_basis : JitteredCompactDbfBasis)
    (cert : JitteredEDFCompactDbfCertificate) : bool :=
  Nat.eqb cert.(jedf_compact_cutoff) expected_cutoff
  && compact_dbf_basis_eqb cert.(jedf_compact_basis) expected_basis
  && cert.(jedf_all_basis_checked).

Definition check_jittered_edf_compact_dbf_certificate_header
    (expected_cutoff : Time)
    (cert : JitteredEDFCompactDbfCertificate) : bool :=
  Nat.eqb cert.(jedf_compact_cutoff) expected_cutoff
  && cert.(jedf_all_basis_checked).

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

Lemma time_list_eqb_true :
  forall xs ys,
    time_list_eqb xs ys = true ->
    xs = ys.
Proof.
  induction xs as [|x xs IH]; intros ys Heq.
  - destruct ys; cbn in Heq; congruence.
  - destruct ys as [|y ys]; cbn in Heq; try discriminate.
    apply andb_true_iff in Heq as [Hxy Htail].
    apply Nat.eqb_eq in Hxy.
    apply IH in Htail.
    subst.
    reflexivity.
Qed.

Lemma compact_dbf_basis_row_eqb_true :
  forall r1 r2,
    compact_dbf_basis_row_eqb r1 r2 = true ->
    r1 = r2.
Proof.
  intros [t2_1 left_edges1] [t2_2 left_edges2] Heq.
  unfold compact_dbf_basis_row_eqb in Heq.
  apply andb_true_iff in Heq as [Ht2 Hleft_edges].
  apply Nat.eqb_eq in Ht2.
  apply time_list_eqb_true in Hleft_edges.
  subst.
  reflexivity.
Qed.

Lemma compact_dbf_basis_eqb_true :
  forall xs ys,
    compact_dbf_basis_eqb xs ys = true ->
    xs = ys.
Proof.
  induction xs as [|x xs IH]; intros ys Heq.
  - destruct ys; cbn in Heq; congruence.
  - destruct ys as [|y ys]; cbn in Heq; try discriminate.
    apply andb_true_iff in Heq as [Hxy Htail].
    apply compact_dbf_basis_row_eqb_true in Hxy.
    apply IH in Htail.
    subst.
    reflexivity.
Qed.

Lemma compact_dbf_basis_blocks_eqb_true :
  forall actual_blocks expected_blocks,
    compact_dbf_basis_blocks_eqb actual_blocks expected_blocks = true ->
    concat actual_blocks = concat expected_blocks.
Proof.
  intros actual_blocks expected_blocks Heq.
  unfold compact_dbf_basis_blocks_eqb in Heq.
  apply compact_dbf_basis_eqb_true in Heq.
  exact Heq.
Qed.

Lemma check_jittered_edf_compact_dbf_certificate_block_basis_sound :
  forall actual_blocks expected_blocks cert,
    check_jittered_edf_compact_dbf_certificate_block_basis
      actual_blocks expected_blocks cert = true ->
    cert.(jedf_compact_basis) = concat actual_blocks
    /\ concat actual_blocks = concat expected_blocks
    /\ cert.(jedf_compact_basis) = concat expected_blocks.
Proof.
  intros actual_blocks expected_blocks cert Hcheck.
  unfold check_jittered_edf_compact_dbf_certificate_block_basis in Hcheck.
  apply andb_true_iff in Hcheck as [Hactual Hblocks].
  apply compact_dbf_basis_eqb_true in Hactual.
  apply compact_dbf_basis_blocks_eqb_true in Hblocks.
  repeat split; congruence.
Qed.

Lemma check_jittered_edf_compact_dbf_certificate_block_basis_for_expected_sound :
  forall expected_basis actual_blocks expected_blocks cert,
    check_jittered_edf_compact_dbf_certificate_block_basis_for_expected
      expected_basis actual_blocks expected_blocks cert = true ->
    cert.(jedf_compact_basis) = expected_basis
    /\ cert.(jedf_compact_basis) = concat actual_blocks
    /\ concat actual_blocks = concat expected_blocks
    /\ expected_basis = concat expected_blocks.
Proof.
  intros expected_basis actual_blocks expected_blocks cert Hcheck.
  unfold check_jittered_edf_compact_dbf_certificate_block_basis_for_expected
    in Hcheck.
  apply andb_true_iff in Hcheck as [Hexpected Hblock].
  apply compact_dbf_basis_eqb_true in Hexpected.
  destruct
    (check_jittered_edf_compact_dbf_certificate_block_basis_sound
       actual_blocks expected_blocks cert Hblock)
    as [Hactual [Hblocks Hcert_expected_blocks]].
  repeat split; congruence.
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

Lemma check_jittered_edf_compact_dbf_certificate_fields_sound :
  forall expected_cutoff expected_basis cert,
    check_jittered_edf_compact_dbf_certificate_fields
      expected_cutoff expected_basis cert = true ->
    cert.(jedf_compact_cutoff) = expected_cutoff
    /\ cert.(jedf_compact_basis) = expected_basis
    /\ cert.(jedf_all_basis_checked) = true.
Proof.
  intros expected_cutoff expected_basis cert Hcheck.
  unfold check_jittered_edf_compact_dbf_certificate_fields in Hcheck.
  apply andb_true_iff in Hcheck as [Hrest Hall].
  apply andb_true_iff in Hrest as [Hcutoff Hbasis].
  apply Nat.eqb_eq in Hcutoff.
  apply compact_dbf_basis_eqb_true in Hbasis.
  repeat split; assumption.
Qed.

Lemma check_jittered_edf_compact_dbf_certificate_header_sound :
  forall expected_cutoff cert,
    check_jittered_edf_compact_dbf_certificate_header
      expected_cutoff cert = true ->
    cert.(jedf_compact_cutoff) = expected_cutoff
    /\ cert.(jedf_all_basis_checked) = true.
Proof.
  intros expected_cutoff cert Hcheck.
  unfold check_jittered_edf_compact_dbf_certificate_header in Hcheck.
  apply andb_true_iff in Hcheck as [Hcutoff Hall].
  apply Nat.eqb_eq in Hcutoff.
  split; assumption.
Qed.
