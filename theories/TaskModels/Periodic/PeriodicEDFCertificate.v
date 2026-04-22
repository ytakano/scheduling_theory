From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.

Import ListNotations.

(* Generic extraction-friendly certificates for Haskell-generated periodic EDF
   witnesses. The common layer records only finite prefix, periodic transport,
   and bounded DBF observables, leaving semantic soundness to a separate file. *)

Record EDFPrefixCert (Job : Type) := {
  prefix_horizon : Time;
  prefix_basis_jobs : list Job;
  prefix_slots : list (option Job);
  prefix_completed_by : list Time;
  prefix_backlog_free_matrix : list (list bool)
}.

Arguments prefix_horizon {Job} _.
Arguments prefix_basis_jobs {Job} _.
Arguments prefix_slots {Job} _.
Arguments prefix_completed_by {Job} _.
Arguments prefix_backlog_free_matrix {Job} _.

Record EDFTransportClass (Job : Type) := {
  transport_rep_job : Job;
  transport_completion_offset : Time;
  transport_backlog_offset : Time
}.

Arguments transport_rep_job {Job} _.
Arguments transport_completion_offset {Job} _.
Arguments transport_backlog_offset {Job} _.

Record EDFTransportCert (Job : Type) := {
  transport_period : Time;
  transport_basis_jobs : list Job;
  transport_classes : list (EDFTransportClass Job);
  transport_job_class : list nat;
  transport_job_shift : list nat
}.

Arguments transport_period {Job} _.
Arguments transport_basis_jobs {Job} _.
Arguments transport_classes {Job} _.
Arguments transport_job_class {Job} _.
Arguments transport_job_shift {Job} _.

Record EDFDBFCert := {
  dbf_cutoff : Time;
  dbf_ok_table : list bool
}.

Record EDFInfiniteCert (Job : Type) := {
  cert_prefix : EDFPrefixCert Job;
  cert_transport : EDFTransportCert Job;
  cert_dbf : EDFDBFCert
}.

Arguments cert_prefix {Job} _.
Arguments cert_transport {Job} _.
Arguments cert_dbf {Job} _.

Definition check_bool_rows_have_length (n : nat) (rows : list (list bool)) : bool :=
  forallb (fun row => Nat.eqb (length row) n) rows.

Definition check_nat_entries_below (bound : nat) (xs : list nat) : bool :=
  forallb (fun x => Nat.ltb x bound) xs.

Definition check_bool_table_true (xs : list bool) : bool :=
  forallb (Bool.eqb true) xs.

Definition check_prefix_cert {Job : Type} (c : EDFPrefixCert Job) : bool :=
  Nat.eqb (length c.(prefix_slots)) c.(prefix_horizon)
  && Nat.eqb (length c.(prefix_completed_by)) (length c.(prefix_basis_jobs))
  && Nat.eqb (length c.(prefix_backlog_free_matrix)) (length c.(prefix_basis_jobs))
  && check_bool_rows_have_length
       (length c.(prefix_basis_jobs))
       c.(prefix_backlog_free_matrix).

Definition check_transport_cert {Job : Type} (c : EDFTransportCert Job) : bool :=
  Nat.ltb 0 c.(transport_period)
  && Nat.eqb (length c.(transport_job_class)) (length c.(transport_basis_jobs))
  && Nat.eqb (length c.(transport_job_shift)) (length c.(transport_basis_jobs))
  && check_nat_entries_below
       (length c.(transport_classes))
       c.(transport_job_class).

Definition check_dbf_cert (c : EDFDBFCert) : bool :=
  Nat.eqb (length c.(dbf_ok_table)) (S c.(dbf_cutoff))
  && check_bool_table_true c.(dbf_ok_table).

Definition check_edf_infinite_cert {Job : Type} (c : EDFInfiniteCert Job) : bool :=
  check_prefix_cert c.(cert_prefix)
  && check_transport_cert c.(cert_transport)
  && check_dbf_cert c.(cert_dbf).

Lemma check_bool_rows_have_length_forall :
  forall rows n,
    check_bool_rows_have_length n rows = true ->
    forall row, In row rows -> length row = n.
Proof.
  intros rows n Hcheck row Hin.
  unfold check_bool_rows_have_length in Hcheck.
  apply forallb_forall with (x := row) in Hcheck; [|exact Hin].
  apply Nat.eqb_eq.
  exact Hcheck.
Qed.

Lemma check_nat_entries_below_forall :
  forall xs bound,
    check_nat_entries_below bound xs = true ->
    forall x, In x xs -> x < bound.
Proof.
  intros xs bound Hcheck x Hin.
  unfold check_nat_entries_below in Hcheck.
  apply forallb_forall with (x := x) in Hcheck; [|exact Hin].
  apply Nat.ltb_lt.
  exact Hcheck.
Qed.

Lemma check_bool_table_true_forall :
  forall xs,
    check_bool_table_true xs = true ->
    forall b, In b xs -> b = true.
Proof.
  intros xs Hcheck b Hin.
  unfold check_bool_table_true in Hcheck.
  apply forallb_forall with (x := b) in Hcheck; [|exact Hin].
  destruct b; simpl in Hcheck; [reflexivity|discriminate].
Qed.

Lemma check_prefix_cert_fields :
  forall Job (c : EDFPrefixCert Job),
    check_prefix_cert c = true ->
    length c.(prefix_slots) = c.(prefix_horizon)
    /\ length c.(prefix_completed_by) = length c.(prefix_basis_jobs)
    /\ length c.(prefix_backlog_free_matrix) = length c.(prefix_basis_jobs)
    /\ forall row,
         In row c.(prefix_backlog_free_matrix) ->
         length row = length c.(prefix_basis_jobs).
Proof.
  intros Job c Hcheck.
  unfold check_prefix_cert in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as [[[Hslots Hcompleted] Hmatrix] Hrows].
  repeat split.
  - apply Nat.eqb_eq. exact Hslots.
  - apply Nat.eqb_eq. exact Hcompleted.
  - apply Nat.eqb_eq. exact Hmatrix.
  - eapply check_bool_rows_have_length_forall; eauto.
Qed.

Lemma check_transport_cert_fields :
  forall Job (c : EDFTransportCert Job),
    check_transport_cert c = true ->
    0 < c.(transport_period)
    /\ length c.(transport_job_class) = length c.(transport_basis_jobs)
    /\ length c.(transport_job_shift) = length c.(transport_basis_jobs)
    /\ forall class_id,
         In class_id c.(transport_job_class) ->
         class_id < length c.(transport_classes).
Proof.
  intros Job c Hcheck.
  unfold check_transport_cert in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as [[[Hperiod Hclass_len] Hshift_len] Hclass_bound].
  repeat split.
  - apply Nat.ltb_lt. exact Hperiod.
  - apply Nat.eqb_eq. exact Hclass_len.
  - apply Nat.eqb_eq. exact Hshift_len.
  - eapply check_nat_entries_below_forall; eauto.
Qed.

Lemma check_dbf_cert_fields :
  forall c,
    check_dbf_cert c = true ->
    length c.(dbf_ok_table) = S c.(dbf_cutoff)
    /\ forall b, In b c.(dbf_ok_table) -> b = true.
Proof.
  intros c Hcheck.
  unfold check_dbf_cert in Hcheck.
  rewrite andb_true_iff in Hcheck.
  destruct Hcheck as [Hlen Hall].
  split.
  - apply Nat.eqb_eq. exact Hlen.
  - eapply check_bool_table_true_forall; eauto.
Qed.

Lemma check_edf_infinite_cert_fields :
  forall Job (c : EDFInfiniteCert Job),
    check_edf_infinite_cert c = true ->
    check_prefix_cert c.(cert_prefix) = true
    /\ check_transport_cert c.(cert_transport) = true
    /\ check_dbf_cert c.(cert_dbf) = true.
Proof.
  intros Job c Hcheck.
  unfold check_edf_infinite_cert in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  tauto.
Qed.
