From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Semantics.ScheduleLemmas.ScheduleFacts.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFCertificate.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFCertificateSoundness.

Import ListNotations.

(** Verified semantic checker for finite EDF prefix certificates.

    This file turns the prefix certificate's finite slot table into a concrete
    schedule and checks completion/backlog claims by executable service counts.
    It intentionally does not check generated-EDF choice or transport facts. *)

Definition schedule_of_slots (slots : list (option JobId)) : Schedule :=
  fun t c => if Nat.eqb c 0 then nth t slots None else None.

Fixpoint certified_service_prefix
    (slots : list (option JobId)) (j : JobId) (t : Time) : nat :=
  match t with
  | 0 => 0
  | S t' =>
      certified_service_prefix slots j t' +
      match nth t' slots None with
      | Some j' => if Nat.eqb j j' then 1 else 0
      | None => 0
      end
  end.

Definition certified_completed_by
    (jobs : JobId -> Job)
    (slots : list (option JobId))
    (j : JobId)
    (t : Time) : bool :=
  Nat.leb (job_cost (jobs j)) (certified_service_prefix slots j t).

Definition check_prefix_completed_by
    (jobs : JobId -> Job)
    (c : EDFPrefixCert JobId) : bool :=
  forallb
    (fun jt =>
       let '(j, t) := jt in
       certified_completed_by jobs c.(prefix_slots) j t)
    (combine c.(prefix_basis_jobs) c.(prefix_completed_by)).

Fixpoint check_prefix_backlog_row
    (jobs : JobId -> Job)
    (slots : list (option JobId))
    (release_time : Time)
    (basis : list JobId)
    (row : list bool) : bool :=
  match basis, row with
  | [], [] => true
  | jj :: basis', b :: row' =>
      (if b then certified_completed_by jobs slots jj release_time else true)
      && check_prefix_backlog_row jobs slots release_time basis' row'
  | _, _ => false
  end.

Fixpoint check_prefix_backlog_rows_with_basis
    (jobs : JobId -> Job)
    (slots : list (option JobId))
    (row_basis : list JobId)
    (column_basis : list JobId)
    (rows : list (list bool)) : bool :=
  match row_basis, rows with
  | [], [] => true
  | ji :: basis', row :: rows' =>
      check_prefix_backlog_row jobs slots (job_release (jobs ji)) column_basis row
      && check_prefix_backlog_rows_with_basis jobs slots basis' column_basis rows'
  | _, _ => false
  end.

Definition check_prefix_backlog_rows
    (jobs : JobId -> Job)
    (slots : list (option JobId))
    (basis : list JobId)
    (rows : list (list bool)) : bool :=
  check_prefix_backlog_rows_with_basis jobs slots basis basis rows.

Definition check_prefix_backlog_matrix
    (jobs : JobId -> Job)
    (c : EDFPrefixCert JobId) : bool :=
  check_prefix_backlog_rows
    jobs c.(prefix_slots) c.(prefix_basis_jobs) c.(prefix_backlog_free_matrix).

Definition check_prefix_cert_semantic
    (jobs : JobId -> Job)
    (c : EDFPrefixCert JobId) : bool :=
  check_prefix_cert c
  && check_prefix_completed_by jobs c
  && check_prefix_backlog_matrix jobs c.

Lemma cpu_count_one_schedule_of_slots :
  forall slots j t,
    cpu_count 1 (schedule_of_slots slots) j t =
    match nth t slots None with
    | Some j' => if Nat.eqb j j' then 1 else 0
    | None => 0
    end.
Proof.
  intros slots j t.
  cbn [cpu_count].
  unfold runs_on, schedule_of_slots.
  rewrite Nat.eqb_refl.
  destruct (nth t slots None) as [j'|].
  - rewrite Nat.eqb_sym.
    destruct (j =? j'); simpl;
    reflexivity.
  - reflexivity.
Qed.

Lemma certified_service_prefix_sound :
  forall slots j t,
    certified_service_prefix slots j t =
    service_job 1 (schedule_of_slots slots) j t.
Proof.
  intros slots j t.
  induction t as [|t IH].
  - reflexivity.
  - cbn [certified_service_prefix].
    rewrite service_job_step.
    rewrite <- IH.
    rewrite cpu_count_one_schedule_of_slots.
    lia.
Qed.

Lemma certified_completed_by_sound :
  forall jobs slots j t,
    certified_completed_by jobs slots j t = true ->
    completed jobs 1 (schedule_of_slots slots) j t.
Proof.
  intros jobs slots j t Hcheck.
  unfold certified_completed_by in Hcheck.
  apply Nat.leb_le in Hcheck.
  rewrite completed_iff_service_ge_cost.
  rewrite <- certified_service_prefix_sound.
  exact Hcheck.
Qed.

Lemma combine_nth_error_some :
  forall A B (xs : list A) (ys : list B) i x y,
    length xs = length ys ->
    nth_error xs i = Some x ->
    nth_error ys i = Some y ->
    nth_error (combine xs ys) i = Some (x, y).
Proof.
  intros A B xs.
  induction xs as [|x0 xs IH]; intros ys i x y Hlen Hx Hy.
  - destruct i; discriminate.
  - destruct ys as [|y0 ys]; [discriminate|].
    destruct i as [|i].
    + cbn in Hx, Hy |- *.
      inversion Hx; inversion Hy; subst.
      reflexivity.
    + cbn in Hx, Hy |- *.
      apply IH; [cbn in Hlen; lia|exact Hx|exact Hy].
Qed.

Lemma check_prefix_completed_by_sound :
  forall jobs c i j t,
    check_prefix_cert c = true ->
    check_prefix_completed_by jobs c = true ->
    nth_error c.(prefix_basis_jobs) i = Some j ->
    nth_error c.(prefix_completed_by) i = Some t ->
    completed jobs 1 (schedule_of_slots c.(prefix_slots)) j t.
Proof.
  intros jobs c i j t Hshape Hcheck Hj Ht.
  unfold check_prefix_completed_by in Hcheck.
  pose proof (check_prefix_cert_fields JobId c Hshape)
    as [_ [Hlen _]].
  pose proof
    (combine_nth_error_some JobId Time
       c.(prefix_basis_jobs) c.(prefix_completed_by) i j t
       (eq_sym Hlen) Hj Ht)
    as Hpair.
  apply forallb_forall with (x := (j, t)) in Hcheck.
  - cbn in Hcheck.
    exact (certified_completed_by_sound jobs c.(prefix_slots) j t Hcheck).
  - eapply nth_error_In.
    exact Hpair.
Qed.

Lemma check_prefix_backlog_row_sound :
  forall jobs slots release_time basis row j jj,
    check_prefix_backlog_row jobs slots release_time basis row = true ->
    nth_error row j = Some true ->
    nth_error basis j = Some jj ->
    completed jobs 1 (schedule_of_slots slots) jj release_time.
Proof.
  intros jobs slots release_time basis.
  induction basis as [|jj0 basis IH]; intros row j jj Hcheck Hcell Hbasis.
  - destruct j; discriminate.
  - destruct row as [|b row]; [discriminate|].
    destruct j as [|j].
    + cbn in Hcheck, Hcell, Hbasis.
      inversion Hcell; inversion Hbasis; subst.
      apply andb_true_iff in Hcheck.
      destruct Hcheck as [Hhead _].
      exact (certified_completed_by_sound jobs slots jj release_time Hhead).
    + cbn in Hcheck, Hcell, Hbasis.
      apply andb_true_iff in Hcheck.
      destruct Hcheck as [_ Htail].
      eapply IH; eauto.
Qed.

Lemma check_prefix_backlog_rows_with_basis_sound :
  forall jobs slots row_basis column_basis rows i row j ji jj,
    check_prefix_backlog_rows_with_basis jobs slots row_basis column_basis rows = true ->
    nth_error rows i = Some row ->
    nth_error row j = Some true ->
    nth_error row_basis i = Some ji ->
    nth_error column_basis j = Some jj ->
    completed jobs 1 (schedule_of_slots slots) jj (job_release (jobs ji)).
Proof.
  intros jobs slots row_basis.
  induction row_basis as [|ji0 row_basis IH];
    intros column_basis rows i row j ji jj Hcheck Hrow Hcell Hji Hjj.
  - destruct i; discriminate.
  - destruct rows as [|row0 rows]; [discriminate|].
    destruct i as [|i].
    + cbn in Hcheck, Hrow, Hji.
      inversion Hrow; inversion Hji; subst.
      apply andb_true_iff in Hcheck.
      destruct Hcheck as [Hrowcheck _].
      eapply check_prefix_backlog_row_sound; eauto.
    + cbn in Hcheck, Hrow, Hji.
      apply andb_true_iff in Hcheck.
      destruct Hcheck as [_ Htail].
      eapply IH; eauto.
Qed.

Lemma check_prefix_backlog_rows_sound :
  forall jobs slots basis rows i row j ji jj,
    check_prefix_backlog_rows jobs slots basis rows = true ->
    nth_error rows i = Some row ->
    nth_error row j = Some true ->
    nth_error basis i = Some ji ->
    nth_error basis j = Some jj ->
    completed jobs 1 (schedule_of_slots slots) jj (job_release (jobs ji)).
Proof.
  intros jobs slots basis rows i row j ji jj Hcheck Hrow Hcell Hji Hjj.
  unfold check_prefix_backlog_rows in Hcheck.
  eapply check_prefix_backlog_rows_with_basis_sound; eauto.
Qed.

Theorem check_prefix_cert_semantic_sound :
  forall jobs c,
    check_prefix_cert_semantic jobs c = true ->
    EDFPrefixCertSemantics
      jobs c (schedule_of_slots c.(prefix_slots)).
Proof.
  intros jobs c Hcheck.
  unfold check_prefix_cert_semantic in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as [[Hshape Hcompleted] Hbacklog].
  constructor.
  - intros t Ht.
    unfold schedule_of_slots.
    rewrite Nat.eqb_refl.
    reflexivity.
  - intros i j t Hj Ht.
    eapply check_prefix_completed_by_sound; eauto.
  - intros i row j b ji jj Hrow Hcell Hji Hjj Hb.
    subst b.
    unfold check_prefix_backlog_matrix in Hbacklog.
    eapply check_prefix_backlog_rows_sound; eauto.
Qed.
