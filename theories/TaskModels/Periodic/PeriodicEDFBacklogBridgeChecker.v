From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Analysis.Uniprocessor.EDFProcessorDemand.
From RocqSched Require Import TaskModels.Periodic.PeriodicInfinite.
From RocqSched Require Import TaskModels.Periodic.PeriodicWindowDemandBound.
From RocqSched Require Import TaskModels.Periodic.PeriodicCodec.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFCertificate.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFCertificateSoundness.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFPrefixChecker.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFGeneratedPrefixChecker.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFNoCarryInSupply.

Import ListNotations.

(** Boolean bridge from finite prefix backlog certificates to the
    backlog-free/no-carry-in assumptions consumed by the EDF demand proof.

    The common layer deliberately does not decide which jobs are relevant for a
    target job.  A downstream adapter supplies a finite [relevant_jobs] list and
    proves that it covers the semantic deadline window.  This file checks that
    the prefix certificate's backlog matrix contains the required completion
    facts for exactly that list. *)

Fixpoint index_of_job (j : JobId) (basis : list JobId) : option nat :=
  match basis with
  | [] => None
  | j' :: basis' =>
      if Nat.eqb j j'
      then Some 0
      else option_map S (index_of_job j basis')
  end.

Definition check_job_in_basis (basis : list JobId) (j : JobId) : bool :=
  match index_of_job j basis with
  | Some _ => true
  | None => false
  end.

Definition check_jobs_in_basis (basis jobs : list JobId) : bool :=
  forallb (check_job_in_basis basis) jobs.

Definition check_prefix_backlog_pair
    (c : EDFPrefixCert JobId)
    (target earlier : JobId) : bool :=
  match index_of_job target c.(prefix_basis_jobs),
        index_of_job earlier c.(prefix_basis_jobs) with
  | Some i, Some k =>
      match nth_error c.(prefix_backlog_free_matrix) i with
      | Some row =>
          match nth_error row k with
          | Some b => b
          | None => false
          end
      | None => false
      end
  | _, _ => false
  end.

Definition check_prefix_backlog_free_before_release
    (c : EDFPrefixCert JobId)
    (target : JobId)
    (relevant_jobs : list JobId) : bool :=
  check_job_in_basis c.(prefix_basis_jobs) target
  && forallb (check_prefix_backlog_pair c target) relevant_jobs.

Lemma index_of_job_sound :
  forall basis j i,
    index_of_job j basis = Some i ->
    nth_error basis i = Some j.
Proof.
  induction basis as [|j' basis IH]; intros j i Hidx.
  - discriminate.
  - cbn in Hidx.
    destruct (Nat.eqb j j') eqn:Heq.
    + inversion Hidx; subst.
      cbn.
      apply Nat.eqb_eq in Heq.
      subst.
      reflexivity.
    + destruct (index_of_job j basis) as [i'|] eqn:Htail; [|discriminate].
      inversion Hidx; subst.
      cbn.
      exact (IH j i' Htail).
Qed.

Lemma check_job_in_basis_sound :
  forall basis j,
    check_job_in_basis basis j = true ->
    exists i, nth_error basis i = Some j.
Proof.
  intros basis j Hcheck.
  unfold check_job_in_basis in Hcheck.
  destruct (index_of_job j basis) as [i|] eqn:Hidx; [|discriminate].
  exists i.
  eapply index_of_job_sound; eauto.
Qed.

Lemma check_jobs_in_basis_sound :
  forall basis jobs j,
    check_jobs_in_basis basis jobs = true ->
    In j jobs ->
    exists i, nth_error basis i = Some j.
Proof.
  intros basis jobs j Hcheck Hin.
  unfold check_jobs_in_basis in Hcheck.
  apply forallb_forall with (x := j) in Hcheck; [|exact Hin].
  eapply check_job_in_basis_sound; eauto.
Qed.

Lemma check_prefix_backlog_pair_sound :
  forall jobs c sched target earlier,
    EDFPrefixCertSemantics jobs c sched ->
    check_prefix_backlog_pair c target earlier = true ->
    completed jobs 1 sched earlier (job_release (jobs target)).
Proof.
  intros jobs c sched target earlier Hsem Hcheck.
  unfold check_prefix_backlog_pair in Hcheck.
  destruct (index_of_job target c.(prefix_basis_jobs)) as [i|] eqn:Htarget;
    [|discriminate].
  destruct (index_of_job earlier c.(prefix_basis_jobs)) as [k|] eqn:Hearlier;
    [|discriminate].
  destruct (nth_error c.(prefix_backlog_free_matrix) i) as [row|] eqn:Hrow;
    [|discriminate].
  destruct (nth_error row k) as [b|] eqn:Hcell; [|discriminate].
  pose proof (index_of_job_sound c.(prefix_basis_jobs) target i Htarget)
    as Htarget_nth.
  pose proof (index_of_job_sound c.(prefix_basis_jobs) earlier k Hearlier)
    as Hearlier_nth.
  eapply prefix_backlog_free_semantics; eauto.
Qed.

Lemma check_prefix_backlog_free_before_release_sound :
  forall jobs c sched target relevant_jobs earlier,
    EDFPrefixCertSemantics jobs c sched ->
    check_prefix_backlog_free_before_release c target relevant_jobs = true ->
    In earlier relevant_jobs ->
    completed jobs 1 sched earlier (job_release (jobs target)).
Proof.
  intros jobs c sched target relevant_jobs earlier Hsem Hcheck Hin.
  unfold check_prefix_backlog_free_before_release in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [_ Hrows].
  apply forallb_forall with (x := earlier) in Hrows; [|exact Hin].
  eapply check_prefix_backlog_pair_sound; eauto.
Qed.

Theorem checked_prefix_backlog_free_before_release :
  forall T tasks offset jobs H sched c target relevant_jobs,
    valid_schedule jobs 1 sched ->
    periodic_jobset T tasks offset jobs target ->
    EDFPrefixCertSemantics jobs c sched ->
    check_prefix_backlog_free_before_release c target relevant_jobs = true ->
    (forall x,
       periodic_jobset_deadline_between
         T tasks offset jobs
         0 (job_abs_deadline (jobs target)) x ->
       job_release (jobs x) < job_release (jobs target) ->
       In x relevant_jobs) ->
    periodic_edf_backlog_free_before_release
      T tasks offset jobs H sched target.
Proof.
  intros T tasks offset jobs H sched c target relevant_jobs
         Hvalid Htarget Hsem Hcheck Hcover.
  eapply periodic_edf_backlog_free_before_release_of_earlier_completion;
    eauto.
  intros x Hbetween Hrelease.
  eapply check_prefix_backlog_free_before_release_sound; eauto.
Qed.

Theorem checked_prefix_no_carry_in_bridge :
  forall T tasks offset jobs H sched c target relevant_jobs,
    valid_schedule jobs 1 sched ->
    periodic_jobset T tasks offset jobs target ->
    EDFPrefixCertSemantics jobs c sched ->
    check_prefix_backlog_free_before_release c target relevant_jobs = true ->
    (forall x,
       periodic_jobset_deadline_between
         T tasks offset jobs
         0 (job_abs_deadline (jobs target)) x ->
       job_release (jobs x) < job_release (jobs target) ->
       In x relevant_jobs) ->
    periodic_edf_busy_prefix_no_carry_in_bridge
      T tasks offset jobs H sched target.
Proof.
  intros T tasks offset jobs H sched c target relevant_jobs
         Hvalid Htarget Hsem Hcheck Hcover.
  eapply periodic_edf_no_carry_in_bridge_of_backlog_free; eauto.
  eapply checked_prefix_backlog_free_before_release; eauto.
Qed.

Theorem checked_generated_prefix_backlog_free_before_release :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs)
         c target relevant_jobs,
    valid_schedule jobs 1
      (generated_periodic_edf_prefix T tasks offset jobs enumT codec c) ->
    periodic_jobset T tasks offset jobs target ->
    check_prefix_cert_semantic jobs c = true ->
    check_prefix_slots_match_generated_edf
      T tasks offset jobs enumT codec c = true ->
    check_prefix_backlog_free_before_release c target relevant_jobs = true ->
    (forall x,
       periodic_jobset_deadline_between
         T tasks offset jobs
         0 (job_abs_deadline (jobs target)) x ->
       job_release (jobs x) < job_release (jobs target) ->
       In x relevant_jobs) ->
    periodic_edf_backlog_free_before_release
      T tasks offset jobs c.(prefix_horizon)
      (generated_periodic_edf_prefix T tasks offset jobs enumT codec c)
      target.
Proof.
  intros T tasks offset jobs enumT codec c target relevant_jobs
         Hvalid Htarget Hcert Hmatch Hcheck Hcover.
  eapply checked_prefix_backlog_free_before_release; eauto.
  eapply checked_prefix_semantics_on_generated_edf; eauto.
Qed.

Theorem checked_generated_prefix_no_carry_in_bridge :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs)
         c target relevant_jobs,
    valid_schedule jobs 1
      (generated_periodic_edf_prefix T tasks offset jobs enumT codec c) ->
    periodic_jobset T tasks offset jobs target ->
    check_prefix_cert_semantic jobs c = true ->
    check_prefix_slots_match_generated_edf
      T tasks offset jobs enumT codec c = true ->
    check_prefix_backlog_free_before_release c target relevant_jobs = true ->
    (forall x,
       periodic_jobset_deadline_between
         T tasks offset jobs
         0 (job_abs_deadline (jobs target)) x ->
       job_release (jobs x) < job_release (jobs target) ->
       In x relevant_jobs) ->
    periodic_edf_busy_prefix_no_carry_in_bridge
      T tasks offset jobs c.(prefix_horizon)
      (generated_periodic_edf_prefix T tasks offset jobs enumT codec c)
      target.
Proof.
  intros T tasks offset jobs enumT codec c target relevant_jobs
         Hvalid Htarget Hcert Hmatch Hcheck Hcover.
  eapply checked_prefix_no_carry_in_bridge; eauto.
  eapply checked_prefix_semantics_on_generated_edf; eauto.
Qed.
