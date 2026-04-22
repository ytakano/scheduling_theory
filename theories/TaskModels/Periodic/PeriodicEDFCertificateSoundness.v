From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
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

Lemma nth_error_exists_of_lt :
  forall A (l : list A) n,
    n < length l ->
    exists x, nth_error l n = Some x.
Proof.
  intros A l.
  induction l as [|x l IH]; intros n Hlt.
  - destruct n; inversion Hlt.
  - destruct n as [|n].
    + exists x. reflexivity.
    + simpl in Hlt.
      assert (Hlt' : n < length l) by lia.
      specialize (IH n Hlt').
      destruct IH as [y Hy].
      exists y. exact Hy.
Qed.

Record EDFPrefixCertSemantics
    (jobs : JobId -> Job)
    (c : EDFPrefixCert JobId)
    (sched : Schedule) : Prop := {
  prefix_slots_match_schedule :
    forall t,
      t < prefix_horizon c ->
      sched t 0 = nth t (prefix_slots c) None;
  prefix_completed_by_semantics :
    forall i j t,
      nth_error (prefix_basis_jobs c) i = Some j ->
      nth_error (prefix_completed_by c) i = Some t ->
      completed jobs 1 sched j t;
  prefix_backlog_free_semantics :
    forall i row j b ji jj,
      nth_error (prefix_backlog_free_matrix c) i = Some row ->
      nth_error row j = Some b ->
      nth_error (prefix_basis_jobs c) i = Some ji ->
      nth_error (prefix_basis_jobs c) j = Some jj ->
      b = true ->
      completed jobs 1 sched jj (job_release (jobs ji))
}.

Section PrefixCertSoundness.
  Context (jobs : JobId -> Job).
  Context (sched : Schedule).

  Theorem check_prefix_cert_semantic_sound :
    forall c,
      check_prefix_cert c = true ->
      EDFPrefixCertSemantics jobs c sched ->
      (forall t,
          t < prefix_horizon c ->
          sched t 0 = nth t (prefix_slots c) None)
      /\
      (forall i t,
          nth_error (prefix_completed_by c) i = Some t ->
          exists j,
            nth_error (prefix_basis_jobs c) i = Some j /\
            completed jobs 1 sched j t)
      /\
      (forall i row j,
          nth_error (prefix_backlog_free_matrix c) i = Some row ->
          nth_error row j = Some true ->
          exists ji jj,
            nth_error (prefix_basis_jobs c) i = Some ji /\
            nth_error (prefix_basis_jobs c) j = Some jj /\
            completed jobs 1 sched jj (job_release (jobs ji))).
  Proof.
    intros c Hcheck Hsem.
    split.
    - exact (prefix_slots_match_schedule jobs c sched Hsem).
    - split.
      + intros i t Hnth.
        pose proof (prefix_completed_by_index_in_basis JobId c i t Hcheck Hnth) as Hi.
        destruct (nth_error_exists_of_lt JobId (prefix_basis_jobs c) i Hi) as [j Hj].
        exists j.
        split; [exact Hj|].
        eapply prefix_completed_by_semantics; eauto.
      + intros i row j Hrow Hcell.
        pose proof
          (prefix_backlog_cell_lookup_sound JobId c i j row true Hcheck Hrow Hcell)
          as [Hi Hj].
        destruct (nth_error_exists_of_lt JobId (prefix_basis_jobs c) i Hi) as [ji Hji].
        destruct (nth_error_exists_of_lt JobId (prefix_basis_jobs c) j Hj) as [jj Hjj].
        exists ji, jj.
        repeat split; try assumption.
        eapply prefix_backlog_free_semantics; eauto.
  Qed.

  Theorem check_prefix_cert_slots_sound :
    forall c,
      check_prefix_cert c = true ->
      EDFPrefixCertSemantics jobs c sched ->
      forall t,
        t < prefix_horizon c ->
        sched t 0 = nth t (prefix_slots c) None.
  Proof.
    intros c Hcheck Hsem t Ht.
    destruct (check_prefix_cert_semantic_sound c Hcheck Hsem)
      as [Hslots _].
    exact (Hslots t Ht).
  Qed.

  Theorem check_prefix_cert_completed_by_sound :
    forall c,
      check_prefix_cert c = true ->
      EDFPrefixCertSemantics jobs c sched ->
      forall i t,
        nth_error (prefix_completed_by c) i = Some t ->
        exists j,
          nth_error (prefix_basis_jobs c) i = Some j /\
          completed jobs 1 sched j t.
  Proof.
    intros c Hcheck Hsem i t Hnth.
    destruct (check_prefix_cert_semantic_sound c Hcheck Hsem)
      as [_ [Hcompleted _]].
    exact (Hcompleted i t Hnth).
  Qed.

  Theorem check_prefix_cert_backlog_sound :
    forall c,
      check_prefix_cert c = true ->
      EDFPrefixCertSemantics jobs c sched ->
      forall i row j,
        nth_error (prefix_backlog_free_matrix c) i = Some row ->
        nth_error row j = Some true ->
        exists ji jj,
          nth_error (prefix_basis_jobs c) i = Some ji /\
          nth_error (prefix_basis_jobs c) j = Some jj /\
          completed jobs 1 sched jj (job_release (jobs ji)).
  Proof.
    intros c Hcheck Hsem i row j Hrow Hcell.
    destruct (check_prefix_cert_semantic_sound c Hcheck Hsem)
      as [_ [_ Hbacklog]].
    exact (Hbacklog i row j Hrow Hcell).
  Qed.
End PrefixCertSoundness.

Record EDFTransportCertSemantics
    (transport_witness_holds : JobId -> EDFTransportClass JobId -> nat -> Prop)
    (c : EDFTransportCert JobId) : Prop := {
  transport_lookup_semantics :
    forall i j class_id shift cls,
      nth_error (transport_basis_jobs c) i = Some j ->
      nth_error (transport_job_class c) i = Some class_id ->
      nth_error (transport_job_shift c) i = Some shift ->
      nth_error (transport_classes c) class_id = Some cls ->
      transport_witness_holds j cls shift
}.

Section TransportCertSoundness.
  Context
    (transport_witness_holds : JobId -> EDFTransportClass JobId -> nat -> Prop).

  Theorem check_transport_cert_semantic_sound :
    forall c,
      check_transport_cert c = true ->
      EDFTransportCertSemantics transport_witness_holds c ->
      0 < transport_period c
      /\
      (forall i j class_id shift,
          nth_error (transport_basis_jobs c) i = Some j ->
          nth_error (transport_job_class c) i = Some class_id ->
          nth_error (transport_job_shift c) i = Some shift ->
          exists cls,
            nth_error (transport_classes c) class_id = Some cls /\
            transport_witness_holds j cls shift).
  Proof.
    intros c Hcheck Hsem.
    pose proof (check_transport_cert_fields JobId c Hcheck)
      as [Hperiod [_ [_ _]]].
    split; [exact Hperiod|].
    intros i j class_id shift Hj Hclass Hshift.
    pose proof
      (transport_job_class_lookup_sound JobId c i class_id Hcheck Hclass)
      as [_ Hclass_lt].
    destruct (nth_error_exists_of_lt (EDFTransportClass JobId)
                (transport_classes c) class_id Hclass_lt) as [cls Hcls].
    exists cls.
    split; [exact Hcls|].
    eapply transport_lookup_semantics; eauto.
  Qed.
End TransportCertSoundness.

Record EDFDBFCertSemantics
    (dbf_holds_at : Time -> Prop)
    (c : EDFDBFCert) : Prop := {
  dbf_table_semantics :
    forall t b,
      nth_error (dbf_ok_table c) t = Some b ->
      b = true ->
      dbf_holds_at t
}.

Section DBFCertSoundness.
  Context (dbf_holds_at : Time -> Prop).

  Theorem check_dbf_cert_semantic_sound :
    forall c,
      check_dbf_cert c = true ->
      EDFDBFCertSemantics dbf_holds_at c ->
      forall t, t <= dbf_cutoff c -> dbf_holds_at t.
  Proof.
    intros c Hcheck Hsem t Ht.
    pose proof (check_dbf_cert_fields c Hcheck) as [Hlen Hall].
    assert (Hlt : t < length (dbf_ok_table c)).
    {
      rewrite Hlen.
      lia.
    }
    destruct (nth_error_exists_of_lt bool (dbf_ok_table c) t Hlt) as [b Hnth].
    eapply dbf_table_semantics; eauto.
    apply Hall.
    eapply nth_error_In.
    exact Hnth.
  Qed.
End DBFCertSoundness.

Section CombinedInfiniteCertSoundness.
  Context (jobs : JobId -> Job).
  Context (sched : Schedule).
  Context (transport_witness_holds : JobId -> EDFTransportClass JobId -> nat -> Prop).
  Context (dbf_holds_at : Time -> Prop).

  Theorem check_edf_infinite_cert_semantic_sound :
    forall c,
      check_edf_infinite_cert c = true ->
      EDFPrefixCertSemantics jobs c.(cert_prefix) sched ->
      EDFTransportCertSemantics transport_witness_holds c.(cert_transport) ->
      EDFDBFCertSemantics dbf_holds_at c.(cert_dbf) ->
      (forall t,
          t < prefix_horizon c.(cert_prefix) ->
          sched t 0 = nth t (prefix_slots c.(cert_prefix)) None)
      /\
      (forall i t,
          nth_error (prefix_completed_by c.(cert_prefix)) i = Some t ->
          exists j,
            nth_error (prefix_basis_jobs c.(cert_prefix)) i = Some j /\
            completed jobs 1 sched j t)
      /\
      (forall i row j,
          nth_error (prefix_backlog_free_matrix c.(cert_prefix)) i = Some row ->
          nth_error row j = Some true ->
          exists ji jj,
            nth_error (prefix_basis_jobs c.(cert_prefix)) i = Some ji /\
            nth_error (prefix_basis_jobs c.(cert_prefix)) j = Some jj /\
            completed jobs 1 sched jj (job_release (jobs ji)))
      /\
      0 < transport_period c.(cert_transport)
      /\
      (forall i j class_id shift,
          nth_error (transport_basis_jobs c.(cert_transport)) i = Some j ->
          nth_error (transport_job_class c.(cert_transport)) i = Some class_id ->
          nth_error (transport_job_shift c.(cert_transport)) i = Some shift ->
          exists cls,
            nth_error (transport_classes c.(cert_transport)) class_id = Some cls /\
            transport_witness_holds j cls shift)
      /\
      (forall t, t <= dbf_cutoff c.(cert_dbf) -> dbf_holds_at t).
  Proof.
    intros c Hcheck Hprefix Htransport Hdbf.
    pose proof (check_edf_infinite_cert_fields JobId c Hcheck)
      as [Hprefix_check [Htransport_check Hdbf_check]].
    pose proof
      (check_prefix_cert_semantic_sound jobs sched c.(cert_prefix) Hprefix_check Hprefix)
      as [Hslots [Hcompleted Hbacklog]].
    pose proof
      (check_transport_cert_semantic_sound transport_witness_holds
         c.(cert_transport) Htransport_check Htransport)
      as [Hperiod Htransport_sound].
    pose proof
      (check_dbf_cert_semantic_sound dbf_holds_at
         c.(cert_dbf) Hdbf_check Hdbf) as Hdbf_sound.
    repeat split; eauto.
  Qed.
End CombinedInfiniteCertSoundness.
