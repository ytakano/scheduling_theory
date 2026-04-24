From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Analysis.Uniprocessor.BusyWindowSearch.
From RocqSched Require Import Analysis.Uniprocessor.EDFProcessorDemand.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFCertificate.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFBacklogBridgeChecker.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFGeneratedPrefixChecker.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFInfiniteBridge.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFNoCarryInSupply.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFTransportChecker.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFWindowTransport.
From RocqSched Require Import TaskModels.Periodic.PeriodicCodec.
From RocqSched Require Import TaskModels.Periodic.PeriodicEnumeration.
From RocqSched Require Import TaskModels.Periodic.PeriodicFiniteHorizon.
From RocqSched Require Import TaskModels.Periodic.PeriodicInfinite.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Periodic.PeriodicWindowDemandBound.

Import ListNotations.

(** Boolean sidecar checker for generated-window transport witnesses.

    The persistent transport certificate continues to say which target job uses
    which representative class and shift.  This sidecar certificate records the
    finite earlier-job correspondences used to justify a shifted window.  The
    checker proves only finite arithmetic and lookup facts; coverage of all
    semantically relevant earlier jobs and actual completion transport remain
    explicit proof obligations for downstream certificate generators. *)

Record EDFWindowTransportPairCert := {
  window_target_earlier_job : JobId;
  window_rep_earlier_job : JobId;
  window_transport_delta : Time
}.

Record EDFWindowTransportTargetCert := {
  window_transport_target_job : JobId;
  window_transport_class_id : nat;
  window_transport_shift : nat;
  window_transport_pairs : list EDFWindowTransportPairCert
}.

Definition check_shifted_job_relation
    (jobs : JobId -> Job)
    (rep target : JobId)
    (p : EDFWindowTransportPairCert) : bool :=
  let delta := p.(window_transport_delta) in
  Nat.eqb (job_release (jobs target)) (job_release (jobs rep) + delta)
  && Nat.eqb
       (job_abs_deadline (jobs target))
       (job_abs_deadline (jobs rep) + delta)
  && Nat.eqb
       (job_release (jobs p.(window_target_earlier_job)))
       (job_release (jobs p.(window_rep_earlier_job)) + delta)
  && Nat.eqb
       (job_abs_deadline (jobs p.(window_target_earlier_job)))
       (job_abs_deadline (jobs p.(window_rep_earlier_job)) + delta).

Definition check_window_transport_target
    (jobs : JobId -> Job)
    (transport_cert : EDFTransportCert JobId)
    (target_cert : EDFWindowTransportTargetCert) : bool :=
  match index_of_job
          target_cert.(window_transport_target_job)
          transport_cert.(transport_basis_jobs) with
  | Some i =>
      match nth_error transport_cert.(transport_job_class) i,
            nth_error transport_cert.(transport_job_shift) i,
            nth_error transport_cert.(transport_classes)
              target_cert.(window_transport_class_id) with
      | Some class_id, Some shift, Some cls =>
          Nat.eqb class_id target_cert.(window_transport_class_id)
          && Nat.eqb shift target_cert.(window_transport_shift)
          && forallb
               (check_shifted_job_relation
                  jobs cls.(transport_rep_job)
                  target_cert.(window_transport_target_job))
               target_cert.(window_transport_pairs)
      | _, _, _ => false
      end
  | None => false
  end.

Definition check_window_transport_targets
    (jobs : JobId -> Job)
    (transport_cert : EDFTransportCert JobId)
    (target_certs : list EDFWindowTransportTargetCert) : bool :=
  forallb (check_window_transport_target jobs transport_cert) target_certs.

Definition check_window_transport_target_entry
    (jobs : JobId -> Job)
    (transport_cert : EDFTransportCert JobId)
    (target class_id shift : nat)
    (target_cert : EDFWindowTransportTargetCert) : bool :=
  Nat.eqb target_cert.(window_transport_target_job) target
  && Nat.eqb target_cert.(window_transport_class_id) class_id
  && Nat.eqb target_cert.(window_transport_shift) shift
  && check_window_transport_target jobs transport_cert target_cert.

Fixpoint check_window_transport_target_rows_complete
    (jobs : JobId -> Job)
    (transport_cert : EDFTransportCert JobId)
    (target_certs : list EDFWindowTransportTargetCert)
    (basis : list JobId)
    (classes shifts : list nat) : bool :=
  match basis, classes, shifts with
  | [], [], [] => true
  | target :: basis', class_id :: classes', shift :: shifts' =>
      match nth_error transport_cert.(transport_classes) class_id with
      | Some _ =>
          existsb
            (check_window_transport_target_entry
               jobs transport_cert target class_id shift)
            target_certs
          && check_window_transport_target_rows_complete
               jobs transport_cert target_certs basis' classes' shifts'
      | None => false
      end
  | _, _, _ => false
  end.

Definition check_window_transport_targets_complete
    (jobs : JobId -> Job)
    (transport_cert : EDFTransportCert JobId)
    (target_certs : list EDFWindowTransportTargetCert) : bool :=
  check_window_transport_targets jobs transport_cert target_certs
  && check_window_transport_target_rows_complete
       jobs transport_cert target_certs
       transport_cert.(transport_basis_jobs)
       transport_cert.(transport_job_class)
       transport_cert.(transport_job_shift).

Definition window_target_candidate_jobs
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (enumT : list TaskId)
    (codec : PeriodicCodec T tasks offset jobs)
    (target : JobId) : list JobId :=
  let H := S (job_abs_deadline (jobs target)) in
  enum_periodic_jobs_upto
    T tasks offset jobs H enumT
    (periodic_finite_horizon_codec_of T tasks offset jobs H codec).

Definition window_target_relevant_earlier_jobs
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (enumT : list TaskId)
    (codec : PeriodicCodec T tasks offset jobs)
    (target : JobId) : list JobId :=
  filter
    (fun x =>
       Nat.ltb (job_release (jobs x)) (job_release (jobs target))
       && Nat.leb (job_abs_deadline (jobs x))
            (job_abs_deadline (jobs target)))
    (window_target_candidate_jobs T tasks offset jobs enumT codec target).

Definition check_window_target_periodic
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (enumT : list TaskId)
    (codec : PeriodicCodec T tasks offset jobs)
    (target : JobId) : bool :=
  existsb
    (Nat.eqb target)
    (window_target_candidate_jobs T tasks offset jobs enumT codec target).

Definition check_window_rep_earlier_membership
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (enumT : list TaskId)
    (codec : PeriodicCodec T tasks offset jobs)
    (rep : JobId)
    (p : EDFWindowTransportPairCert) : bool :=
  existsb
    (Nat.eqb p.(window_rep_earlier_job))
    (window_target_relevant_earlier_jobs T tasks offset jobs enumT codec rep).

Definition check_window_target_rep_earlier_membership
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (enumT : list TaskId)
    (codec : PeriodicCodec T tasks offset jobs)
    (rep : JobId)
    (target_cert : EDFWindowTransportTargetCert) : bool :=
  forallb
    (check_window_rep_earlier_membership
       T tasks offset jobs enumT codec rep)
    target_cert.(window_transport_pairs).

Definition check_window_generated_pair_semantics
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (enumT : list TaskId)
    (codec : PeriodicCodec T tasks offset jobs)
    (transport_cert : EDFTransportCert JobId)
    (target_cert : EDFWindowTransportTargetCert) : bool :=
  match nth_error transport_cert.(transport_classes)
          target_cert.(window_transport_class_id) with
  | Some cls =>
      check_window_target_periodic
        T tasks offset jobs enumT codec
        target_cert.(window_transport_target_job)
      && check_window_target_rep_earlier_membership
           T tasks offset jobs enumT codec
           cls.(transport_rep_job) target_cert
  | None => false
  end.

Definition check_window_generated_pair_semantics_all
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (enumT : list TaskId)
    (codec : PeriodicCodec T tasks offset jobs)
    (transport_cert : EDFTransportCert JobId)
    (target_certs : list EDFWindowTransportTargetCert) : bool :=
  forallb
    (check_window_generated_pair_semantics
       T tasks offset jobs enumT codec transport_cert)
    target_certs.

Definition check_window_transport_pair_for_target_earlier
    (jobs : JobId -> Job)
    (rep target x : JobId)
    (p : EDFWindowTransportPairCert) : bool :=
  Nat.eqb p.(window_target_earlier_job) x
  && Nat.ltb
       (job_release (jobs p.(window_rep_earlier_job)))
       (job_release (jobs rep))
  && Nat.leb
       (job_abs_deadline (jobs p.(window_rep_earlier_job)))
       (job_abs_deadline (jobs rep))
  && check_shifted_job_relation jobs rep target p.

Definition check_window_target_pair_coverage
    (jobs : JobId -> Job)
    (rep : JobId)
    (target_cert : EDFWindowTransportTargetCert)
    (target_earlier_jobs : list JobId) : bool :=
  forallb
    (fun x =>
       existsb
         (check_window_transport_pair_for_target_earlier
            jobs rep target_cert.(window_transport_target_job) x)
         target_cert.(window_transport_pairs))
    target_earlier_jobs.

Definition check_window_transport_target_complete_with_pairs
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (enumT : list TaskId)
    (codec : PeriodicCodec T tasks offset jobs)
    (transport_cert : EDFTransportCert JobId)
    (target_cert : EDFWindowTransportTargetCert) : bool :=
  match nth_error transport_cert.(transport_classes)
          target_cert.(window_transport_class_id) with
  | Some cls =>
      check_window_transport_target jobs transport_cert target_cert
      && check_window_target_pair_coverage
           jobs cls.(transport_rep_job) target_cert
           (window_target_relevant_earlier_jobs
              T tasks offset jobs enumT codec
              target_cert.(window_transport_target_job))
  | None => false
  end.

Definition check_window_transport_targets_complete_with_pairs
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (enumT : list TaskId)
    (codec : PeriodicCodec T tasks offset jobs)
    (transport_cert : EDFTransportCert JobId)
    (target_certs : list EDFWindowTransportTargetCert) : bool :=
  forallb
    (check_window_transport_target_complete_with_pairs
       T tasks offset jobs enumT codec transport_cert)
    target_certs
  && check_window_transport_target_rows_complete
       jobs transport_cert target_certs
       transport_cert.(transport_basis_jobs)
       transport_cert.(transport_job_class)
       transport_cert.(transport_job_shift).

Lemma check_shifted_job_relation_sound :
  forall jobs rep target p,
    check_shifted_job_relation jobs rep target p = true ->
    ShiftedJobRelation
      jobs rep target
      p.(window_rep_earlier_job)
      p.(window_target_earlier_job)
      p.(window_transport_delta).
Proof.
  intros jobs rep target p Hcheck.
  unfold check_shifted_job_relation in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as [[[Htarget_rel Htarget_dl] Hearlier_rel] Hearlier_dl].
  constructor.
  - apply Nat.eqb_eq. exact Htarget_rel.
  - apply Nat.eqb_eq. exact Htarget_dl.
  - apply Nat.eqb_eq. exact Hearlier_rel.
  - apply Nat.eqb_eq. exact Hearlier_dl.
Qed.

Lemma check_window_transport_target_lookup_sound :
  forall jobs transport_cert target_cert,
    check_window_transport_target jobs transport_cert target_cert = true ->
    exists i cls,
      nth_error transport_cert.(transport_basis_jobs) i =
        Some target_cert.(window_transport_target_job)
      /\
      nth_error transport_cert.(transport_job_class) i =
        Some target_cert.(window_transport_class_id)
      /\
      nth_error transport_cert.(transport_job_shift) i =
        Some target_cert.(window_transport_shift)
      /\
      nth_error transport_cert.(transport_classes)
        target_cert.(window_transport_class_id) = Some cls
      /\
      forall p,
        In p target_cert.(window_transport_pairs) ->
        ShiftedJobRelation
          jobs cls.(transport_rep_job)
          target_cert.(window_transport_target_job)
          p.(window_rep_earlier_job)
          p.(window_target_earlier_job)
          p.(window_transport_delta).
Proof.
  intros jobs transport_cert target_cert Hcheck.
  unfold check_window_transport_target in Hcheck.
  destruct (index_of_job
              target_cert.(window_transport_target_job)
              transport_cert.(transport_basis_jobs)) as [i|] eqn:Hidx;
    [|discriminate].
  destruct (nth_error transport_cert.(transport_job_class) i) as [class_id|]
    eqn:Hclass; [|discriminate].
  destruct (nth_error transport_cert.(transport_job_shift) i) as [shift|]
    eqn:Hshift; [|discriminate].
  destruct (nth_error transport_cert.(transport_classes)
              target_cert.(window_transport_class_id)) as [cls|]
    eqn:Hcls; [|discriminate].
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as [[Hclass_eq Hshift_eq] Hpairs].
  apply Nat.eqb_eq in Hclass_eq.
  apply Nat.eqb_eq in Hshift_eq.
  subst class_id shift.
  exists i, cls.
  split.
  - eapply index_of_job_sound; eauto.
  - split.
    + exact Hclass.
    + split.
      * exact Hshift.
      * split.
        -- reflexivity.
        -- intros p Hin.
           apply forallb_forall with (x := p) in Hpairs; [|exact Hin].
           eapply check_shifted_job_relation_sound; eauto.
Qed.

Lemma check_window_transport_targets_sound :
  forall jobs transport_cert target_certs target_cert,
    check_window_transport_targets jobs transport_cert target_certs = true ->
    In target_cert target_certs ->
    check_window_transport_target jobs transport_cert target_cert = true.
Proof.
  intros jobs transport_cert target_certs target_cert Hcheck Hin.
  unfold check_window_transport_targets in Hcheck.
  eapply forallb_forall; eauto.
Qed.

Lemma check_window_transport_targets_complete_targets :
  forall jobs transport_cert target_certs,
    check_window_transport_targets_complete
      jobs transport_cert target_certs = true ->
    check_window_transport_targets jobs transport_cert target_certs = true.
Proof.
  intros jobs transport_cert target_certs Hcheck.
  unfold check_window_transport_targets_complete in Hcheck.
  apply andb_true_iff in Hcheck.
  exact (proj1 Hcheck).
Qed.

Lemma check_window_transport_targets_complete_with_pairs_targets :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs)
         transport_cert target_certs,
    check_window_transport_targets_complete_with_pairs
      T tasks offset jobs enumT codec transport_cert target_certs = true ->
    check_window_transport_targets jobs transport_cert target_certs = true.
Proof.
  intros T tasks offset jobs enumT codec transport_cert target_certs Hcheck.
  unfold check_window_transport_targets_complete_with_pairs in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Htargets _].
  unfold check_window_transport_targets.
  apply forallb_forall.
  intros target_cert Hin.
  apply forallb_forall with (x := target_cert) in Htargets; [|exact Hin].
  unfold check_window_transport_target_complete_with_pairs in Htargets.
  destruct (nth_error transport_cert.(transport_classes)
              target_cert.(window_transport_class_id)) as [cls|];
    [|discriminate].
  apply andb_true_iff in Htargets.
  exact (proj1 Htargets).
Qed.

Lemma check_window_transport_pair_for_target_earlier_sound :
  forall jobs rep target x p,
    check_window_transport_pair_for_target_earlier jobs rep target x p = true ->
    p.(window_target_earlier_job) = x
    /\
    job_release (jobs p.(window_rep_earlier_job)) <
      job_release (jobs rep)
    /\
    job_abs_deadline (jobs p.(window_rep_earlier_job)) <=
      job_abs_deadline (jobs rep)
    /\
    ShiftedJobRelation
      jobs rep target
      p.(window_rep_earlier_job)
      p.(window_target_earlier_job)
      p.(window_transport_delta).
Proof.
  intros jobs rep target x p Hcheck.
  unfold check_window_transport_pair_for_target_earlier in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as [[[Htarget Hrelease] Hdeadline] Hshifted].
  split.
  - apply Nat.eqb_eq. exact Htarget.
  - split.
    + apply Nat.ltb_lt. exact Hrelease.
    + split.
      * apply Nat.leb_le. exact Hdeadline.
      * eapply check_shifted_job_relation_sound; eauto.
Qed.

Lemma check_window_target_pair_coverage_sound :
  forall jobs rep target_cert target_earlier_jobs x,
    check_window_target_pair_coverage
      jobs rep target_cert target_earlier_jobs = true ->
    In x target_earlier_jobs ->
    exists p,
      In p target_cert.(window_transport_pairs)
      /\
      p.(window_target_earlier_job) = x
      /\
      job_release (jobs p.(window_rep_earlier_job)) <
        job_release (jobs rep)
      /\
      job_abs_deadline (jobs p.(window_rep_earlier_job)) <=
        job_abs_deadline (jobs rep)
      /\
      ShiftedJobRelation
        jobs rep target_cert.(window_transport_target_job)
        p.(window_rep_earlier_job)
        p.(window_target_earlier_job)
        p.(window_transport_delta).
Proof.
  intros jobs rep target_cert target_earlier_jobs x Hcheck Hin.
  unfold check_window_target_pair_coverage in Hcheck.
  apply forallb_forall with (x := x) in Hcheck; [|exact Hin].
  apply existsb_exists in Hcheck.
  destruct Hcheck as [p [Hin_pair Hpair_check]].
  exists p.
  destruct
    (check_window_transport_pair_for_target_earlier_sound
       jobs rep target_cert.(window_transport_target_job) x p Hpair_check)
    as [Htarget [Hrelease [Hdeadline Hshifted]]].
  split; [exact Hin_pair|].
  split; [exact Htarget|].
  split; [exact Hrelease|].
  split; [exact Hdeadline|].
  exact Hshifted.
Qed.

Lemma check_window_transport_target_complete_with_pairs_coverage_sound :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs)
         transport_cert target_cert cls x,
    check_window_transport_target_complete_with_pairs
      T tasks offset jobs enumT codec transport_cert target_cert = true ->
    nth_error transport_cert.(transport_classes)
      target_cert.(window_transport_class_id) = Some cls ->
    In x
      (window_target_relevant_earlier_jobs
         T tasks offset jobs enumT codec
         target_cert.(window_transport_target_job)) ->
    exists p,
      In p target_cert.(window_transport_pairs)
      /\
      p.(window_target_earlier_job) = x
      /\
      job_release (jobs p.(window_rep_earlier_job)) <
        job_release (jobs cls.(transport_rep_job))
      /\
      job_abs_deadline (jobs p.(window_rep_earlier_job)) <=
        job_abs_deadline (jobs cls.(transport_rep_job))
      /\
      ShiftedJobRelation
        jobs cls.(transport_rep_job)
        target_cert.(window_transport_target_job)
        p.(window_rep_earlier_job)
        p.(window_target_earlier_job)
        p.(window_transport_delta).
Proof.
  intros T tasks offset jobs enumT codec transport_cert target_cert cls x
         Hcheck Hcls Hin.
  unfold check_window_transport_target_complete_with_pairs in Hcheck.
  rewrite Hcls in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [_ Hcoverage].
  eapply check_window_target_pair_coverage_sound; eauto.
Qed.

Lemma check_window_transport_targets_complete_with_pairs_coverage_sound :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs)
         transport_cert target_certs target_cert cls x,
    check_window_transport_targets_complete_with_pairs
      T tasks offset jobs enumT codec transport_cert target_certs = true ->
    In target_cert target_certs ->
    nth_error transport_cert.(transport_classes)
      target_cert.(window_transport_class_id) = Some cls ->
    In x
      (window_target_relevant_earlier_jobs
         T tasks offset jobs enumT codec
         target_cert.(window_transport_target_job)) ->
    exists p,
      In p target_cert.(window_transport_pairs)
      /\
      p.(window_target_earlier_job) = x
      /\
      job_release (jobs p.(window_rep_earlier_job)) <
        job_release (jobs cls.(transport_rep_job))
      /\
      job_abs_deadline (jobs p.(window_rep_earlier_job)) <=
        job_abs_deadline (jobs cls.(transport_rep_job))
      /\
      ShiftedJobRelation
        jobs cls.(transport_rep_job)
        target_cert.(window_transport_target_job)
        p.(window_rep_earlier_job)
        p.(window_target_earlier_job)
        p.(window_transport_delta).
Proof.
  intros T tasks offset jobs enumT codec transport_cert target_certs
         target_cert cls x Hcheck Hin Hcls Hx.
  unfold check_window_transport_targets_complete_with_pairs in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Htargets _].
  apply forallb_forall with (x := target_cert) in Htargets; [|exact Hin].
  eapply check_window_transport_target_complete_with_pairs_coverage_sound;
    eauto.
Qed.

Lemma window_target_relevant_earlier_jobs_complete :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs)
         target x,
    well_formed_periodic_tasks_on T tasks ->
    (forall τ, T τ -> In τ enumT) ->
    periodic_jobset_deadline_between
      T tasks offset jobs 0 (job_abs_deadline (jobs target)) x ->
    job_release (jobs x) < job_release (jobs target) ->
    In x
      (window_target_relevant_earlier_jobs
         T tasks offset jobs enumT codec target).
Proof.
  intros T tasks offset jobs enumT codec target x
         Hwf HenumT_complete Hbetween Hrelease.
  unfold window_target_relevant_earlier_jobs.
  apply filter_In.
  split.
  - unfold window_target_candidate_jobs.
    apply enum_periodic_jobs_upto_complete; [exact Hwf|exact HenumT_complete|].
    unfold periodic_jobset_upto.
    pose proof
      (periodic_jobset_deadline_between_implies_task_in_scope
         T tasks offset jobs 0 (job_abs_deadline (jobs target)) x Hbetween)
      as HT.
    pose proof
      (periodic_jobset_deadline_between_implies_generated
         T tasks offset jobs 0 (job_abs_deadline (jobs target)) x Hbetween)
      as Hgen.
    pose proof
      (periodic_jobset_deadline_between_implies_deadline_le
         T tasks offset jobs 0 (job_abs_deadline (jobs target)) x Hbetween)
      as Hdeadline.
    split; [exact HT|].
    split; [exact Hgen|].
    pose proof (generated_job_deadline tasks offset jobs x Hgen) as Hdeadline_eq.
    lia.
  - apply andb_true_iff.
    split.
    + apply Nat.ltb_lt. exact Hrelease.
    + apply Nat.leb_le.
      exact (periodic_jobset_deadline_between_implies_deadline_le
               T tasks offset jobs 0 (job_abs_deadline (jobs target))
               x Hbetween).
Qed.

Lemma window_target_candidate_jobs_sound :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs)
         target x,
    (forall τ, In τ enumT -> T τ) ->
    In x (window_target_candidate_jobs T tasks offset jobs enumT codec target) ->
    periodic_jobset T tasks offset jobs x.
Proof.
  intros T tasks offset jobs enumT codec target x HenumT_sound Hin.
  unfold window_target_candidate_jobs in Hin.
  eapply periodic_jobset_upto_implies_periodic_jobset.
  eapply enum_periodic_jobs_upto_sound; eauto.
Qed.

Lemma window_target_relevant_earlier_jobs_sound :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs)
         target x,
    (forall τ, In τ enumT -> T τ) ->
    In x (window_target_relevant_earlier_jobs
            T tasks offset jobs enumT codec target) ->
    periodic_jobset_deadline_between
      T tasks offset jobs 0 (job_abs_deadline (jobs target)) x
    /\
    job_release (jobs x) < job_release (jobs target).
Proof.
  intros T tasks offset jobs enumT codec target x HenumT_sound Hin.
  unfold window_target_relevant_earlier_jobs in Hin.
  apply filter_In in Hin.
  destruct Hin as [Hin_candidate Hfilter].
  apply andb_true_iff in Hfilter.
  destruct Hfilter as [Hrelease Hdeadline].
  pose proof
    (window_target_candidate_jobs_sound
       T tasks offset jobs enumT codec target x HenumT_sound Hin_candidate)
    as Hjobset.
  destruct Hjobset as [HT Hgen].
  split.
  - split; [exact HT|].
    split; [exact Hgen|].
    split; [lia|].
    apply Nat.leb_le. exact Hdeadline.
  - apply Nat.ltb_lt. exact Hrelease.
Qed.

Lemma check_window_target_periodic_sound :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs)
         target,
    (forall τ, In τ enumT -> T τ) ->
    check_window_target_periodic T tasks offset jobs enumT codec target = true ->
    periodic_jobset T tasks offset jobs target.
Proof.
  intros T tasks offset jobs enumT codec target HenumT_sound Hcheck.
  unfold check_window_target_periodic in Hcheck.
  apply existsb_exists in Hcheck.
  destruct Hcheck as [x [Hin Heq]].
  apply Nat.eqb_eq in Heq.
  subst x.
  eapply window_target_candidate_jobs_sound; eauto.
Qed.

Lemma check_window_rep_earlier_membership_sound :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs)
         rep p,
    (forall τ, In τ enumT -> T τ) ->
    check_window_rep_earlier_membership
      T tasks offset jobs enumT codec rep p = true ->
    periodic_jobset_deadline_between
      T tasks offset jobs 0 (job_abs_deadline (jobs rep))
      p.(window_rep_earlier_job).
Proof.
  intros T tasks offset jobs enumT codec rep p HenumT_sound Hcheck.
  unfold check_window_rep_earlier_membership in Hcheck.
  apply existsb_exists in Hcheck.
  destruct Hcheck as [x [Hin Heq]].
  apply Nat.eqb_eq in Heq.
  subst x.
  destruct
    (window_target_relevant_earlier_jobs_sound
       T tasks offset jobs enumT codec rep
       p.(window_rep_earlier_job) HenumT_sound Hin)
    as [Hbetween _].
  exact Hbetween.
Qed.

Lemma check_window_target_rep_earlier_membership_sound :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs)
         rep target_cert p,
    (forall τ, In τ enumT -> T τ) ->
    check_window_target_rep_earlier_membership
      T tasks offset jobs enumT codec rep target_cert = true ->
    In p target_cert.(window_transport_pairs) ->
    periodic_jobset_deadline_between
      T tasks offset jobs 0 (job_abs_deadline (jobs rep))
      p.(window_rep_earlier_job).
Proof.
  intros T tasks offset jobs enumT codec rep target_cert p
         HenumT_sound Hcheck Hin.
  unfold check_window_target_rep_earlier_membership in Hcheck.
  apply forallb_forall with (x := p) in Hcheck; [|exact Hin].
  eapply check_window_rep_earlier_membership_sound; eauto.
Qed.

Lemma check_window_generated_pair_semantics_sound :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs)
         transport_cert target_cert cls,
    (forall τ, In τ enumT -> T τ) ->
    check_window_generated_pair_semantics
      T tasks offset jobs enumT codec transport_cert target_cert = true ->
    nth_error transport_cert.(transport_classes)
      target_cert.(window_transport_class_id) = Some cls ->
    periodic_jobset
      T tasks offset jobs target_cert.(window_transport_target_job)
    /\
    forall p,
      In p target_cert.(window_transport_pairs) ->
      periodic_jobset_deadline_between
        T tasks offset jobs 0 (job_abs_deadline (jobs cls.(transport_rep_job)))
        p.(window_rep_earlier_job).
Proof.
  intros T tasks offset jobs enumT codec transport_cert target_cert cls
         HenumT_sound Hcheck Hcls.
  unfold check_window_generated_pair_semantics in Hcheck.
  rewrite Hcls in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [Htarget_check Hrep_check].
  split.
  - eapply check_window_target_periodic_sound; eauto.
  - intros p Hin.
    eapply check_window_target_rep_earlier_membership_sound; eauto.
Qed.

Lemma check_window_generated_pair_semantics_all_sound :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs)
         transport_cert target_certs target_cert cls,
    (forall τ, In τ enumT -> T τ) ->
    check_window_generated_pair_semantics_all
      T tasks offset jobs enumT codec transport_cert target_certs = true ->
    In target_cert target_certs ->
    nth_error transport_cert.(transport_classes)
      target_cert.(window_transport_class_id) = Some cls ->
    periodic_jobset
      T tasks offset jobs target_cert.(window_transport_target_job)
    /\
    forall p,
      In p target_cert.(window_transport_pairs) ->
      periodic_jobset_deadline_between
        T tasks offset jobs 0 (job_abs_deadline (jobs cls.(transport_rep_job)))
        p.(window_rep_earlier_job).
Proof.
  intros T tasks offset jobs enumT codec transport_cert target_certs
         target_cert cls HenumT_sound Hcheck Hin Hcls.
  unfold check_window_generated_pair_semantics_all in Hcheck.
  apply forallb_forall with (x := target_cert) in Hcheck; [|exact Hin].
  eapply check_window_generated_pair_semantics_sound; eauto.
Qed.

Lemma check_window_transport_target_entry_sound :
  forall jobs transport_cert target class_id shift target_cert,
    check_window_transport_target_entry
      jobs transport_cert target class_id shift target_cert = true ->
    target_cert.(window_transport_target_job) = target
    /\
    target_cert.(window_transport_class_id) = class_id
    /\
    target_cert.(window_transport_shift) = shift
    /\
    check_window_transport_target jobs transport_cert target_cert = true.
Proof.
  intros jobs transport_cert target class_id shift target_cert Hcheck.
  unfold check_window_transport_target_entry in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as [[[Htarget Hclass] Hshift] Htarget_check].
  repeat split.
  - apply Nat.eqb_eq. exact Htarget.
  - apply Nat.eqb_eq. exact Hclass.
  - apply Nat.eqb_eq. exact Hshift.
  - exact Htarget_check.
Qed.

Lemma check_window_transport_target_rows_complete_sound :
  forall jobs transport_cert target_certs basis classes shifts
         i target class_id shift cls,
    check_window_transport_target_rows_complete
      jobs transport_cert target_certs basis classes shifts = true ->
    nth_error basis i = Some target ->
    nth_error classes i = Some class_id ->
    nth_error shifts i = Some shift ->
    nth_error transport_cert.(transport_classes) class_id = Some cls ->
    exists target_cert,
      In target_cert target_certs
      /\
      target_cert.(window_transport_target_job) = target
      /\
      target_cert.(window_transport_class_id) = class_id
      /\
      target_cert.(window_transport_shift) = shift
      /\
      check_window_transport_target jobs transport_cert target_cert = true.
Proof.
  intros jobs transport_cert target_certs basis.
  induction basis as [|target0 basis IH];
    intros classes shifts i target class_id shift cls
           Hcheck Hbasis Hclass Hshift Hcls.
  - destruct i; discriminate.
  - destruct classes as [|class0 classes]; [discriminate|].
    destruct shifts as [|shift0 shifts]; [discriminate|].
    destruct i as [|i].
    + cbn in Hbasis, Hclass, Hshift.
      inversion Hbasis; inversion Hclass; inversion Hshift; subst.
      cbn in Hcheck.
      rewrite Hcls in Hcheck.
      apply andb_true_iff in Hcheck.
      destruct Hcheck as [Hexists _].
      apply existsb_exists in Hexists.
      destruct Hexists as [target_cert [Hin Hentry]].
      exists target_cert.
      destruct
        (check_window_transport_target_entry_sound
           jobs transport_cert target class_id shift target_cert Hentry)
        as [Htarget [Hclass' [Hshift' Htarget_check]]].
      repeat split; assumption.
    + cbn in Hbasis, Hclass, Hshift.
      cbn in Hcheck.
      destruct (nth_error transport_cert.(transport_classes) class0) as [cls0|]
        eqn:Hcls0; [|discriminate].
      apply andb_true_iff in Hcheck.
      destruct Hcheck as [_ Htail].
      eapply IH; eauto.
Qed.

Lemma check_window_transport_targets_complete_basis_sound :
  forall jobs transport_cert target_certs i target class_id shift cls,
    check_window_transport_targets_complete
      jobs transport_cert target_certs = true ->
    nth_error transport_cert.(transport_basis_jobs) i = Some target ->
    nth_error transport_cert.(transport_job_class) i = Some class_id ->
    nth_error transport_cert.(transport_job_shift) i = Some shift ->
    nth_error transport_cert.(transport_classes) class_id = Some cls ->
    exists target_cert,
      In target_cert target_certs
      /\
      target_cert.(window_transport_target_job) = target
      /\
      target_cert.(window_transport_class_id) = class_id
      /\
      target_cert.(window_transport_shift) = shift
      /\
      check_window_transport_target jobs transport_cert target_cert = true.
Proof.
  intros jobs transport_cert target_certs i target class_id shift cls
         Hcheck Hbasis Hclass Hshift Hcls.
  unfold check_window_transport_targets_complete in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [_ Hrows].
  eapply check_window_transport_target_rows_complete_sound; eauto.
Qed.

Lemma check_window_transport_targets_complete_with_pairs_basis_sound :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs)
         transport_cert target_certs i target class_id shift cls,
    check_window_transport_targets_complete_with_pairs
      T tasks offset jobs enumT codec transport_cert target_certs = true ->
    nth_error transport_cert.(transport_basis_jobs) i = Some target ->
    nth_error transport_cert.(transport_job_class) i = Some class_id ->
    nth_error transport_cert.(transport_job_shift) i = Some shift ->
    nth_error transport_cert.(transport_classes) class_id = Some cls ->
    exists target_cert,
      In target_cert target_certs
      /\
      target_cert.(window_transport_target_job) = target
      /\
      target_cert.(window_transport_class_id) = class_id
      /\
      target_cert.(window_transport_shift) = shift
      /\
      check_window_transport_target jobs transport_cert target_cert = true.
Proof.
  intros T tasks offset jobs enumT codec transport_cert target_certs
         i target class_id shift cls Hcheck Hbasis Hclass Hshift Hcls.
  unfold check_window_transport_targets_complete_with_pairs in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [_ Hrows].
  eapply check_window_transport_target_rows_complete_sound; eauto.
Qed.

Record WindowTransportTargetObligation
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (rep_sched target_sched : Schedule)
    (rep target : JobId)
    (target_cert : EDFWindowTransportTargetCert) : Prop := {
  checked_window_rep_backlog_to_completion :
    periodic_edf_backlog_free_before_release
      T tasks offset jobs (job_abs_deadline (jobs rep)) rep_sched rep ->
    representative_earlier_completion_before_release
      T tasks offset jobs rep_sched rep;
  checked_window_target_pair_coverage :
    forall t1 t2 x,
      busy_prefix_witness target_sched (job_abs_deadline (jobs target)) t1 t2 ->
      t1 <= job_release (jobs target) ->
      periodic_jobset_deadline_between
        T tasks offset jobs t1 (job_abs_deadline (jobs target)) x ->
      job_release (jobs x) < job_release (jobs target) ->
      exists p,
        In p target_cert.(window_transport_pairs)
        /\ p.(window_target_earlier_job) = x
        /\ periodic_jobset_deadline_between
             T tasks offset jobs 0 (job_abs_deadline (jobs rep))
             p.(window_rep_earlier_job)
        /\ job_release (jobs p.(window_rep_earlier_job)) <
             job_release (jobs rep);
  checked_window_pair_completion_transport :
    forall p,
      In p target_cert.(window_transport_pairs) ->
      ShiftedJobRelation
        jobs rep target
        p.(window_rep_earlier_job)
        p.(window_target_earlier_job)
        p.(window_transport_delta) ->
      ShiftedCompletionTransport
        jobs rep_sched target_sched rep target
        p.(window_rep_earlier_job)
        p.(window_target_earlier_job)
}.

Record WindowPairGeneratedCompletionTransportObligation
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (enumT : list TaskId)
    (codec : PeriodicCodec T tasks offset jobs)
    (prefix_cert : EDFPrefixCert JobId)
    (rep target : JobId)
    (target_cert : EDFWindowTransportTargetCert) : Prop := {
  checked_window_completion_target_periodic :
    periodic_jobset T tasks offset jobs target;
  checked_window_pair_generated_completion_transport :
    forall p,
      In p target_cert.(window_transport_pairs) ->
      GeneratedShiftedCompletionTransport
        T tasks offset jobs enumT codec prefix_cert
        rep target
        p.(window_rep_earlier_job)
        p.(window_target_earlier_job)
}.

Theorem checked_window_pair_generated_completion_transport_sound :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs)
         prefix_cert rep target target_cert,
    well_formed_periodic_tasks_on T tasks ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    WindowPairGeneratedCompletionTransportObligation
      T tasks offset jobs enumT codec prefix_cert rep target target_cert ->
    forall p,
      In p target_cert.(window_transport_pairs) ->
      ShiftedJobRelation
        jobs rep target
        p.(window_rep_earlier_job)
        p.(window_target_earlier_job)
        p.(window_transport_delta) ->
      ShiftedCompletionTransport
        jobs
        (generated_periodic_edf_prefix
           T tasks offset jobs enumT codec prefix_cert)
        (generated_periodic_edf_schedule_upto
           T tasks offset jobs (S (job_abs_deadline (jobs target))) enumT codec)
        rep target
        p.(window_rep_earlier_job)
        p.(window_target_earlier_job).
Proof.
  intros T tasks offset jobs enumT codec prefix_cert rep target target_cert
         Hwf HenumT_complete HenumT_sound Hobligation p Hin _.
  eapply generated_shifted_completion_transport_sound.
  - exact Hwf.
  - exact HenumT_complete.
  - exact HenumT_sound.
  - exact
      (checked_window_completion_target_periodic
         T tasks offset jobs enumT codec prefix_cert
         rep target target_cert Hobligation).
  - exact
      (checked_window_pair_generated_completion_transport
         T tasks offset jobs enumT codec prefix_cert
         rep target target_cert Hobligation p Hin).
Qed.

Theorem window_transport_target_obligation_of_generated_completion :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs)
         prefix_cert rep target target_cert,
    well_formed_periodic_tasks_on T tasks ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    (periodic_edf_backlog_free_before_release
       T tasks offset jobs
       (job_abs_deadline (jobs rep))
       (generated_periodic_edf_prefix
          T tasks offset jobs enumT codec prefix_cert)
       rep ->
     representative_earlier_completion_before_release
       T tasks offset jobs
       (generated_periodic_edf_prefix
          T tasks offset jobs enumT codec prefix_cert)
       rep) ->
    (forall t1 t2 x,
      busy_prefix_witness
        (generated_periodic_edf_schedule_upto
           T tasks offset jobs
           (S (job_abs_deadline (jobs target))) enumT codec)
        (job_abs_deadline (jobs target)) t1 t2 ->
      t1 <= job_release (jobs target) ->
      periodic_jobset_deadline_between
        T tasks offset jobs t1 (job_abs_deadline (jobs target)) x ->
      job_release (jobs x) < job_release (jobs target) ->
      exists p,
        In p target_cert.(window_transport_pairs)
        /\ p.(window_target_earlier_job) = x
        /\ periodic_jobset_deadline_between
             T tasks offset jobs 0 (job_abs_deadline (jobs rep))
             p.(window_rep_earlier_job)
        /\ job_release (jobs p.(window_rep_earlier_job)) <
             job_release (jobs rep)) ->
    WindowPairGeneratedCompletionTransportObligation
      T tasks offset jobs enumT codec prefix_cert rep target target_cert ->
    WindowTransportTargetObligation
      T tasks offset jobs
      (generated_periodic_edf_prefix
         T tasks offset jobs enumT codec prefix_cert)
      (generated_periodic_edf_schedule_upto
         T tasks offset jobs
         (S (job_abs_deadline (jobs target))) enumT codec)
      rep target target_cert.
Proof.
  intros T tasks offset jobs enumT codec prefix_cert rep target target_cert
         Hwf HenumT_complete HenumT_sound Hrep_completion
         Hpair_coverage Hgenerated_completion.
  constructor.
  - exact Hrep_completion.
  - exact Hpair_coverage.
  - intros p Hin Hshifted.
    eapply checked_window_pair_generated_completion_transport_sound; eauto.
Qed.

Theorem checked_window_transport_target_sound :
  forall T tasks offset jobs rep_sched target_sched transport_cert target_cert
         i cls,
    check_window_transport_target jobs transport_cert target_cert = true ->
    NoDup transport_cert.(transport_basis_jobs) ->
    nth_error transport_cert.(transport_basis_jobs) i =
      Some target_cert.(window_transport_target_job) ->
    nth_error transport_cert.(transport_job_class) i =
      Some target_cert.(window_transport_class_id) ->
    nth_error transport_cert.(transport_job_shift) i =
      Some target_cert.(window_transport_shift) ->
    nth_error transport_cert.(transport_classes)
      target_cert.(window_transport_class_id) = Some cls ->
    WindowTransportTargetObligation
      T tasks offset jobs rep_sched target_sched
      cls.(transport_rep_job)
      target_cert.(window_transport_target_job)
      target_cert ->
    ShiftedBacklogWindowTransport
      T tasks offset jobs rep_sched target_sched
      cls.(transport_rep_job)
      target_cert.(window_transport_target_job).
Proof.
  intros T tasks offset jobs rep_sched target_sched transport_cert target_cert
         i cls Hcheck Hbasis_nodup Hbasis Hclass Hshift Hcls Hobligation.
  destruct
    (check_window_transport_target_lookup_sound
       jobs transport_cert target_cert Hcheck)
    as [i_lookup [cls_lookup
          [Hbasis_lookup [Hclass_lookup [Hshift_lookup
          [Hcls_lookup Hrelations]]]]]].
  assert (Hi : i_lookup = i).
  {
    rewrite NoDup_nth_error in Hbasis_nodup.
    apply Hbasis_nodup.
    - apply nth_error_Some.
      rewrite Hbasis_lookup.
      discriminate.
    - rewrite Hbasis_lookup, Hbasis.
      reflexivity.
  }
  subst i_lookup.
  assert (Hcls_eq : cls_lookup = cls).
  {
    rewrite Hclass in Hclass_lookup.
    inversion Hclass_lookup.
    subst.
    rewrite Hcls in Hcls_lookup.
    inversion Hcls_lookup.
    reflexivity.
  }
  subst cls_lookup.
  constructor.
  - exact
      (checked_window_rep_backlog_to_completion
         T tasks offset jobs rep_sched target_sched
         cls.(transport_rep_job)
         target_cert.(window_transport_target_job)
         target_cert
         Hobligation).
  - intros t1 t2 x Hbusy Ht1 Hbetween Hrelease.
    destruct
      (checked_window_target_pair_coverage
         T tasks offset jobs rep_sched target_sched
         cls.(transport_rep_job)
         target_cert.(window_transport_target_job)
         target_cert Hobligation
         t1 t2 x Hbusy Ht1 Hbetween Hrelease)
	    as [p [Hin [Htarget [Hrep_between Hrep_release]]]].
    exists p.(window_rep_earlier_job).
    split.
    + exact Hrep_between.
    + split.
      * exact Hrep_release.
      * rewrite <- Htarget.
        exact
        (checked_window_pair_completion_transport
           T tasks offset jobs rep_sched target_sched
           cls.(transport_rep_job)
           target_cert.(window_transport_target_job)
           target_cert Hobligation p Hin
           (Hrelations p Hin)).
Qed.

Record WindowTransportTargetsObligation
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (enumT : list TaskId)
    (codec : PeriodicCodec T tasks offset jobs)
    (prefix_cert : EDFPrefixCert JobId)
    (transport_cert : EDFTransportCert JobId)
    (target_certs : list EDFWindowTransportTargetCert) : Prop := {
  checked_window_transport_basis_nodup :
    NoDup transport_cert.(transport_basis_jobs);
  checked_window_target_cert_complete :
    forall target (cls : EDFTransportClass JobId) (shift : nat),
      exists target_cert i class_id,
        In target_cert target_certs
        /\ target_cert.(window_transport_target_job) = target
        /\ nth_error transport_cert.(transport_basis_jobs) i = Some target
        /\ nth_error transport_cert.(transport_job_class) i = Some class_id
        /\ nth_error transport_cert.(transport_job_shift) i = Some shift
        /\ nth_error transport_cert.(transport_classes) class_id = Some cls
        /\ target_cert.(window_transport_class_id) = class_id
        /\ target_cert.(window_transport_shift) = shift;
  checked_window_target_obligation :
    forall target_cert i cls,
      In target_cert target_certs ->
      nth_error transport_cert.(transport_basis_jobs) i =
        Some target_cert.(window_transport_target_job) ->
      nth_error transport_cert.(transport_job_class) i =
        Some target_cert.(window_transport_class_id) ->
      nth_error transport_cert.(transport_classes)
        target_cert.(window_transport_class_id) = Some cls ->
      WindowTransportTargetObligation
        T tasks offset jobs
        (generated_periodic_edf_prefix
           T tasks offset jobs enumT codec prefix_cert)
        (generated_periodic_edf_schedule_upto
           T tasks offset jobs
           (S (job_abs_deadline
                 (jobs target_cert.(window_transport_target_job)))) enumT codec)
        cls.(transport_rep_job)
        target_cert.(window_transport_target_job)
        target_cert
}.

Theorem checked_window_transport_targets_obligation_sound :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs)
         prefix_cert transport_cert target_certs,
    check_window_transport_targets jobs transport_cert target_certs = true ->
    WindowTransportTargetsObligation
      T tasks offset jobs enumT codec prefix_cert transport_cert target_certs ->
    ShiftedGeneratedWindowTransportObligation
      T tasks offset jobs enumT codec prefix_cert.
Proof.
  intros T tasks offset jobs enumT codec prefix_cert transport_cert target_certs
         Hcheck Hobligation.
  constructor.
  intros target cls shift.
  destruct
    (checked_window_target_cert_complete
       T tasks offset jobs enumT codec prefix_cert transport_cert target_certs
       Hobligation target cls shift)
    as [target_cert [i_cert [class_id Hcomplete]]].
  destruct Hcomplete as
    [Hin [Htarget [Hbasis_complete
    [Hclass_complete [Hshift_complete [Hcls_complete
    [Htarget_class Htarget_shift]]]]]]].
  pose proof
    (check_window_transport_targets_sound
       jobs transport_cert target_certs target_cert Hcheck Hin)
    as Htarget_check.
  assert (Hbasis_target :
    nth_error transport_cert.(transport_basis_jobs) i_cert =
      Some target_cert.(window_transport_target_job)).
  {
    rewrite Htarget.
    exact Hbasis_complete.
  }
  assert (Hclass_target :
    nth_error transport_cert.(transport_job_class) i_cert =
      Some target_cert.(window_transport_class_id)).
  {
    rewrite Htarget_class.
    exact Hclass_complete.
  }
  assert (Hshift_target :
    nth_error transport_cert.(transport_job_shift) i_cert =
      Some target_cert.(window_transport_shift)).
  {
    rewrite Htarget_shift.
    exact Hshift_complete.
  }
  assert (Hcls_target :
    nth_error transport_cert.(transport_classes)
      target_cert.(window_transport_class_id) = Some cls).
  {
    rewrite Htarget_class.
    exact Hcls_complete.
  }
  assert (Hshifted :
    ShiftedBacklogWindowTransport
      T tasks offset jobs
      (generated_periodic_edf_prefix
         T tasks offset jobs enumT codec prefix_cert)
      (generated_periodic_edf_schedule_upto
         T tasks offset jobs
         (S (job_abs_deadline
               (jobs target_cert.(window_transport_target_job)))) enumT codec)
      cls.(transport_rep_job)
	      target_cert.(window_transport_target_job)).
  {
    eapply checked_window_transport_target_sound.
    - exact Htarget_check.
    - exact
        (checked_window_transport_basis_nodup
           T tasks offset jobs enumT codec prefix_cert transport_cert
           target_certs Hobligation).
    - exact Hbasis_target.
    - exact Hclass_target.
    - exact Hshift_target.
    - exact Hcls_target.
    - eapply checked_window_target_obligation; eauto.
  }
  rewrite Htarget in Hshifted.
  exact Hshifted.
Qed.
