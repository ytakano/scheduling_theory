From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Semantics.ScheduleLemmas.SchedulePrefix.
From RocqSched Require Import Uniprocessor.Generic.FinitePrefixScheduleWitness.
From RocqSched Require Import Uniprocessor.Policies.EDF.
From RocqSched Require Import TaskModels.Periodic.PeriodicCodec.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFCertificate.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFCertificateSoundness.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFPrefixChecker.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFPrefixCoherence.

Import ListNotations.

(** Boolean checker connecting a finite prefix certificate to the generated
    periodic EDF prefix.  The checker compares certified CPU-0 slots with the
    already executable [generated_schedule_prefix]; it does not duplicate EDF
    choice logic. *)

Definition option_job_eqb (x y : option JobId) : bool :=
  match x, y with
  | Some jx, Some jy => Nat.eqb jx jy
  | None, None => true
  | _, _ => false
  end.

Definition check_prefix_slots_match_schedule
    (sched : Schedule)
    (c : EDFPrefixCert JobId) : bool :=
  check_prefix_cert c
  && forallb
       (fun t => option_job_eqb (nth t c.(prefix_slots) None) (sched t 0))
       (seq 0 c.(prefix_horizon)).

Definition generated_periodic_edf_prefix
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (enumT : list TaskId)
    (codec : PeriodicCodec T tasks offset jobs)
    (c : EDFPrefixCert JobId) : Schedule :=
  generated_schedule_prefix
    edf_generic_spec
    (periodic_candidates_before T tasks offset jobs enumT codec)
    jobs
    c.(prefix_horizon).

Definition check_prefix_slots_match_generated_edf
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (enumT : list TaskId)
    (codec : PeriodicCodec T tasks offset jobs)
    (c : EDFPrefixCert JobId) : bool :=
  check_prefix_slots_match_schedule
    (generated_periodic_edf_prefix T tasks offset jobs enumT codec c)
    c.

Lemma option_job_eqb_true_iff :
  forall x y,
    option_job_eqb x y = true <-> x = y.
Proof.
  intros [jx|] [jy|]; simpl.
  - rewrite Nat.eqb_eq. split; congruence.
  - split; discriminate.
  - split; discriminate.
  - split; reflexivity.
Qed.

Lemma nth_prefix_slots_none_after_horizon :
  forall (c : EDFPrefixCert JobId) t,
    check_prefix_cert c = true ->
    c.(prefix_horizon) <= t ->
    nth t c.(prefix_slots) None = None.
Proof.
  intros c t Hcheck Ht.
  pose proof (check_prefix_cert_fields JobId c Hcheck)
    as [Hslots _].
  apply nth_overflow.
  rewrite Hslots.
  exact Ht.
Qed.

Lemma generated_schedule_prefix_none_after_horizon :
  forall alg candidates_of jobs H t cpu,
    H <= t ->
    generated_schedule_prefix alg candidates_of jobs H t cpu = None.
Proof.
  intros alg candidates_of jobs H.
  induction H as [|H IH]; intros t cpu Hle.
  - reflexivity.
  - simpl.
    destruct (Nat.ltb t H) eqn:Hlt.
    + apply Nat.ltb_lt in Hlt. lia.
    + destruct (Nat.eqb t H) eqn:Heq.
      * apply Nat.eqb_eq in Heq. lia.
      * reflexivity.
Qed.

Lemma generated_schedule_prefix_other_cpu_none :
  forall alg candidates_of jobs H t cpu,
    0 < cpu ->
    generated_schedule_prefix alg candidates_of jobs H t cpu = None.
Proof.
  intros alg candidates_of jobs H.
  induction H as [|H IH]; intros t cpu Hcpu.
  - reflexivity.
  - simpl.
    destruct (Nat.ltb t H) eqn:Hlt.
    + apply IH. exact Hcpu.
    + destruct (Nat.eqb t H) eqn:Heq.
      * destruct (Nat.eqb cpu 0) eqn:Hcpu0.
        -- apply Nat.eqb_eq in Hcpu0. lia.
        -- reflexivity.
      * reflexivity.
Qed.

Lemma check_prefix_slots_match_schedule_cpu0 :
  forall sched c t,
    check_prefix_slots_match_schedule sched c = true ->
    t < c.(prefix_horizon) ->
    nth t c.(prefix_slots) None = sched t 0.
Proof.
  intros sched c t Hcheck Ht.
  unfold check_prefix_slots_match_schedule in Hcheck.
  apply andb_true_iff in Hcheck.
  destruct Hcheck as [_ Hslots].
  apply forallb_forall with (x := t) in Hslots.
  - apply option_job_eqb_true_iff.
    exact Hslots.
  - rewrite in_seq.
    lia.
Qed.

Lemma check_prefix_slots_match_schedule_shape :
  forall sched c,
    check_prefix_slots_match_schedule sched c = true ->
    check_prefix_cert c = true.
Proof.
  intros sched c Hcheck.
  unfold check_prefix_slots_match_schedule in Hcheck.
  apply andb_true_iff in Hcheck.
  exact (proj1 Hcheck).
Qed.

Theorem check_prefix_slots_match_generated_edf_pointwise :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs) c t cpu,
    check_prefix_slots_match_generated_edf
      T tasks offset jobs enumT codec c = true ->
    schedule_of_slots c.(prefix_slots) t cpu =
    generated_periodic_edf_prefix T tasks offset jobs enumT codec c t cpu.
Proof.
  intros T tasks offset jobs enumT codec c t cpu Hcheck.
  pose proof
    (check_prefix_slots_match_schedule_shape
       (generated_periodic_edf_prefix T tasks offset jobs enumT codec c)
       c Hcheck) as Hshape.
  destruct cpu as [|cpu'].
  - unfold schedule_of_slots.
    rewrite Nat.eqb_refl.
    destruct (Nat.lt_ge_cases t c.(prefix_horizon)) as [Ht | Ht].
    + eapply check_prefix_slots_match_schedule_cpu0; eauto.
    + rewrite (nth_prefix_slots_none_after_horizon c t Hshape Ht).
      symmetry.
      unfold generated_periodic_edf_prefix.
      apply generated_schedule_prefix_none_after_horizon.
      exact Ht.
  - unfold schedule_of_slots.
    destruct (Nat.eqb_spec (S cpu') 0); [lia|].
    symmetry.
    unfold generated_periodic_edf_prefix.
    apply generated_schedule_prefix_other_cpu_none.
    lia.
Qed.

Theorem check_prefix_slots_match_generated_edf_agrees_before :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs) c,
    check_prefix_slots_match_generated_edf
      T tasks offset jobs enumT codec c = true ->
    agrees_before
      (schedule_of_slots c.(prefix_slots))
      (generated_periodic_edf_prefix T tasks offset jobs enumT codec c)
      c.(prefix_horizon).
Proof.
  intros T tasks offset jobs enumT codec c Hcheck t cpu _.
  eapply check_prefix_slots_match_generated_edf_pointwise.
  exact Hcheck.
Qed.

Lemma pointwise_agrees_before :
  forall s1 s2 t,
    (forall t' cpu, s1 t' cpu = s2 t' cpu) ->
    agrees_before s1 s2 t.
Proof.
  intros s1 s2 t Heq t' cpu _.
  apply Heq.
Qed.

Theorem checked_prefix_semantics_on_generated_edf :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs) c,
    check_prefix_cert_semantic jobs c = true ->
    check_prefix_slots_match_generated_edf
      T tasks offset jobs enumT codec c = true ->
    EDFPrefixCertSemantics
      jobs c
      (generated_periodic_edf_prefix T tasks offset jobs enumT codec c).
Proof.
  intros T tasks offset jobs enumT codec c Hsem Hmatch.
  pose proof (check_prefix_cert_semantic_sound jobs c Hsem) as Hslot_sem.
  pose proof
    (check_prefix_slots_match_generated_edf_pointwise
       T tasks offset jobs enumT codec c) as Hpoint.
  constructor.
  - intros t Ht.
    rewrite <- (Hpoint t 0 Hmatch).
    unfold schedule_of_slots.
    rewrite Nat.eqb_refl.
    reflexivity.
  - intros i j t Hj Ht.
    pose proof
      (prefix_completed_by_semantics
         jobs c (schedule_of_slots c.(prefix_slots)) Hslot_sem
         i j t Hj Ht) as Hcompleted.
    apply (proj1 (agrees_before_completed
                    jobs 1
                    (schedule_of_slots c.(prefix_slots))
                    (generated_periodic_edf_prefix T tasks offset jobs enumT codec c)
                    j t
                    (pointwise_agrees_before
                       (schedule_of_slots c.(prefix_slots))
                       (generated_periodic_edf_prefix T tasks offset jobs enumT codec c)
                       t
                       (fun t' cpu => Hpoint t' cpu Hmatch)))).
    exact Hcompleted.
  - intros i row j b ji jj Hrow Hcell Hji Hjj Hb.
    pose proof
      (prefix_backlog_free_semantics
         jobs c (schedule_of_slots c.(prefix_slots)) Hslot_sem
         i row j b ji jj Hrow Hcell Hji Hjj Hb) as Hcompleted.
    apply (proj1 (agrees_before_completed
                    jobs 1
                    (schedule_of_slots c.(prefix_slots))
                    (generated_periodic_edf_prefix T tasks offset jobs enumT codec c)
                    jj (job_release (jobs ji))
                    (pointwise_agrees_before
                       (schedule_of_slots c.(prefix_slots))
                       (generated_periodic_edf_prefix T tasks offset jobs enumT codec c)
                       (job_release (jobs ji))
                       (fun t' cpu => Hpoint t' cpu Hmatch)))).
    exact Hcompleted.
Qed.
