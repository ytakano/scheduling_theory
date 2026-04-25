From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Semantics.ScheduleLemmas.ScheduleFacts.
From RocqSched Require Import Semantics.ScheduleLemmas.SchedulePrefix.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Uniprocessor.Generic.FinitePrefixScheduleWitness.
From RocqSched Require Import TaskModels.Periodic.PeriodicCodec.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFCertificate.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFExtractionDecision.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFExtractionSoundness.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFExtractionTypes.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFGeneratedPrefixChecker.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFInfiniteBridge.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFPrefixChecker.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFPrefixCoherence.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFTransportAlgebra.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFTransportCoverageChecker.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFTransportWitnessChecker.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFWindowTransportChecker.
From RocqSched Require Import TaskModels.Periodic.PeriodicConcreteAnalysis.
From RocqSched Require Import TaskModels.Periodic.PeriodicEnumeration.
From RocqSched Require Import TaskModels.Periodic.PeriodicInfinite.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Periodic.PeriodicWindowDemandBound.
From RocqSched Require Import Uniprocessor.Policies.EDF.

Import ListNotations.

(** Top-level checked periodic EDF certificate wrapper.

    This file collects the boolean checkers that have been proved so far into a
    single extraction-facing entry point.  Coverage of all periodic jobs and the
    remaining schedule-level window transport facts are still explicit semantic
    obligations; the purpose here is to make the verified boolean frontier
    visible as one checker before exposing it to extraction. *)

Record PeriodicEDFCheckedSidecarCert := {
  checked_candidate_jobs : list JobId;
  checked_class_relevant_jobs : list (list JobId);
  checked_window_target_certs : list EDFWindowTransportTargetCert;
  checked_post_reset_window_target_certs : list EDFWindowTransportTargetCert
}.

Definition extracted_taskset_nonempty
    (ts : list ExtractedPeriodicTask) : bool :=
  Nat.ltb 0 (length ts).

Definition extracted_periodic_codec
    (ts : list ExtractedPeriodicTask) :
  PeriodicCodec
    (extracted_task_scope ts)
    (extracted_periodic_tasks ts)
    (fun _ => 0)
    (extracted_periodic_jobs ts).
Proof.
  destruct ts as [|τ ts'].
  - refine
      (mkPeriodicCodec
         (extracted_task_scope [])
         (extracted_periodic_tasks [])
         (fun _ => 0)
         (extracted_periodic_jobs [])
         (fun _ _ => 0)
         _ _).
    + intros τ k Hτ.
      unfold extracted_task_scope in Hτ.
      cbn in Hτ.
      lia.
    + intros j Hj.
      unfold periodic_jobset, extracted_task_scope in Hj.
      cbn in Hj.
      lia.
  - apply zero_offset_periodic_codec_of_tasks.
    + apply enumT_of_extracted_list_nodup.
    + apply extracted_enum_complete.
    + apply extracted_enum_sound.
    + unfold enumT_of_extracted_list.
      rewrite length_seq.
      cbn.
      lia.
Defined.

Lemma extracted_periodic_job_cost_exact :
  forall ts j,
    periodic_jobset
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      j ->
    job_cost (extracted_periodic_jobs ts j) =
    task_cost
      (extracted_periodic_tasks ts (job_task (extracted_periodic_jobs ts j))).
Proof.
  intros ts j Hjob.
  unfold extracted_periodic_jobs.
  eapply canonical_periodic_job_cost_exact.
  - apply extracted_enum_complete.
  - exact Hjob.
Qed.

Lemma extracted_periodic_same_task_job_cost :
  forall ts j1 j2,
    periodic_jobset
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      j1 ->
    periodic_jobset
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      j2 ->
    job_task (extracted_periodic_jobs ts j1) =
    job_task (extracted_periodic_jobs ts j2) ->
    job_cost (extracted_periodic_jobs ts j1) =
    job_cost (extracted_periodic_jobs ts j2).
Proof.
  intros ts j1 j2 Hj1 Hj2 Htask.
  rewrite (extracted_periodic_job_cost_exact ts j1 Hj1).
  rewrite (extracted_periodic_job_cost_exact ts j2 Hj2).
  rewrite Htask.
  reflexivity.
Qed.

Lemma extracted_periodic_hyperperiod_shifted_service_pair_of_transport :
  forall ts target x target0 x0 target_step x_step n,
    periodic_jobset
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      target0 ->
    periodic_jobset
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      x0 ->
    transport_rep_to_target_job
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (extracted_periodic_codec ts)
      target0 target target_step n ->
    transport_rep_to_target_job
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (extracted_periodic_codec ts)
      x0 x x_step n ->
    target_step * n *
      task_period
        (extracted_periodic_tasks ts
           (job_task (extracted_periodic_jobs ts target0))) =
      periodic_hyperperiod
        (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) * n ->
    x_step * n *
      task_period
        (extracted_periodic_tasks ts
           (job_task (extracted_periodic_jobs ts x0))) =
      periodic_hyperperiod
        (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) * n ->
    HyperperiodShiftedServicePair
      (extracted_periodic_tasks ts)
      (enumT_of_extracted_list ts)
      (extracted_periodic_jobs ts)
      target x target0 x0
      (periodic_hyperperiod
         (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) * n).
Proof.
  intros ts target x target0 x0 target_step x_step n
         Htarget0 Hx0 Htarget_transport Hx_transport
         Htarget_delta Hx_delta.
  eapply codec_hyperperiod_shifted_service_pair_of_transport.
  - exact (proj1 Htarget0).
  - exact (proj1 Hx0).
  - exact (proj2 Htarget0).
  - exact (proj2 Hx0).
  - exact Htarget_transport.
  - exact Hx_transport.
  - exact Htarget_delta.
  - exact Hx_delta.
  - assert (Hx : periodic_jobset
        (extracted_task_scope ts)
        (extracted_periodic_tasks ts)
        (fun _ => 0)
        (extracted_periodic_jobs ts)
        x).
    {
      unfold transport_rep_to_target_job in Hx_transport.
      subst x.
      split.
      - rewrite (codec_job_task
                   (extracted_task_scope ts)
                   (extracted_periodic_tasks ts)
                   (fun _ => 0)
                   (extracted_periodic_jobs ts)
                   (extracted_periodic_codec ts)
                   (job_task (extracted_periodic_jobs ts x0))
                   (job_index (extracted_periodic_jobs ts x0) +
                    x_step * n)
                   (proj1 Hx0)).
        exact (proj1 Hx0).
      - eapply codec_job_generated.
        exact (proj1 Hx0).
    }
    eapply extracted_periodic_same_task_job_cost.
    + exact Hx.
    + exact Hx0.
    + unfold transport_rep_to_target_job in Hx_transport.
      subst x.
      rewrite (codec_job_task
                 (extracted_task_scope ts)
                 (extracted_periodic_tasks ts)
                 (fun _ => 0)
                 (extracted_periodic_jobs ts)
                 (extracted_periodic_codec ts)
                 (job_task (extracted_periodic_jobs ts x0))
                 (job_index (extracted_periodic_jobs ts x0) +
                  x_step * n)
                 (proj1 Hx0)).
      reflexivity.
Qed.

Lemma hyperperiod_block_no_boundary_same_delta :
  forall hp rx rt,
    0 < hp ->
    rx < rt ->
    ~ (exists boundary delta,
        hp <= boundary
        /\
        (exists n, delta = hp * n)
        /\
        boundary = hp + delta
        /\
        boundary <= rt
        /\
        rx < boundary) ->
    exists n,
      hp * n <= rx /\ rt < hp * S n.
Proof.
  intros hp rx rt Hhp Hrx_rt Hno_boundary.
  exists (rx / hp).
  split.
  - pose proof (Nat.div_mod rx hp ltac:(lia)) as Hdiv.
    lia.
  - assert (Hrx_next : rx < hp * S (rx / hp)).
    {
      pose proof (Nat.div_mod rx hp ltac:(lia)) as Hdiv.
      pose proof (Nat.mod_upper_bound rx hp ltac:(lia)) as Hmod.
      lia.
    }
    destruct (lt_dec rt (hp * S (rx / hp))) as [Hrt|Hnrt];
      [exact Hrt|].
    exfalso.
    apply Hno_boundary.
    exists (hp * S (rx / hp)), (hp * (rx / hp)).
    repeat split.
    + lia.
    + exists (rx / hp).
      reflexivity.
    + lia.
    + lia.
    + exact Hrx_next.
Qed.

Lemma extracted_periodic_shift_back_job_by_hyperperiod :
  forall ts j n,
    extracted_taskset_wf ts = true ->
    periodic_jobset
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      j ->
    periodic_hyperperiod
      (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) * n <=
    job_release (extracted_periodic_jobs ts j) ->
    exists j0 step,
      periodic_jobset
        (extracted_task_scope ts)
        (extracted_periodic_tasks ts)
        (fun _ => 0)
        (extracted_periodic_jobs ts)
        j0
      /\
      transport_rep_to_target_job
        (extracted_task_scope ts)
        (extracted_periodic_tasks ts)
        (fun _ => 0)
        (extracted_periodic_jobs ts)
        (extracted_periodic_codec ts)
        j0 j step n
      /\
      step * n *
        task_period
          (extracted_periodic_tasks ts
             (job_task (extracted_periodic_jobs ts j0))) =
      periodic_hyperperiod
        (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) * n.
Proof.
  intros ts j n Hwf Hjob Hrelease.
  set (T := extracted_task_scope ts).
  set (tasks := extracted_periodic_tasks ts).
  set (jobs := extracted_periodic_jobs ts).
  set (enumT := enumT_of_extracted_list ts).
  set (codec := extracted_periodic_codec ts).
  set (τ := job_task (jobs j)).
  set (k := job_index (jobs j)).
  set (hp := periodic_hyperperiod tasks enumT).
  assert (HT : T τ).
  {
    subst T τ jobs.
    exact (proj1 Hjob).
  }
  assert (Hgen : generated_by_periodic_task tasks (fun _ => 0) jobs j).
  {
    subst T tasks jobs.
    exact (proj2 Hjob).
  }
  assert (Hperiod_pos : 0 < task_period (tasks τ)).
  {
    subst T tasks τ.
    eapply extracted_tasks_well_formed_on_enum; eauto.
  }
  assert (Hin : In τ enumT).
  {
    subst T enumT τ.
    apply extracted_enum_complete.
    exact HT.
  }
  destruct (periodic_hyperperiod_divides tasks enumT τ Hin)
    as [step Hhp_div].
  assert (Hhp_eq : hp = task_period (tasks τ) * step).
  {
    subst hp.
    rewrite Hhp_div.
    apply Nat.mul_comm.
  }
  assert (Hrelease_eq :
    job_release (jobs j) = k * task_period (tasks τ)).
  {
    subst k τ.
    pose proof (generated_job_release tasks (fun _ => 0) jobs j Hgen)
      as Hrel.
    unfold expected_release in Hrel.
    cbn in Hrel.
    exact Hrel.
  }
  assert (Hidx_lower : step * n <= k).
  {
    assert (Hrelease' : hp * n <= job_release (jobs j)).
    {
      subst hp jobs tasks enumT.
      exact Hrelease.
    }
    rewrite Hrelease_eq in Hrelease'.
    rewrite Hhp_eq in Hrelease'.
    nia.
  }
  set (k0 := k - step * n).
  set (j0 :=
    global_periodic_job_id_of
      T tasks (fun _ => 0) jobs codec τ k0).
  exists j0, step.
  assert (Hj0_task : job_task (jobs j0) = τ).
  {
    subst j0 codec.
    apply codec_job_task.
    exact HT.
  }
  assert (Hj0_index : job_index (jobs j0) = k0).
  {
    subst j0 codec.
    apply codec_job_index.
    exact HT.
  }
  split.
  - split.
    + rewrite Hj0_task.
      exact HT.
    + subst j0 codec.
      eapply codec_job_generated.
      exact HT.
  - split.
    + unfold transport_rep_to_target_job.
      subst j0.
      rewrite Hj0_task.
      rewrite Hj0_index.
      replace (k0 + step * n) with k by (subst k0; lia).
      subst τ k.
      apply global_periodic_job_id_of_complete.
      exact Hjob.
    + rewrite Hj0_task.
      rewrite Hhp_eq.
      nia.
Qed.

Lemma extracted_periodic_shift_back_deadline_between_pair :
  forall ts target x n,
    extracted_taskset_wf ts = true ->
    periodic_jobset
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      target ->
    periodic_jobset_deadline_between
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      0
      (job_abs_deadline (extracted_periodic_jobs ts target))
      x ->
    job_release (extracted_periodic_jobs ts x) <
    job_release (extracted_periodic_jobs ts target) ->
    periodic_hyperperiod
      (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) * n <=
    job_release (extracted_periodic_jobs ts x) ->
    job_release (extracted_periodic_jobs ts target) <
    periodic_hyperperiod
      (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) * S n ->
    exists target0 x0,
      periodic_jobset
        (extracted_task_scope ts)
        (extracted_periodic_tasks ts)
        (fun _ => 0)
        (extracted_periodic_jobs ts)
        target0
      /\
      job_release (extracted_periodic_jobs ts target0) <
        post_reset_target_candidate_horizon
          (extracted_periodic_tasks ts) (enumT_of_extracted_list ts)
      /\
      periodic_jobset_deadline_between
        (extracted_task_scope ts)
        (extracted_periodic_tasks ts)
        (fun _ => 0)
        (extracted_periodic_jobs ts)
        0
        (job_abs_deadline (extracted_periodic_jobs ts target0))
        x0
      /\
      job_release (extracted_periodic_jobs ts x0) <
      job_release (extracted_periodic_jobs ts target0)
      /\
      HyperperiodShiftedServicePair
        (extracted_periodic_tasks ts)
        (enumT_of_extracted_list ts)
        (extracted_periodic_jobs ts)
        target x target0 x0
        (periodic_hyperperiod
           (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) * n).
Proof.
  intros ts target x n Hwf Htarget Hbetween Hrelease_before
         Hx_after_delta Htarget_before_next.
  set (hp :=
    periodic_hyperperiod
      (extracted_periodic_tasks ts) (enumT_of_extracted_list ts)).
  assert (Hx : periodic_jobset
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      x).
  {
    split.
    - eapply periodic_jobset_deadline_between_implies_task_in_scope.
      exact Hbetween.
    - eapply periodic_jobset_deadline_between_implies_generated.
      exact Hbetween.
  }
  assert (Htarget_after_delta :
    hp * n <= job_release (extracted_periodic_jobs ts target)).
  {
    subst hp.
    lia.
  }
  destruct
    (extracted_periodic_shift_back_job_by_hyperperiod
       ts target n Hwf Htarget Htarget_after_delta)
    as [target0 [target_step
        [Htarget0 [Htarget_transport Htarget_delta]]]].
  destruct
    (extracted_periodic_shift_back_job_by_hyperperiod
       ts x n Hwf Hx Hx_after_delta)
    as [x0 [x_step [Hx0 [Hx_transport Hx_delta]]]].
  pose proof
    (extracted_periodic_hyperperiod_shifted_service_pair_of_transport
       ts target x target0 x0 target_step x_step n
       Htarget0 Hx0 Htarget_transport Hx_transport
       Htarget_delta Hx_delta) as Hshift.
  exists target0, x0.
  split; [exact Htarget0|].
  split.
  - destruct Hshift as [_ Htarget_release _ _ _ _].
    unfold post_reset_target_candidate_horizon.
    subst hp.
    rewrite Htarget_release in Htarget_before_next.
    lia.
  - split.
    + destruct Hshift as [_ Htarget_release Htarget_deadline
                          Hx_release Hx_deadline _].
      split.
      * exact (proj1 Hx0).
      * split.
        -- exact (proj2 Hx0).
        -- split; [lia|].
           pose proof
             (periodic_jobset_deadline_between_implies_deadline_le
                (extracted_task_scope ts)
                (extracted_periodic_tasks ts)
                (fun _ => 0)
                (extracted_periodic_jobs ts)
                0
                (job_abs_deadline (extracted_periodic_jobs ts target))
                x Hbetween) as Hdeadline_le.
           lia.
    + split.
      * destruct Hshift as [_ Htarget_release _ Hx_release _ _].
        lia.
      * exact Hshift.
Qed.

Definition check_periodic_hyperperiod_state_reset
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (enumT : list TaskId)
    (codec : PeriodicCodec T tasks offset jobs)
    (prefix_cert : EDFPrefixCert JobId)
    (hyperperiod : Time) : bool :=
  forallb
    (fun j =>
       certified_completed_by
         jobs prefix_cert.(prefix_slots) j hyperperiod)
    (enum_periodic_jobs_before
       T tasks offset jobs enumT codec hyperperiod).

Definition periodic_hyperperiod_state_reset
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (enumT : list TaskId)
    (codec : PeriodicCodec T tasks offset jobs)
    (prefix_cert : EDFPrefixCert JobId)
    (hyperperiod : Time) : Prop :=
  forall j,
    periodic_jobset T tasks offset jobs j ->
    job_release (jobs j) < hyperperiod ->
    completed jobs 1
      (generated_periodic_edf_prefix
         T tasks offset jobs enumT codec prefix_cert)
      j hyperperiod.

Theorem check_periodic_hyperperiod_state_reset_sound :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs)
         prefix_cert hyperperiod,
    well_formed_periodic_tasks_on T tasks ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    check_prefix_slots_match_generated_edf
      T tasks offset jobs enumT codec prefix_cert = true ->
    check_periodic_hyperperiod_state_reset
      T tasks offset jobs enumT codec prefix_cert hyperperiod = true ->
    periodic_hyperperiod_state_reset
      T tasks offset jobs enumT codec prefix_cert hyperperiod.
Proof.
  intros T tasks offset jobs enumT codec prefix_cert hyperperiod
         Hwf HenumT_complete HenumT_sound Hmatch Hreset j Hj Hrelease.
  unfold check_periodic_hyperperiod_state_reset in Hreset.
  pose proof
    (enum_periodic_jobs_before_complete
       T tasks offset jobs enumT codec
       Hwf HenumT_complete hyperperiod j Hj Hrelease) as Hin.
  apply forallb_forall with (x := j) in Hreset; [|exact Hin].
  pose proof
    (certified_completed_by_sound
       jobs prefix_cert.(prefix_slots) j hyperperiod Hreset)
    as Hcompleted_slots.
  apply
    (proj1
       (agrees_before_completed
          jobs 1
          (schedule_of_slots prefix_cert.(prefix_slots))
          (generated_periodic_edf_prefix
             T tasks offset jobs enumT codec prefix_cert)
          j hyperperiod
          (pointwise_agrees_before
             (schedule_of_slots prefix_cert.(prefix_slots))
             (generated_periodic_edf_prefix
                T tasks offset jobs enumT codec prefix_cert)
             hyperperiod
             (fun t cpu =>
                check_prefix_slots_match_generated_edf_pointwise
                  T tasks offset jobs enumT codec prefix_cert
                  t cpu Hmatch)))).
  exact Hcompleted_slots.
Qed.

(** [transport_period] is an index shift, not a time shift.  Matching it to
    the time hyperperiod is a conservative common shift: for each task, one
    transport step advances time by a multiple of the hyperperiod. *)
Definition check_transport_period_is_hyperperiod
    (tasks : TaskId -> Task)
    (enumT : list TaskId)
    (transport_cert : EDFTransportCert JobId) : bool :=
  Nat.eqb
    transport_cert.(transport_period)
    (periodic_hyperperiod tasks enumT).

Theorem check_transport_period_is_hyperperiod_sound :
  forall tasks enumT transport_cert,
    check_transport_period_is_hyperperiod
      tasks enumT transport_cert = true ->
    transport_cert.(transport_period) =
      periodic_hyperperiod tasks enumT.
Proof.
  intros tasks enumT transport_cert Hcheck.
  unfold check_transport_period_is_hyperperiod in Hcheck.
  now apply Nat.eqb_eq in Hcheck.
Qed.

Definition check_prefix_horizon_covers_hyperperiod
    (tasks : TaskId -> Task)
    (enumT : list TaskId)
    (prefix_cert : EDFPrefixCert JobId) : bool :=
  Nat.leb
    (periodic_hyperperiod tasks enumT)
    prefix_cert.(prefix_horizon).

Theorem check_prefix_horizon_covers_hyperperiod_sound :
  forall tasks enumT prefix_cert,
    check_prefix_horizon_covers_hyperperiod tasks enumT prefix_cert = true ->
    periodic_hyperperiod tasks enumT <= prefix_cert.(prefix_horizon).
Proof.
  intros tasks enumT prefix_cert Hcheck.
  unfold check_prefix_horizon_covers_hyperperiod in Hcheck.
  now apply Nat.leb_le in Hcheck.
Qed.

Definition post_reset_window_horizon
    (tasks : TaskId -> Task)
    (enumT : list TaskId) : Time :=
  2 * periodic_hyperperiod tasks enumT +
  periodic_max_relative_deadline tasks enumT.

Definition check_prefix_horizon_covers_post_reset_window
    (tasks : TaskId -> Task)
    (enumT : list TaskId)
    (prefix_cert : EDFPrefixCert JobId) : bool :=
  Nat.leb
    (post_reset_window_horizon tasks enumT)
    prefix_cert.(prefix_horizon).

Theorem check_prefix_horizon_covers_post_reset_window_sound :
  forall tasks enumT prefix_cert,
    check_prefix_horizon_covers_post_reset_window tasks enumT prefix_cert = true ->
    post_reset_window_horizon tasks enumT <= prefix_cert.(prefix_horizon).
Proof.
  intros tasks enumT prefix_cert Hcheck.
  unfold check_prefix_horizon_covers_post_reset_window in Hcheck.
  now apply Nat.leb_le in Hcheck.
Qed.

Definition check_periodic_edf_checked_sidecar
    (ts : list ExtractedPeriodicTask)
    (codec :
      PeriodicCodec
        (extracted_task_scope ts)
        (extracted_periodic_tasks ts)
        (fun _ => 0)
        (extracted_periodic_jobs ts))
    (cert : EDFInfiniteCert JobId)
    (sidecar : PeriodicEDFCheckedSidecarCert) : bool :=
  check_prefix_cert_semantic
    (extracted_periodic_jobs ts)
    cert.(cert_prefix)
  && check_prefix_slots_match_generated_edf_fast
       (extracted_task_scope ts)
       (extracted_periodic_tasks ts)
       (fun _ => 0)
       (extracted_periodic_jobs ts)
       (enumT_of_extracted_list ts)
       codec
       cert.(cert_prefix)
  && check_periodic_hyperperiod_state_reset
       (extracted_task_scope ts)
       (extracted_periodic_tasks ts)
       (fun _ => 0)
       (extracted_periodic_jobs ts)
       (enumT_of_extracted_list ts)
       codec
       cert.(cert_prefix)
       (periodic_hyperperiod
          (extracted_periodic_tasks ts)
          (enumT_of_extracted_list ts))
  && check_transport_period_is_hyperperiod
       (extracted_periodic_tasks ts)
       (enumT_of_extracted_list ts)
       cert.(cert_transport)
  && check_prefix_horizon_covers_hyperperiod
       (extracted_periodic_tasks ts)
       (enumT_of_extracted_list ts)
       cert.(cert_prefix)
  && check_prefix_horizon_covers_post_reset_window
       (extracted_periodic_tasks ts)
       (enumT_of_extracted_list ts)
       cert.(cert_prefix)
  && check_transport_cert cert.(cert_transport)
  && check_transport_basis_nodup cert.(cert_transport)
  && check_transport_classes_rep_backlog
       cert.(cert_prefix)
       cert.(cert_transport).(transport_classes)
       sidecar.(checked_class_relevant_jobs)
  && check_transport_classes_rep_backlog_generated
       (extracted_task_scope ts)
       (extracted_periodic_tasks ts)
       (fun _ => 0)
       (extracted_periodic_jobs ts)
       (enumT_of_extracted_list ts)
       codec
       cert.(cert_prefix)
       cert.(cert_transport).(transport_classes)
  && check_transport_classes_rep_periodic_generated
       (extracted_task_scope ts)
       (extracted_periodic_tasks ts)
       (fun _ => 0)
       (extracted_periodic_jobs ts)
       (enumT_of_extracted_list ts)
       codec
       cert.(cert_transport).(transport_classes)
  && check_periodic_transport_residue_coverage
       cert.(cert_transport)
       (periodic_transport_residue_jobs
          (extracted_task_scope ts)
          (extracted_periodic_tasks ts)
          (fun _ => 0)
          (extracted_periodic_jobs ts)
          (enumT_of_extracted_list ts)
          codec
          cert.(cert_transport).(transport_period))
  && check_transport_residue_shifts cert.(cert_transport)
  && check_window_transport_targets_complete_with_pairs
       (extracted_task_scope ts)
       (extracted_periodic_tasks ts)
       (fun _ => 0)
       (extracted_periodic_jobs ts)
       (enumT_of_extracted_list ts)
       codec
       cert.(cert_transport)
       sidecar.(checked_window_target_certs)
  && check_window_generated_pair_semantics_all
       (extracted_task_scope ts)
       (extracted_periodic_tasks ts)
       (fun _ => 0)
       (extracted_periodic_jobs ts)
       (enumT_of_extracted_list ts)
       codec
       cert.(cert_transport)
       sidecar.(checked_window_target_certs)
  && check_window_generated_pair_completion_all
       (extracted_task_scope ts)
       (extracted_periodic_tasks ts)
       (fun _ => 0)
       (extracted_periodic_jobs ts)
       (enumT_of_extracted_list ts)
       codec
       sidecar.(checked_window_target_certs)
  && check_post_reset_window_targets_complete_with_pairs
       (extracted_task_scope ts)
       (extracted_periodic_tasks ts)
       (fun _ => 0)
       (extracted_periodic_jobs ts)
       (enumT_of_extracted_list ts)
       codec
       cert.(cert_transport)
       sidecar.(checked_post_reset_window_target_certs)
  && check_post_reset_window_target_basis_coverage
       cert.(cert_transport)
       sidecar.(checked_post_reset_window_target_certs)
  && check_post_reset_target_list_complete
       (post_reset_window_target_jobs
          (extracted_task_scope ts)
          (extracted_periodic_tasks ts)
          (fun _ => 0)
          (extracted_periodic_jobs ts)
          (enumT_of_extracted_list ts)
          codec)
       sidecar.(checked_post_reset_window_target_certs)
  && edf_schedulability_decide ts.

Definition check_periodic_edf_checked_sidecar_extracted
    (ts : list ExtractedPeriodicTask)
    (cert : EDFInfiniteCert JobId)
    (sidecar : PeriodicEDFCheckedSidecarCert) : bool :=
  extracted_taskset_nonempty ts
  && check_periodic_edf_checked_sidecar
       ts (extracted_periodic_codec ts) cert sidecar.

Lemma check_periodic_edf_checked_sidecar_fields :
  forall ts
         (codec :
          PeriodicCodec
            (extracted_task_scope ts)
            (extracted_periodic_tasks ts)
            (fun _ => 0)
            (extracted_periodic_jobs ts))
         cert sidecar,
    check_periodic_edf_checked_sidecar ts codec cert sidecar = true ->
    check_prefix_cert_semantic
      (extracted_periodic_jobs ts)
      cert.(cert_prefix) = true
    /\
    check_prefix_slots_match_generated_edf
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      codec
      cert.(cert_prefix) = true
    /\
    check_periodic_hyperperiod_state_reset
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      codec
      cert.(cert_prefix)
      (periodic_hyperperiod
         (extracted_periodic_tasks ts)
         (enumT_of_extracted_list ts)) = true
    /\
    cert.(cert_transport).(transport_period) =
      periodic_hyperperiod
        (extracted_periodic_tasks ts)
        (enumT_of_extracted_list ts)
    /\
    periodic_hyperperiod
      (extracted_periodic_tasks ts)
      (enumT_of_extracted_list ts) <=
      cert.(cert_prefix).(prefix_horizon)
    /\
    post_reset_window_horizon
      (extracted_periodic_tasks ts)
      (enumT_of_extracted_list ts) <=
      cert.(cert_prefix).(prefix_horizon)
    /\
    check_transport_cert cert.(cert_transport) = true
    /\
    check_transport_basis_nodup cert.(cert_transport) = true
    /\
    check_transport_classes_rep_backlog
      cert.(cert_prefix)
      cert.(cert_transport).(transport_classes)
      sidecar.(checked_class_relevant_jobs) = true
    /\
    check_transport_classes_rep_backlog_generated
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      codec
      cert.(cert_prefix)
      cert.(cert_transport).(transport_classes) = true
    /\
    check_transport_classes_rep_periodic_generated
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      codec
      cert.(cert_transport).(transport_classes) = true
    /\
    check_periodic_transport_residue_coverage
      cert.(cert_transport)
      (periodic_transport_residue_jobs
        (extracted_task_scope ts)
        (extracted_periodic_tasks ts)
        (fun _ => 0)
        (extracted_periodic_jobs ts)
        (enumT_of_extracted_list ts)
        codec
        cert.(cert_transport).(transport_period)) = true
    /\
    check_transport_residue_shifts cert.(cert_transport) = true
    /\
    check_window_transport_targets_complete_with_pairs
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      codec
      cert.(cert_transport)
      sidecar.(checked_window_target_certs) = true
    /\
    check_window_generated_pair_semantics_all
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      codec
      cert.(cert_transport)
      sidecar.(checked_window_target_certs) = true
    /\
    check_window_generated_pair_completion_all
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      codec
      sidecar.(checked_window_target_certs) = true
    /\
    check_post_reset_window_targets_complete_with_pairs
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      codec
      cert.(cert_transport)
      sidecar.(checked_post_reset_window_target_certs) = true
    /\
    check_post_reset_window_target_basis_coverage
      cert.(cert_transport)
      sidecar.(checked_post_reset_window_target_certs) = true
    /\
    check_post_reset_target_list_complete
      (post_reset_window_target_jobs
        (extracted_task_scope ts)
        (extracted_periodic_tasks ts)
        (fun _ => 0)
        (extracted_periodic_jobs ts)
        (enumT_of_extracted_list ts)
        codec)
      sidecar.(checked_post_reset_window_target_certs) = true
    /\
    edf_schedulability_decide ts = true.
Proof.
  intros ts codec cert sidecar Hcheck.
  unfold check_periodic_edf_checked_sidecar in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as
    [[[[[[[[[[[[[[[[[[[Hprefix Hfast] Hreset] Hperiod_eq] Hhorizon]
        Hpost_reset_horizon]
        Htransport] Hbasis_nodup] Hrep] Hrep_generated] Hrep_periodic]
        Hcoverage] Hshifts] Hwindow] Hpair_semantics] Hpair_completion]
        Hpost_reset_window] Hpost_reset_basis] Hpost_reset_list] Hdec].
  repeat split; try assumption.
  - eapply check_prefix_slots_match_generated_edf_fast_sound.
    exact Hfast.
  - eapply check_transport_period_is_hyperperiod_sound.
    exact Hperiod_eq.
  - eapply check_prefix_horizon_covers_hyperperiod_sound.
    exact Hhorizon.
  - eapply check_prefix_horizon_covers_post_reset_window_sound.
    exact Hpost_reset_horizon.
Qed.

Lemma check_periodic_edf_checked_sidecar_wf :
  forall ts
         (codec :
          PeriodicCodec
            (extracted_task_scope ts)
            (extracted_periodic_tasks ts)
            (fun _ => 0)
            (extracted_periodic_jobs ts))
         cert sidecar,
    check_periodic_edf_checked_sidecar ts codec cert sidecar = true ->
    extracted_taskset_wf ts = true.
Proof.
  intros ts codec cert sidecar Hcheck.
  destruct
    (check_periodic_edf_checked_sidecar_fields
       ts codec cert sidecar Hcheck)
    as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hdec).
  unfold edf_schedulability_decide in Hdec.
  apply andb_true_iff in Hdec.
  exact (proj1 Hdec).
Qed.

Lemma check_periodic_edf_checked_sidecar_extracted_fields :
  forall ts cert sidecar,
    check_periodic_edf_checked_sidecar_extracted ts cert sidecar = true ->
    extracted_taskset_nonempty ts = true
    /\
    check_periodic_edf_checked_sidecar
      ts (extracted_periodic_codec ts) cert sidecar = true.
Proof.
  intros ts cert sidecar Hcheck.
  unfold check_periodic_edf_checked_sidecar_extracted in Hcheck.
  apply andb_true_iff in Hcheck.
  exact Hcheck.
Qed.

Lemma check_periodic_edf_checked_sidecar_hyperperiod_facts :
  forall ts
         (codec :
          PeriodicCodec
            (extracted_task_scope ts)
            (extracted_periodic_tasks ts)
            (fun _ => 0)
            (extracted_periodic_jobs ts))
         cert sidecar,
    check_periodic_edf_checked_sidecar ts codec cert sidecar = true ->
    periodic_hyperperiod_state_reset
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      codec
      cert.(cert_prefix)
      (periodic_hyperperiod
         (extracted_periodic_tasks ts)
         (enumT_of_extracted_list ts))
    /\
    cert.(cert_transport).(transport_period) =
      periodic_hyperperiod
        (extracted_periodic_tasks ts)
        (enumT_of_extracted_list ts).
Proof.
  intros ts codec cert sidecar Hcheck.
  destruct
    (check_periodic_edf_checked_sidecar_fields
       ts codec cert sidecar Hcheck)
    as (_ & Hmatch & Hreset_check & Hperiod_eq
        & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
  split.
  - eapply check_periodic_hyperperiod_state_reset_sound.
    + apply extracted_tasks_well_formed_on_enum.
      eapply check_periodic_edf_checked_sidecar_wf; eauto.
    + apply extracted_enum_complete.
    + apply extracted_enum_sound.
    + exact Hmatch.
    + exact Hreset_check.
  - exact Hperiod_eq.
Qed.

Lemma check_periodic_edf_checked_sidecar_post_reset_window_fact :
  forall ts
         (codec :
          PeriodicCodec
            (extracted_task_scope ts)
            (extracted_periodic_tasks ts)
            (fun _ => 0)
            (extracted_periodic_jobs ts))
         cert sidecar,
    check_periodic_edf_checked_sidecar ts codec cert sidecar = true ->
    post_reset_window_horizon
      (extracted_periodic_tasks ts)
      (enumT_of_extracted_list ts) <=
    cert.(cert_prefix).(prefix_horizon).
Proof.
  intros ts codec cert sidecar Hcheck.
  destruct
    (check_periodic_edf_checked_sidecar_fields
       ts codec cert sidecar Hcheck)
    as (_ & _ & _ & _ & _ & Hpost_reset_horizon
        & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
  exact Hpost_reset_horizon.
Qed.

Lemma periodic_hyperperiod_state_reset_completed_in_schedule_upto :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs)
         prefix_cert hyperperiod H j,
    well_formed_periodic_tasks_on T tasks ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    hyperperiod <= prefix_cert.(prefix_horizon) ->
    hyperperiod < H ->
    periodic_hyperperiod_state_reset
      T tasks offset jobs enumT codec prefix_cert hyperperiod ->
    periodic_jobset T tasks offset jobs j ->
    job_release (jobs j) < hyperperiod ->
    completed jobs 1
      (generated_periodic_edf_schedule_upto
         T tasks offset jobs H enumT codec)
      j hyperperiod.
Proof.
  intros T tasks offset jobs enumT codec prefix_cert hyperperiod H j
         Hwf HenumT_complete HenumT_sound Hhorizon HH
         Hreset Hj Hrelease.
  pose proof (Hreset j Hj Hrelease) as Hcompleted_prefix.
  assert (Hprefix_generated :
    completed jobs 1
      (generated_periodic_edf_schedule T tasks offset jobs enumT codec)
      j hyperperiod).
  {
    apply
      (proj1
         (agrees_before_completed
            jobs 1
            (generated_periodic_edf_prefix
               T tasks offset jobs enumT codec prefix_cert)
            (generated_periodic_edf_schedule
               T tasks offset jobs enumT codec)
            j hyperperiod
            (agrees_before_weaken
               (generated_periodic_edf_prefix
                  T tasks offset jobs enumT codec prefix_cert)
               (generated_periodic_edf_schedule
                  T tasks offset jobs enumT codec)
               hyperperiod
               prefix_cert.(prefix_horizon)
               Hhorizon
               (ltac:(
                  unfold generated_periodic_edf_prefix,
                         generated_periodic_edf_schedule;
                  apply generated_schedule_prefix_agrees_before))))).
    exact Hcompleted_prefix.
  }
  apply
    (proj2
       (generated_periodic_edf_schedule_upto_completed_iff_generated_before
          T tasks offset jobs enumT codec H j hyperperiod
          Hwf HenumT_complete HenumT_sound HH)).
  exact Hprefix_generated.
Qed.

Lemma periodic_hyperperiod_backlog_transport_of_checked_reset :
  forall ts
         (codec :
          PeriodicCodec
            (extracted_task_scope ts)
            (extracted_periodic_tasks ts)
            (fun _ => 0)
            (extracted_periodic_jobs ts))
         cert sidecar,
    check_periodic_edf_checked_sidecar ts codec cert sidecar = true ->
    PeriodicHyperperiodPostResetEarlierCompletionShiftObligation
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      codec
      cert.(cert_transport) ->
    PeriodicHyperperiodBacklogTransportObligation
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      codec
      cert.(cert_transport).
Proof.
  intros ts codec cert sidecar Hcheck Hpost.
  destruct
    (check_periodic_edf_checked_sidecar_fields
       ts codec cert sidecar Hcheck)
    as (_ & _ & _ & Hperiod_eq & Hhorizon_covers
        & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
  pose proof
    (check_periodic_edf_checked_sidecar_hyperperiod_facts
       ts codec cert sidecar Hcheck)
    as [Hreset Htransport_period_hyperperiod].
  pose proof
    (periodic_hyperperiod_earlier_completion_shift_of_post_reset_shift
       (extracted_task_scope ts)
       (extracted_periodic_tasks ts)
       (fun _ => 0)
       (extracted_periodic_jobs ts)
       (enumT_of_extracted_list ts)
       codec
       cert.(cert_transport)
       Hpost) as Hearlier.
  pose proof
    (periodic_hyperperiod_window_shift_of_earlier_completion_shift
       (extracted_task_scope ts)
       (extracted_periodic_tasks ts)
       (fun _ => 0)
       (extracted_periodic_jobs ts)
       (enumT_of_extracted_list ts)
       codec
       cert.(cert_transport)
       (extracted_tasks_well_formed_on_enum
          ts (check_periodic_edf_checked_sidecar_wf ts codec cert sidecar Hcheck))
       (extracted_enum_complete ts)
       (extracted_enum_sound ts)
       Hearlier) as Hshift.
  constructor.
  intros residue target q Hperiod_eq' Htarget Htransport Hresidue_backlog.
  refine
    (periodic_hyperperiod_window_shift
       (extracted_task_scope ts)
       (extracted_periodic_tasks ts)
       (fun _ => 0)
       (extracted_periodic_jobs ts)
       (enumT_of_extracted_list ts)
       codec
       cert.(cert_transport)
       Hshift
       residue target q
       Hperiod_eq'
       Htarget
       Htransport
       _
       Hresidue_backlog).
  intros Htarget_horizon x Hx Hrelease.
    eapply periodic_hyperperiod_state_reset_completed_in_schedule_upto.
    + apply extracted_tasks_well_formed_on_enum.
      eapply check_periodic_edf_checked_sidecar_wf; eauto.
    + apply extracted_enum_complete.
    + apply extracted_enum_sound.
    + exact Hhorizon_covers.
    + exact Htarget_horizon.
    + exact Hreset.
    + exact Hx.
    + exact Hrelease.
Qed.

Lemma check_periodic_edf_checked_sidecar_bounded_post_reset_coverage :
  forall ts
         (codec :
          PeriodicCodec
            (extracted_task_scope ts)
            (extracted_periodic_tasks ts)
            (fun _ => 0)
            (extracted_periodic_jobs ts))
         cert sidecar,
    check_periodic_edf_checked_sidecar ts codec cert sidecar = true ->
    BoundedPostResetWindowTargetCoverageObligation
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      codec
      sidecar.(checked_post_reset_window_target_certs).
Proof.
  intros ts codec cert sidecar Hcheck.
  destruct
    (check_periodic_edf_checked_sidecar_fields
       ts codec cert sidecar Hcheck)
    as (_ & _ & _ & _ & _ & _
        & Htransport_check & _ & _ & _ & _ & _ & _
        & _ & _ & _
        & Hpost_reset_window_check & Hpost_reset_basis_check
        & Hpost_reset_list_check & _).
  assert (Hpost_window_pairs :
    check_window_transport_targets_complete_with_pairs
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      codec
      cert.(cert_transport)
      sidecar.(checked_post_reset_window_target_certs) = true).
  {
    unfold check_post_reset_window_targets_complete_with_pairs
      in Hpost_reset_window_check.
    repeat rewrite andb_true_iff in Hpost_reset_window_check.
    tauto.
  }
  pose proof
    (bounded_post_reset_window_target_candidate_coverage_of_generated_jobs
       (extracted_task_scope ts)
       (extracted_periodic_tasks ts)
       (fun _ => 0)
       (extracted_periodic_jobs ts)
       (enumT_of_extracted_list ts)
       codec
       (extracted_tasks_well_formed_on_enum
          ts (check_periodic_edf_checked_sidecar_wf ts codec cert sidecar Hcheck))
       (extracted_enum_complete ts)) as Hcandidate_coverage.
  pose proof
    (bounded_post_reset_window_target_list_coverage_of_checked_candidates
       (extracted_task_scope ts)
       (extracted_periodic_tasks ts)
       (fun _ => 0)
       (extracted_periodic_jobs ts)
       (enumT_of_extracted_list ts)
       codec
       (post_reset_window_target_jobs
          (extracted_task_scope ts)
          (extracted_periodic_tasks ts)
          (fun _ => 0)
          (extracted_periodic_jobs ts)
          (enumT_of_extracted_list ts)
          codec)
       sidecar.(checked_post_reset_window_target_certs)
       Hpost_reset_list_check
       Hcandidate_coverage) as Hlist_coverage.
  pose proof
    (bounded_post_reset_window_target_basis_coverage_of_checked_targets
       (extracted_task_scope ts)
       (extracted_periodic_tasks ts)
       (fun _ => 0)
       (extracted_periodic_jobs ts)
       (enumT_of_extracted_list ts)
       codec
       cert.(cert_transport)
       sidecar.(checked_post_reset_window_target_certs)
       Htransport_check
       Hpost_reset_basis_check
       Hlist_coverage) as Hbasis_coverage.
  eapply bounded_post_reset_window_target_coverage_of_checked_basis.
  - apply extracted_tasks_well_formed_on_enum.
    eapply check_periodic_edf_checked_sidecar_wf; eauto.
  - apply extracted_enum_complete.
  - exact Hpost_window_pairs.
  - exact Hbasis_coverage.
Qed.

Theorem check_periodic_edf_checked_sidecar_extracted_block_service_source_obligation :
  forall ts cert sidecar,
    check_periodic_edf_checked_sidecar_extracted ts cert sidecar = true ->
    PeriodicHyperperiodBlockServiceSourceObligation
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      (extracted_periodic_codec ts)
      sidecar.(checked_post_reset_window_target_certs).
Proof.
  intros ts cert sidecar Hcheck.
  destruct
    (check_periodic_edf_checked_sidecar_extracted_fields
       ts cert sidecar Hcheck)
    as [_ Hchecked].
  pose proof
    (check_periodic_edf_checked_sidecar_wf
       ts (extracted_periodic_codec ts) cert sidecar Hchecked) as Hwf.
  pose proof
    (check_periodic_edf_checked_sidecar_bounded_post_reset_coverage
       ts (extracted_periodic_codec ts) cert sidecar Hchecked)
    as Hbounded_coverage.
  set (hp :=
    periodic_hyperperiod
      (extracted_periodic_tasks ts) (enumT_of_extracted_list ts)).
  assert (Hhp_pos : 0 < hp).
  {
    subst hp.
    apply periodic_hyperperiod_positive.
    intros τ Hin.
    apply extracted_tasks_well_formed_on_enum.
    - exact Hwf.
    - apply extracted_enum_sound.
      exact Hin.
  }
  constructor.
  intros target x Htarget Hbetween Hrelease_before_target Hpost_reset_case.
  assert (Hsource_pair :
    forall n,
      hp * n <= job_release (extracted_periodic_jobs ts x) ->
      job_release (extracted_periodic_jobs ts target) < hp * S n ->
      PeriodicHyperperiodBlockServiceSource
        (extracted_task_scope ts)
        (extracted_periodic_tasks ts)
        (fun _ => 0)
        (extracted_periodic_jobs ts)
        (enumT_of_extracted_list ts)
        (extracted_periodic_codec ts)
        sidecar.(checked_post_reset_window_target_certs)
        target x).
  {
    intros n Hx_after_delta Htarget_before_next.
    destruct
      (extracted_periodic_shift_back_deadline_between_pair
         ts target x n Hwf Htarget Hbetween Hrelease_before_target
         Hx_after_delta Htarget_before_next)
      as [target0 [x0 [Htarget0 [Htarget0_horizon
          [Hbetween0 [Hrelease0 Hshift]]]]]].
    assert (Htarget0_before_hp :
      job_release (extracted_periodic_jobs ts target0) < hp).
    {
      pose proof Hshift as Hshift_release.
      destruct Hshift_release as [_ Htarget_release _ _ _ _].
      subst hp.
      rewrite Htarget_release in Htarget_before_next.
      lia.
    }
    destruct
      (bounded_post_reset_window_target_coverage
         (extracted_task_scope ts)
         (extracted_periodic_tasks ts)
         (fun _ => 0)
         (extracted_periodic_jobs ts)
         (enumT_of_extracted_list ts)
         (extracted_periodic_codec ts)
         sidecar.(checked_post_reset_window_target_certs)
         Hbounded_coverage
         target0 x0 Htarget0 Htarget0_horizon Hbetween0 Hrelease0
         (or_introl Htarget0_before_hp))
      as [target_cert [p [Hin_cert [Htarget_cert [Hin_pair Hx0]]]]].
    eapply periodic_hyperperiod_block_service_source_pair
      with (target0 := target0) (x0 := x0)
           (target_cert := target_cert) (p := p)
           (delta := hp * n).
    - exact Htarget0.
    - exact Htarget0_horizon.
    - exact Hbetween0.
    - exact Hrelease0.
    - exact Hin_cert.
    - exact Htarget_cert.
    - exact Hin_pair.
    - exact Hx0.
    - subst hp.
      exact Hshift.
  }
  destruct Hpost_reset_case as [Htarget_before_hp | Hx_after_reset].
  - apply Hsource_pair with (n := 0); cbn; lia.
  - set (n := job_release (extracted_periodic_jobs ts x) / hp).
    assert (Hx_after_delta :
      hp * n <= job_release (extracted_periodic_jobs ts x)).
    {
      subst n.
      pose proof
        (Nat.div_mod
           (job_release (extracted_periodic_jobs ts x)) hp
           ltac:(lia)) as Hdiv.
      lia.
    }
    assert (Hx_before_next :
      job_release (extracted_periodic_jobs ts x) < hp * S n).
    {
      subst n.
      pose proof
        (Nat.div_mod
           (job_release (extracted_periodic_jobs ts x)) hp
           ltac:(lia)) as Hdiv.
      pose proof
        (Nat.mod_upper_bound
           (job_release (extracted_periodic_jobs ts x)) hp
           ltac:(lia)) as Hmod.
      lia.
    }
    destruct
      (lt_dec
         (job_release (extracted_periodic_jobs ts target))
         (hp * S n))
      as [Htarget_before_next | Htarget_not_before_next].
    + apply Hsource_pair with (n := n); assumption.
    + eapply periodic_hyperperiod_block_service_source_reset
        with (boundary := hp * S n) (delta := hp * n).
      * lia.
      * exists n.
        reflexivity.
      * lia.
      * lia.
      * exact Hx_before_next.
Qed.

Theorem check_periodic_edf_checked_sidecar_sound_with_completion_transport :
  forall ts
         (codec :
          PeriodicCodec
            (extracted_task_scope ts)
            (extracted_periodic_tasks ts)
            (fun _ => 0)
            (extracted_periodic_jobs ts))
         cert sidecar,
    check_periodic_edf_checked_sidecar ts codec cert sidecar = true ->
    TransportClassRepresentativeObligation
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      codec
      cert.(cert_prefix)
      cert.(cert_transport).(transport_classes)
      sidecar.(checked_class_relevant_jobs) ->
    PeriodicHyperperiodCompletionTransportObligation
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      codec
      sidecar.(checked_post_reset_window_target_certs) ->
    schedulable_by_on
      (periodic_jobset
        (extracted_task_scope ts)
        (extracted_periodic_tasks ts)
        (fun _ => 0)
        (extracted_periodic_jobs ts))
      (edf_scheduler
         (periodic_candidates_before
            (extracted_task_scope ts)
            (extracted_periodic_tasks ts)
            (fun _ => 0)
            (extracted_periodic_jobs ts)
            (enumT_of_extracted_list ts)
            codec))
      (extracted_periodic_jobs ts)
      1.
Proof.
  intros ts codec cert sidecar Hcheck Hrep Hcompletion_transport.
  destruct
    (check_periodic_edf_checked_sidecar_fields
       ts codec cert sidecar Hcheck)
    as (_ & _Hmatch & _Hreset_check & _Hperiod_eq & _Hhorizon_covers
        & _Hpost_reset_horizon
        & Htransport_check & Hbasis_nodup_check & Hrep_check
        & Hrep_generated_check & Hrep_periodic_check
        & Hresidue_check & Hshift_check
        & Hwindow_check & Hpair_semantics & Hpair_completion
        & _Hpost_reset_window_check & _Hpost_reset_basis_check
        & _Hpost_reset_list_check & Hdec).
  pose proof
    (check_periodic_edf_checked_sidecar_bounded_post_reset_coverage
       ts
       codec
       cert
       sidecar
       Hcheck) as Hbounded_coverage.
  pose proof
    (check_periodic_edf_checked_sidecar_hyperperiod_facts
       ts codec cert sidecar Hcheck)
    as [_Hhyperperiod_reset Htransport_period_hyperperiod].
  pose proof
    (periodic_hyperperiod_bounded_post_reset_lift_of_completion_transport
       (extracted_task_scope ts)
       (extracted_periodic_tasks ts)
       (fun _ => 0)
       (extracted_periodic_jobs ts)
       (enumT_of_extracted_list ts)
       codec
       cert.(cert_transport)
       sidecar.(checked_post_reset_window_target_certs)
       Hcompletion_transport) as Hbounded_lift.
  pose proof
    (periodic_hyperperiod_post_reset_earlier_completion_shift_of_bounded_checked_targets
       (extracted_task_scope ts)
       (extracted_periodic_tasks ts)
       (fun _ => 0)
       (extracted_periodic_jobs ts)
       (enumT_of_extracted_list ts)
       codec
       cert.(cert_transport)
       sidecar.(checked_post_reset_window_target_certs)
       Hbounded_lift
       Hbounded_coverage) as Hpost.
  pose proof
    (periodic_hyperperiod_backlog_transport_of_checked_reset
       ts codec cert sidecar Hcheck Hpost)
    as Hhyper_transport.
  eapply periodic_edf_schedulable_by_classical_dbf_with_periodic_hyperperiod_transport_generated_checks.
  - apply extracted_tasks_well_formed_on_enum.
    eapply check_periodic_edf_checked_sidecar_wf; eauto.
  - apply extracted_periodic_nonblocking.
  - apply enumT_of_extracted_list_nodup.
  - apply extracted_enum_complete.
  - apply extracted_enum_sound.
  - apply extracted_zero_offset.
  - exact Htransport_period_hyperperiod.
  - eapply check_periodic_transport_residue_coverage_period_pos.
    exact Hresidue_check.
  - exact Htransport_check.
  - exact Hbasis_nodup_check.
  - exact Hrep.
  - exact Hrep_check.
  - exact Hrep_generated_check.
  - exact Hrep_periodic_check.
  - eapply checked_periodic_transport_residue_coverage_sound.
    + exact Htransport_check.
    + apply extracted_enum_complete.
    + exact Hresidue_check.
  - exact Hshift_check.
  - exact Hwindow_check.
  - exact Hpair_semantics.
  - exact Hpair_completion.
  - exact Hhyper_transport.
  - apply edf_schedulability_decide_true_global_dbf_ok.
    exact Hdec.
Qed.

Theorem check_periodic_edf_checked_sidecar_sound_with_completion_transport_generated_rep :
  forall ts
         (codec :
          PeriodicCodec
            (extracted_task_scope ts)
            (extracted_periodic_tasks ts)
            (fun _ => 0)
            (extracted_periodic_jobs ts))
         cert sidecar,
    check_periodic_edf_checked_sidecar ts codec cert sidecar = true ->
    PeriodicHyperperiodCompletionTransportObligation
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      codec
      sidecar.(checked_post_reset_window_target_certs) ->
    schedulable_by_on
      (periodic_jobset
        (extracted_task_scope ts)
        (extracted_periodic_tasks ts)
        (fun _ => 0)
        (extracted_periodic_jobs ts))
      (edf_scheduler
         (periodic_candidates_before
            (extracted_task_scope ts)
            (extracted_periodic_tasks ts)
            (fun _ => 0)
            (extracted_periodic_jobs ts)
            (enumT_of_extracted_list ts)
            codec))
      (extracted_periodic_jobs ts)
      1.
Proof.
  intros ts codec cert sidecar Hcheck Hcompletion_transport.
  destruct
    (check_periodic_edf_checked_sidecar_fields
       ts codec cert sidecar Hcheck)
    as (Hprefix_sem & Hmatch & _Hreset_check & _Hperiod_eq
        & _Hhorizon_covers & _Hpost_reset_horizon
        & Htransport_check & Hbasis_nodup_check & _Hrep_check
        & Hrep_generated_check & Hrep_periodic_check
        & Hresidue_check & Hshift_check
        & Hwindow_check & Hpair_semantics & Hpair_completion
        & _Hpost_reset_window_check & _Hpost_reset_basis_check
        & _Hpost_reset_list_check & Hdec).
  pose proof
    (check_periodic_edf_checked_sidecar_bounded_post_reset_coverage
       ts codec cert sidecar Hcheck) as Hbounded_coverage.
  pose proof
    (check_periodic_edf_checked_sidecar_hyperperiod_facts
       ts codec cert sidecar Hcheck)
    as [_Hhyperperiod_reset Htransport_period_hyperperiod].
  pose proof
    (periodic_hyperperiod_bounded_post_reset_lift_of_completion_transport
       (extracted_task_scope ts)
       (extracted_periodic_tasks ts)
       (fun _ => 0)
       (extracted_periodic_jobs ts)
       (enumT_of_extracted_list ts)
       codec
       cert.(cert_transport)
       sidecar.(checked_post_reset_window_target_certs)
       Hcompletion_transport) as Hbounded_lift.
  pose proof
    (periodic_hyperperiod_post_reset_earlier_completion_shift_of_bounded_checked_targets
       (extracted_task_scope ts)
       (extracted_periodic_tasks ts)
       (fun _ => 0)
       (extracted_periodic_jobs ts)
       (enumT_of_extracted_list ts)
       codec
       cert.(cert_transport)
       sidecar.(checked_post_reset_window_target_certs)
       Hbounded_lift
       Hbounded_coverage) as Hpost.
  pose proof
    (periodic_hyperperiod_backlog_transport_of_checked_reset
       ts codec cert sidecar Hcheck Hpost)
    as Hhyper_transport.
  pose proof
    (transport_class_representative_obligation_of_generated_semantic_checks
       (extracted_task_scope ts)
       (extracted_periodic_tasks ts)
       (fun _ => 0)
       (extracted_periodic_jobs ts)
       (enumT_of_extracted_list ts)
       codec
       cert.(cert_prefix)
       cert.(cert_transport).(transport_classes)
       (extracted_tasks_well_formed_on_enum
          ts
          (check_periodic_edf_checked_sidecar_wf
             ts codec cert sidecar Hcheck))
       (extracted_enum_complete ts)
       (extracted_enum_sound ts)
       Hprefix_sem
       Hmatch
       Hrep_periodic_check) as Hrep_generated.
  eapply periodic_edf_schedulable_by_classical_dbf_with_periodic_hyperperiod_transport_generated_checks.
  - apply extracted_tasks_well_formed_on_enum.
    eapply check_periodic_edf_checked_sidecar_wf; eauto.
  - apply extracted_periodic_nonblocking.
  - apply enumT_of_extracted_list_nodup.
  - apply extracted_enum_complete.
  - apply extracted_enum_sound.
  - apply extracted_zero_offset.
  - exact Htransport_period_hyperperiod.
  - eapply check_periodic_transport_residue_coverage_period_pos.
    exact Hresidue_check.
  - exact Htransport_check.
  - exact Hbasis_nodup_check.
  - exact Hrep_generated.
  - rewrite <- check_transport_classes_rep_backlog_generated_eq.
    exact Hrep_generated_check.
  - exact Hrep_generated_check.
  - exact Hrep_periodic_check.
  - eapply checked_periodic_transport_residue_coverage_sound.
    + exact Htransport_check.
    + apply extracted_enum_complete.
    + exact Hresidue_check.
  - exact Hshift_check.
  - exact Hwindow_check.
  - exact Hpair_semantics.
  - exact Hpair_completion.
  - exact Hhyper_transport.
  - apply edf_schedulability_decide_true_global_dbf_ok.
    exact Hdec.
Qed.

Theorem check_periodic_edf_checked_sidecar_block_sound :
  forall ts
         (codec :
          PeriodicCodec
            (extracted_task_scope ts)
            (extracted_periodic_tasks ts)
            (fun _ => 0)
            (extracted_periodic_jobs ts))
         cert sidecar,
    check_periodic_edf_checked_sidecar ts codec cert sidecar = true ->
    TransportClassRepresentativeObligation
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      codec
      cert.(cert_prefix)
      cert.(cert_transport).(transport_classes)
      sidecar.(checked_class_relevant_jobs) ->
    PeriodicHyperperiodBlockServiceSourceObligation
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      codec
      sidecar.(checked_post_reset_window_target_certs) ->
    PeriodicHyperperiodServicePairTransportObligation
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      codec ->
    PeriodicHyperperiodBoundaryResetCompletionObligation
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      codec ->
    schedulable_by_on
      (periodic_jobset
        (extracted_task_scope ts)
        (extracted_periodic_tasks ts)
        (fun _ => 0)
        (extracted_periodic_jobs ts))
      (edf_scheduler
         (periodic_candidates_before
            (extracted_task_scope ts)
            (extracted_periodic_tasks ts)
            (fun _ => 0)
            (extracted_periodic_jobs ts)
            (enumT_of_extracted_list ts)
            codec))
      (extracted_periodic_jobs ts)
      1.
Proof.
  intros ts codec cert sidecar Hcheck Hrep Hsource_block
         Hpair_transport Hboundary_reset.
  destruct
    (check_periodic_edf_checked_sidecar_fields
       ts codec cert sidecar Hcheck)
    as (_ & _ & _ & _ & _ & _
        & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
        & Hpost_reset_window_check & _ & _ & _).
  assert (Hpost_reset_pair_completion :
    check_window_generated_pair_completion_all
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      codec
      sidecar.(checked_post_reset_window_target_certs) = true).
  {
    unfold check_post_reset_window_targets_complete_with_pairs
      in Hpost_reset_window_check.
    repeat rewrite andb_true_iff in Hpost_reset_window_check.
    tauto.
  }
  pose proof
    (periodic_hyperperiod_completion_transport_of_block_service_source
       (extracted_task_scope ts)
       (extracted_periodic_tasks ts)
       (fun _ => 0)
       (extracted_periodic_jobs ts)
       (enumT_of_extracted_list ts)
       codec
       sidecar.(checked_post_reset_window_target_certs)
       Hpost_reset_pair_completion
       Hsource_block
       Hpair_transport
       Hboundary_reset) as Hcompletion_transport.
  eapply check_periodic_edf_checked_sidecar_sound_with_completion_transport;
    eauto.
Qed.

Theorem check_periodic_edf_checked_sidecar_checked_block_sound :
  forall ts
         (codec :
          PeriodicCodec
            (extracted_task_scope ts)
            (extracted_periodic_tasks ts)
            (fun _ => 0)
            (extracted_periodic_jobs ts))
         cert sidecar,
    check_periodic_edf_checked_sidecar ts codec cert sidecar = true ->
    TransportClassRepresentativeObligation
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      codec
      cert.(cert_prefix)
      cert.(cert_transport).(transport_classes)
      sidecar.(checked_class_relevant_jobs) ->
    PeriodicHyperperiodCheckedBlockSourceNormalizationObligation
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      codec
      sidecar.(checked_post_reset_window_target_certs) ->
    PeriodicHyperperiodServicePairTransportObligation
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      codec ->
    PeriodicHyperperiodBoundaryResetCompletionObligation
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      codec ->
    schedulable_by_on
      (periodic_jobset
        (extracted_task_scope ts)
        (extracted_periodic_tasks ts)
        (fun _ => 0)
        (extracted_periodic_jobs ts))
      (edf_scheduler
         (periodic_candidates_before
            (extracted_task_scope ts)
            (extracted_periodic_tasks ts)
            (fun _ => 0)
            (extracted_periodic_jobs ts)
            (enumT_of_extracted_list ts)
            codec))
      (extracted_periodic_jobs ts)
      1.
Proof.
  intros ts codec cert sidecar Hcheck Hrep Hchecked_source
         Hpair_transport Hboundary_reset.
  eapply check_periodic_edf_checked_sidecar_block_sound.
  - exact Hcheck.
  - exact Hrep.
  - eapply periodic_hyperperiod_block_service_source_of_checked_normalization.
    exact Hchecked_source.
  - exact Hpair_transport.
  - exact Hboundary_reset.
Qed.

Theorem check_periodic_edf_checked_sidecar_checked_block_generated_rep_sound :
  forall ts
         (codec :
          PeriodicCodec
            (extracted_task_scope ts)
            (extracted_periodic_tasks ts)
            (fun _ => 0)
            (extracted_periodic_jobs ts))
         cert sidecar,
    check_periodic_edf_checked_sidecar ts codec cert sidecar = true ->
    PeriodicHyperperiodCheckedBlockSourceNormalizationObligation
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      codec
      sidecar.(checked_post_reset_window_target_certs) ->
    PeriodicHyperperiodServicePairTransportObligation
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      codec ->
    PeriodicHyperperiodBoundaryResetCompletionObligation
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      codec ->
    schedulable_by_on
      (periodic_jobset
        (extracted_task_scope ts)
        (extracted_periodic_tasks ts)
        (fun _ => 0)
        (extracted_periodic_jobs ts))
      (edf_scheduler
         (periodic_candidates_before
            (extracted_task_scope ts)
            (extracted_periodic_tasks ts)
            (fun _ => 0)
            (extracted_periodic_jobs ts)
            (enumT_of_extracted_list ts)
            codec))
      (extracted_periodic_jobs ts)
      1.
Proof.
  intros ts codec cert sidecar Hcheck Hchecked_source
         Hpair_transport Hboundary_reset.
  destruct
    (check_periodic_edf_checked_sidecar_fields
       ts codec cert sidecar Hcheck)
    as (_ & _ & _ & _ & _ & _
        & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
        & Hpost_reset_window_check & _ & _ & _).
  assert (Hpost_reset_pair_completion :
    check_window_generated_pair_completion_all
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      codec
      sidecar.(checked_post_reset_window_target_certs) = true).
  {
    unfold check_post_reset_window_targets_complete_with_pairs
      in Hpost_reset_window_check.
    repeat rewrite andb_true_iff in Hpost_reset_window_check.
    tauto.
  }
  pose proof
    (periodic_hyperperiod_completion_transport_of_block_service_source
       (extracted_task_scope ts)
       (extracted_periodic_tasks ts)
       (fun _ => 0)
       (extracted_periodic_jobs ts)
       (enumT_of_extracted_list ts)
       codec
       sidecar.(checked_post_reset_window_target_certs)
       Hpost_reset_pair_completion
       (periodic_hyperperiod_block_service_source_of_checked_normalization
          (extracted_task_scope ts)
          (extracted_periodic_tasks ts)
          (fun _ => 0)
          (extracted_periodic_jobs ts)
          (enumT_of_extracted_list ts)
          codec
          sidecar.(checked_post_reset_window_target_certs)
          Hchecked_source)
       Hpair_transport
       Hboundary_reset) as Hcompletion_transport.
  eapply check_periodic_edf_checked_sidecar_sound_with_completion_transport_generated_rep;
    eauto.
Qed.

Theorem check_periodic_edf_checked_sidecar_block_generated_rep_sound :
  forall ts
         (codec :
          PeriodicCodec
            (extracted_task_scope ts)
            (extracted_periodic_tasks ts)
            (fun _ => 0)
            (extracted_periodic_jobs ts))
         cert sidecar,
    check_periodic_edf_checked_sidecar ts codec cert sidecar = true ->
    PeriodicHyperperiodBlockServiceSourceObligation
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      codec
      sidecar.(checked_post_reset_window_target_certs) ->
    PeriodicHyperperiodServicePairTransportObligation
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      codec ->
    PeriodicHyperperiodBoundaryResetCompletionObligation
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      codec ->
    schedulable_by_on
      (periodic_jobset
        (extracted_task_scope ts)
        (extracted_periodic_tasks ts)
        (fun _ => 0)
        (extracted_periodic_jobs ts))
      (edf_scheduler
         (periodic_candidates_before
            (extracted_task_scope ts)
            (extracted_periodic_tasks ts)
            (fun _ => 0)
            (extracted_periodic_jobs ts)
            (enumT_of_extracted_list ts)
            codec))
      (extracted_periodic_jobs ts)
      1.
Proof.
  intros ts codec cert sidecar Hcheck Hsource_block
         Hpair_transport Hboundary_reset.
  destruct
    (check_periodic_edf_checked_sidecar_fields
       ts codec cert sidecar Hcheck)
    as (_ & _ & _ & _ & _ & _
        & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
        & Hpost_reset_window_check & _ & _ & _).
  assert (Hpost_reset_pair_completion :
    check_window_generated_pair_completion_all
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      codec
      sidecar.(checked_post_reset_window_target_certs) = true).
  {
    unfold check_post_reset_window_targets_complete_with_pairs
      in Hpost_reset_window_check.
    repeat rewrite andb_true_iff in Hpost_reset_window_check.
    tauto.
  }
  pose proof
    (periodic_hyperperiod_completion_transport_of_block_service_source
       (extracted_task_scope ts)
       (extracted_periodic_tasks ts)
       (fun _ => 0)
       (extracted_periodic_jobs ts)
       (enumT_of_extracted_list ts)
       codec
       sidecar.(checked_post_reset_window_target_certs)
       Hpost_reset_pair_completion
       Hsource_block
       Hpair_transport
       Hboundary_reset) as Hcompletion_transport.
  eapply check_periodic_edf_checked_sidecar_sound_with_completion_transport_generated_rep;
    eauto.
Qed.

Theorem check_periodic_edf_checked_sidecar_periodic_sound :
  forall ts
         (codec :
          PeriodicCodec
            (extracted_task_scope ts)
            (extracted_periodic_tasks ts)
            (fun _ => 0)
            (extracted_periodic_jobs ts))
         cert sidecar,
    check_periodic_edf_checked_sidecar ts codec cert sidecar = true ->
    TransportClassRepresentativeObligation
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      codec
      cert.(cert_prefix)
      cert.(cert_transport).(transport_classes)
      sidecar.(checked_class_relevant_jobs) ->
    PeriodicHyperperiodBlockServiceSourceObligation
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      codec
      sidecar.(checked_post_reset_window_target_certs) ->
    PeriodicHyperperiodGeneratedSchedulePeriodicity
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      codec ->
    schedulable_by_on
      (periodic_jobset
        (extracted_task_scope ts)
        (extracted_periodic_tasks ts)
        (fun _ => 0)
        (extracted_periodic_jobs ts))
      (edf_scheduler
         (periodic_candidates_before
            (extracted_task_scope ts)
            (extracted_periodic_tasks ts)
            (fun _ => 0)
            (extracted_periodic_jobs ts)
            (enumT_of_extracted_list ts)
            codec))
      (extracted_periodic_jobs ts)
      1.
Proof.
  intros ts codec cert sidecar Hcheck Hrep Hsource_block Hperiodicity.
  eapply check_periodic_edf_checked_sidecar_block_sound.
  - exact Hcheck.
  - exact Hrep.
  - exact Hsource_block.
  - eapply periodic_hyperperiod_service_pair_transport_of_periodicity.
    exact Hperiodicity.
  - eapply periodic_hyperperiod_boundary_reset_completion_of_periodicity.
    exact Hperiodicity.
Qed.

Theorem check_periodic_edf_checked_sidecar_sound :
  forall ts
         (codec :
          PeriodicCodec
            (extracted_task_scope ts)
            (extracted_periodic_tasks ts)
            (fun _ => 0)
            (extracted_periodic_jobs ts))
         cert sidecar,
    check_periodic_edf_checked_sidecar ts codec cert sidecar = true ->
    TransportClassRepresentativeObligation
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      codec
      cert.(cert_prefix)
      cert.(cert_transport).(transport_classes)
      sidecar.(checked_class_relevant_jobs) ->
    PeriodicHyperperiodServiceSourceNormalizationObligation
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      codec
      sidecar.(checked_post_reset_window_target_certs) ->
    PeriodicHyperperiodServicePairTransportObligation
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      codec ->
    schedulable_by_on
      (periodic_jobset
        (extracted_task_scope ts)
        (extracted_periodic_tasks ts)
        (fun _ => 0)
        (extracted_periodic_jobs ts))
      (edf_scheduler
         (periodic_candidates_before
            (extracted_task_scope ts)
            (extracted_periodic_tasks ts)
            (fun _ => 0)
            (extracted_periodic_jobs ts)
            (enumT_of_extracted_list ts)
            codec))
      (extracted_periodic_jobs ts)
      1.
Proof.
  intros ts codec cert sidecar Hcheck Hrep Hsource_normalization Hpair_transport.
  destruct
    (check_periodic_edf_checked_sidecar_fields
       ts codec cert sidecar Hcheck)
    as (_ & _Hmatch & _Hreset_check & _Hperiod_eq & Hhorizon_covers
        & _Hpost_reset_horizon
        & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
        & Hpost_reset_window_check & _ & _ & _).
  assert (Hpost_reset_pair_completion :
    check_window_generated_pair_completion_all
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      codec
      sidecar.(checked_post_reset_window_target_certs) = true).
  {
    unfold check_post_reset_window_targets_complete_with_pairs
      in Hpost_reset_window_check.
    repeat rewrite andb_true_iff in Hpost_reset_window_check.
    tauto.
  }
  pose proof
    (check_periodic_edf_checked_sidecar_hyperperiod_facts
       ts codec cert sidecar Hcheck)
    as [Hhyperperiod_reset _Htransport_period_hyperperiod].
  assert (Hreset_completion :
    forall target x,
      periodic_jobset
        (extracted_task_scope ts)
        (extracted_periodic_tasks ts)
        (fun _ => 0)
        (extracted_periodic_jobs ts)
        target ->
      periodic_jobset_deadline_between
        (extracted_task_scope ts)
        (extracted_periodic_tasks ts)
        (fun _ => 0)
        (extracted_periodic_jobs ts)
        0
        (job_abs_deadline (extracted_periodic_jobs ts target))
        x ->
      job_release (extracted_periodic_jobs ts x) <
        job_release (extracted_periodic_jobs ts target) ->
      periodic_hyperperiod
        (extracted_periodic_tasks ts)
        (enumT_of_extracted_list ts) <=
        job_release (extracted_periodic_jobs ts target) ->
      job_release (extracted_periodic_jobs ts x) <
        periodic_hyperperiod
          (extracted_periodic_tasks ts)
          (enumT_of_extracted_list ts) ->
      completed
        (extracted_periodic_jobs ts)
        1
        (generated_periodic_edf_schedule_upto
           (extracted_task_scope ts)
           (extracted_periodic_tasks ts)
           (fun _ => 0)
           (extracted_periodic_jobs ts)
           (S (job_abs_deadline (extracted_periodic_jobs ts target)))
           (enumT_of_extracted_list ts)
           codec)
        x
        (job_release (extracted_periodic_jobs ts target))).
  {
    intros target x Htarget Hbetween _Hrelease_before_target
           Htarget_after_reset Hx_before_reset.
    eapply completed_monotone.
    - exact Htarget_after_reset.
    - eapply periodic_hyperperiod_state_reset_completed_in_schedule_upto.
      + apply extracted_tasks_well_formed_on_enum.
        eapply check_periodic_edf_checked_sidecar_wf; eauto.
      + apply extracted_enum_complete.
      + apply extracted_enum_sound.
      + exact Hhorizon_covers.
      + destruct Htarget as [_ Htarget_generated].
        pose proof
          (generated_job_deadline
             (extracted_periodic_tasks ts)
             (fun _ => 0)
             (extracted_periodic_jobs ts)
             target
             Htarget_generated).
        lia.
      + exact Hhyperperiod_reset.
      + split.
        * exact (proj1 Hbetween).
        * exact (proj1 (proj2 Hbetween)).
      + exact Hx_before_reset.
  }
  pose proof
    (periodic_hyperperiod_completion_transport_of_service_source
       (extracted_task_scope ts)
       (extracted_periodic_tasks ts)
       (fun _ => 0)
       (extracted_periodic_jobs ts)
       (enumT_of_extracted_list ts)
       codec
       sidecar.(checked_post_reset_window_target_certs)
       Hpost_reset_pair_completion
       (periodic_hyperperiod_service_source_of_normalization
          (extracted_task_scope ts)
          (extracted_periodic_tasks ts)
          (fun _ => 0)
          (extracted_periodic_jobs ts)
          (enumT_of_extracted_list ts)
          codec
          sidecar.(checked_post_reset_window_target_certs)
          Hsource_normalization)
       Hpair_transport
       Hreset_completion) as Hcompletion_transport.
  eapply check_periodic_edf_checked_sidecar_sound_with_completion_transport;
    eauto.
Qed.

Theorem check_periodic_edf_checked_sidecar_extracted_block_sound :
  forall ts cert sidecar,
    check_periodic_edf_checked_sidecar_extracted ts cert sidecar = true ->
    TransportClassRepresentativeObligation
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      (extracted_periodic_codec ts)
      cert.(cert_prefix)
      cert.(cert_transport).(transport_classes)
      sidecar.(checked_class_relevant_jobs) ->
    PeriodicHyperperiodBlockServiceSourceObligation
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      (extracted_periodic_codec ts)
      sidecar.(checked_post_reset_window_target_certs) ->
    PeriodicHyperperiodServicePairTransportObligation
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      (extracted_periodic_codec ts) ->
    PeriodicHyperperiodBoundaryResetCompletionObligation
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      (extracted_periodic_codec ts) ->
    schedulable_by_on
      (periodic_jobset
        (extracted_task_scope ts)
        (extracted_periodic_tasks ts)
        (fun _ => 0)
        (extracted_periodic_jobs ts))
      (edf_scheduler
         (periodic_candidates_before
            (extracted_task_scope ts)
            (extracted_periodic_tasks ts)
            (fun _ => 0)
            (extracted_periodic_jobs ts)
            (enumT_of_extracted_list ts)
            (extracted_periodic_codec ts)))
      (extracted_periodic_jobs ts)
      1.
Proof.
  intros ts cert sidecar Hcheck Hrep Hsource_block
         Hpair_transport Hboundary_reset.
  destruct
    (check_periodic_edf_checked_sidecar_extracted_fields
       ts cert sidecar Hcheck)
    as [_ Hchecked].
  eapply check_periodic_edf_checked_sidecar_block_sound; eauto.
Qed.

Theorem check_periodic_edf_checked_sidecar_extracted_checked_block_sound :
  forall ts cert sidecar,
    check_periodic_edf_checked_sidecar_extracted ts cert sidecar = true ->
    TransportClassRepresentativeObligation
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      (extracted_periodic_codec ts)
      cert.(cert_prefix)
      cert.(cert_transport).(transport_classes)
      sidecar.(checked_class_relevant_jobs) ->
    PeriodicHyperperiodCheckedBlockSourceNormalizationObligation
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      (extracted_periodic_codec ts)
      sidecar.(checked_post_reset_window_target_certs) ->
    PeriodicHyperperiodServicePairTransportObligation
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      (extracted_periodic_codec ts) ->
    PeriodicHyperperiodBoundaryResetCompletionObligation
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      (extracted_periodic_codec ts) ->
    schedulable_by_on
      (periodic_jobset
        (extracted_task_scope ts)
        (extracted_periodic_tasks ts)
        (fun _ => 0)
        (extracted_periodic_jobs ts))
      (edf_scheduler
         (periodic_candidates_before
            (extracted_task_scope ts)
            (extracted_periodic_tasks ts)
            (fun _ => 0)
            (extracted_periodic_jobs ts)
            (enumT_of_extracted_list ts)
            (extracted_periodic_codec ts)))
      (extracted_periodic_jobs ts)
      1.
Proof.
  intros ts cert sidecar Hcheck Hrep Hchecked_source
         Hpair_transport Hboundary_reset.
  destruct
    (check_periodic_edf_checked_sidecar_extracted_fields
       ts cert sidecar Hcheck)
    as [_ Hchecked].
  eapply check_periodic_edf_checked_sidecar_checked_block_sound; eauto.
Qed.

Theorem check_periodic_edf_checked_sidecar_extracted_checked_block_generated_rep_sound :
  forall ts cert sidecar,
    check_periodic_edf_checked_sidecar_extracted ts cert sidecar = true ->
    PeriodicHyperperiodCheckedBlockSourceNormalizationObligation
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      (extracted_periodic_codec ts)
      sidecar.(checked_post_reset_window_target_certs) ->
    PeriodicHyperperiodServicePairTransportObligation
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      (extracted_periodic_codec ts) ->
    PeriodicHyperperiodBoundaryResetCompletionObligation
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      (extracted_periodic_codec ts) ->
    schedulable_by_on
      (periodic_jobset
        (extracted_task_scope ts)
        (extracted_periodic_tasks ts)
        (fun _ => 0)
        (extracted_periodic_jobs ts))
      (edf_scheduler
         (periodic_candidates_before
            (extracted_task_scope ts)
            (extracted_periodic_tasks ts)
            (fun _ => 0)
            (extracted_periodic_jobs ts)
            (enumT_of_extracted_list ts)
            (extracted_periodic_codec ts)))
      (extracted_periodic_jobs ts)
      1.
Proof.
  intros ts cert sidecar Hcheck Hchecked_source
         Hpair_transport Hboundary_reset.
  destruct
    (check_periodic_edf_checked_sidecar_extracted_fields
       ts cert sidecar Hcheck)
    as [_ Hchecked].
  eapply check_periodic_edf_checked_sidecar_checked_block_generated_rep_sound;
    eauto.
Qed.

Theorem check_periodic_edf_checked_sidecar_extracted_block_generated_rep_sound :
  forall ts cert sidecar,
    check_periodic_edf_checked_sidecar_extracted ts cert sidecar = true ->
    PeriodicHyperperiodBlockServiceSourceObligation
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      (extracted_periodic_codec ts)
      sidecar.(checked_post_reset_window_target_certs) ->
    PeriodicHyperperiodServicePairTransportObligation
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      (extracted_periodic_codec ts) ->
    PeriodicHyperperiodBoundaryResetCompletionObligation
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      (extracted_periodic_codec ts) ->
    schedulable_by_on
      (periodic_jobset
        (extracted_task_scope ts)
        (extracted_periodic_tasks ts)
        (fun _ => 0)
        (extracted_periodic_jobs ts))
      (edf_scheduler
         (periodic_candidates_before
            (extracted_task_scope ts)
            (extracted_periodic_tasks ts)
            (fun _ => 0)
            (extracted_periodic_jobs ts)
            (enumT_of_extracted_list ts)
            (extracted_periodic_codec ts)))
      (extracted_periodic_jobs ts)
      1.
Proof.
  intros ts cert sidecar Hcheck Hsource_block
         Hpair_transport Hboundary_reset.
  destruct
    (check_periodic_edf_checked_sidecar_extracted_fields
       ts cert sidecar Hcheck)
    as [_ Hchecked].
  eapply check_periodic_edf_checked_sidecar_block_generated_rep_sound;
    eauto.
Qed.

Theorem check_periodic_edf_checked_sidecar_extracted_block_source_generated_rep_sound :
  forall ts cert sidecar,
    check_periodic_edf_checked_sidecar_extracted ts cert sidecar = true ->
    PeriodicHyperperiodServicePairTransportObligation
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      (extracted_periodic_codec ts) ->
    PeriodicHyperperiodBoundaryResetCompletionObligation
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      (extracted_periodic_codec ts) ->
    schedulable_by_on
      (periodic_jobset
        (extracted_task_scope ts)
        (extracted_periodic_tasks ts)
        (fun _ => 0)
        (extracted_periodic_jobs ts))
      (edf_scheduler
         (periodic_candidates_before
            (extracted_task_scope ts)
            (extracted_periodic_tasks ts)
            (fun _ => 0)
            (extracted_periodic_jobs ts)
            (enumT_of_extracted_list ts)
            (extracted_periodic_codec ts)))
      (extracted_periodic_jobs ts)
      1.
Proof.
  intros ts cert sidecar Hcheck Hpair_transport Hboundary_reset.
  eapply check_periodic_edf_checked_sidecar_extracted_block_generated_rep_sound.
  - exact Hcheck.
  - eapply
      check_periodic_edf_checked_sidecar_extracted_block_service_source_obligation.
    exact Hcheck.
  - exact Hpair_transport.
  - exact Hboundary_reset.
Qed.

Theorem check_periodic_edf_checked_sidecar_extracted_periodic_generated_rep_sound :
  forall ts cert sidecar,
    check_periodic_edf_checked_sidecar_extracted ts cert sidecar = true ->
    PeriodicHyperperiodGeneratedSchedulePeriodicity
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      (extracted_periodic_codec ts) ->
    schedulable_by_on
      (periodic_jobset
        (extracted_task_scope ts)
        (extracted_periodic_tasks ts)
        (fun _ => 0)
        (extracted_periodic_jobs ts))
      (edf_scheduler
         (periodic_candidates_before
            (extracted_task_scope ts)
            (extracted_periodic_tasks ts)
            (fun _ => 0)
            (extracted_periodic_jobs ts)
            (enumT_of_extracted_list ts)
            (extracted_periodic_codec ts)))
      (extracted_periodic_jobs ts)
      1.
Proof.
  intros ts cert sidecar Hcheck Hperiodicity.
  eapply check_periodic_edf_checked_sidecar_extracted_block_source_generated_rep_sound.
  - exact Hcheck.
  - eapply periodic_hyperperiod_service_pair_transport_of_periodicity.
    exact Hperiodicity.
  - eapply periodic_hyperperiod_boundary_reset_completion_of_periodicity.
    exact Hperiodicity.
Qed.

Theorem check_periodic_edf_checked_sidecar_extracted_periodic_sound :
  forall ts cert sidecar,
    check_periodic_edf_checked_sidecar_extracted ts cert sidecar = true ->
    TransportClassRepresentativeObligation
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      (extracted_periodic_codec ts)
      cert.(cert_prefix)
      cert.(cert_transport).(transport_classes)
      sidecar.(checked_class_relevant_jobs) ->
    PeriodicHyperperiodBlockServiceSourceObligation
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      (extracted_periodic_codec ts)
      sidecar.(checked_post_reset_window_target_certs) ->
    PeriodicHyperperiodGeneratedSchedulePeriodicity
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      (extracted_periodic_codec ts) ->
    schedulable_by_on
      (periodic_jobset
        (extracted_task_scope ts)
        (extracted_periodic_tasks ts)
        (fun _ => 0)
        (extracted_periodic_jobs ts))
      (edf_scheduler
         (periodic_candidates_before
            (extracted_task_scope ts)
            (extracted_periodic_tasks ts)
            (fun _ => 0)
            (extracted_periodic_jobs ts)
            (enumT_of_extracted_list ts)
            (extracted_periodic_codec ts)))
      (extracted_periodic_jobs ts)
      1.
Proof.
  intros ts cert sidecar Hcheck Hrep Hsource_block Hperiodicity.
  destruct
    (check_periodic_edf_checked_sidecar_extracted_fields
       ts cert sidecar Hcheck)
    as [_ Hchecked].
  eapply check_periodic_edf_checked_sidecar_periodic_sound; eauto.
Qed.

Theorem check_periodic_edf_checked_sidecar_extracted_sound :
  forall ts cert sidecar,
    check_periodic_edf_checked_sidecar_extracted ts cert sidecar = true ->
    TransportClassRepresentativeObligation
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      (extracted_periodic_codec ts)
      cert.(cert_prefix)
      cert.(cert_transport).(transport_classes)
      sidecar.(checked_class_relevant_jobs) ->
    PeriodicHyperperiodServiceSourceNormalizationObligation
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      (extracted_periodic_codec ts)
      sidecar.(checked_post_reset_window_target_certs) ->
    PeriodicHyperperiodServicePairTransportObligation
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      (extracted_periodic_codec ts) ->
    schedulable_by_on
      (periodic_jobset
        (extracted_task_scope ts)
        (extracted_periodic_tasks ts)
        (fun _ => 0)
        (extracted_periodic_jobs ts))
      (edf_scheduler
         (periodic_candidates_before
            (extracted_task_scope ts)
            (extracted_periodic_tasks ts)
            (fun _ => 0)
            (extracted_periodic_jobs ts)
            (enumT_of_extracted_list ts)
            (extracted_periodic_codec ts)))
      (extracted_periodic_jobs ts)
      1.
Proof.
  intros ts cert sidecar Hcheck Hrep Hsource Hpair_transport.
  destruct
    (check_periodic_edf_checked_sidecar_extracted_fields
       ts cert sidecar Hcheck)
    as [_ Hchecked].
  eapply check_periodic_edf_checked_sidecar_sound; eauto.
Qed.
