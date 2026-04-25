From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia ZArith.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Semantics.ScheduleLemmas.ScheduleFacts.
From RocqSched Require Import Semantics.ScheduleLemmas.SchedulePrefix.
From RocqSched Require Import Semantics.ScheduleLemmas.ScheduleTransform.
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
From RocqSched Require Import Uniprocessor.Policies.EDFLemmas.

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

Lemma extracted_periodic_shift_forward_job_by_hyperperiod :
  forall ts j n,
    extracted_taskset_wf ts = true ->
    periodic_jobset
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      j ->
    exists j1 step,
      periodic_jobset
        (extracted_task_scope ts)
        (extracted_periodic_tasks ts)
        (fun _ => 0)
        (extracted_periodic_jobs ts)
        j1
      /\
      transport_rep_to_target_job
        (extracted_task_scope ts)
        (extracted_periodic_tasks ts)
        (fun _ => 0)
        (extracted_periodic_jobs ts)
        (extracted_periodic_codec ts)
        j j1 step n
      /\
      step * n *
        task_period
          (extracted_periodic_tasks ts
             (job_task (extracted_periodic_jobs ts j))) =
      periodic_hyperperiod
        (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) * n.
Proof.
  intros ts j n Hwf Hjob.
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
  set (j1 :=
    global_periodic_job_id_of
      T tasks (fun _ => 0) jobs codec τ (k + step * n)).
  exists j1, step.
  split.
  - split.
    + subst j1 codec.
      rewrite (codec_job_task
                 T tasks (fun _ => 0) jobs
                 (extracted_periodic_codec ts)
                 τ (k + step * n) HT).
      exact HT.
    + subst j1 codec.
      eapply codec_job_generated.
      exact HT.
  - split.
    + unfold transport_rep_to_target_job.
      subst j1 τ k.
      reflexivity.
    + subst hp τ jobs tasks enumT.
      rewrite Hhp_eq.
      nia.
Qed.

Definition extracted_periodic_hyperperiod_task_step
    (ts : list ExtractedPeriodicTask) (τ : TaskId) : nat :=
  periodic_hyperperiod
    (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) /
  task_period (extracted_periodic_tasks ts τ).

Definition extracted_periodic_shift_forward_job_id
    (ts : list ExtractedPeriodicTask) (n : nat) (j : JobId) : JobId :=
  let jobs := extracted_periodic_jobs ts in
  let τ := job_task (jobs j) in
  let step := extracted_periodic_hyperperiod_task_step ts τ in
  global_periodic_job_id_of
    (extracted_task_scope ts)
    (extracted_periodic_tasks ts)
    (fun _ => 0)
    jobs
    (extracted_periodic_codec ts)
    τ
    (job_index (jobs j) + step * n).

Lemma map_flat_map_local :
  forall (A B C : Type) (f : B -> C) (g : A -> list B) xs,
    map f (flat_map g xs) = flat_map (fun x => map f (g x)) xs.
Proof.
  intros A B C f g xs.
  induction xs as [|x xs IH]; simpl.
  - reflexivity.
  - rewrite map_app.
    rewrite IH.
    reflexivity.
Qed.

Lemma map_seq_add :
  forall start len shift,
    map (fun k => k + shift) (seq start len) =
    seq (start + shift) len.
Proof.
  intros start len.
  revert start.
  induction len as [|len IH]; intros start shift; simpl.
  - reflexivity.
  - f_equal.
    rewrite IH.
    replace (S start + shift) with (S (start + shift)) by lia.
    reflexivity.
Qed.

Lemma filter_shifted_release_window_indices :
  forall p s H,
    0 < p ->
    filter
      (fun k => Nat.leb (p * s) (k * p)
                && Nat.ltb (k * p) (p * s + H))
      (filter
         (fun k => Nat.ltb (k * p) (p * s + H))
         (seq 0 (p * s + H))) =
    map (fun k => k + s)
      (filter (fun k => Nat.ltb (k * p) H) (seq 0 H)).
Proof.
  intros p s H Hp.
  replace (p * s + H) with (s + (p * s + H - s)) by nia.
  rewrite seq_app.
  rewrite filter_app.
  rewrite filter_app.
  replace (s + (p * s + H - s)) with (p * s + H) by nia.
  assert (Hprefix :
    filter
      (fun x : nat =>
         (p * s <=? x * p) && (x * p <? p * s + H))
      (filter (fun k : nat => k * p <? p * s + H) (seq 0 s)) = []).
  {
    apply filter_all_false.
    intros k Hin.
    apply filter_In in Hin.
    destruct Hin as [Hin _].
    apply in_seq in Hin.
    destruct Hin as [_ Hklt].
    apply andb_false_intro1.
      apply Nat.leb_gt.
      nia.
  }
  rewrite Hprefix.
  simpl.
  replace (seq s (p * s + H - s)) with
    (seq (0 + s) (p * s + H - s)) by (replace (0 + s) with s by lia; reflexivity).
  rewrite <- map_seq_add with (start := 0) (len := p * s + H - s) (shift := s).
  assert (Hshift_filter :
    filter
      (fun x : nat =>
         (p * s <=? x * p) && (x * p <? p * s + H))
      (filter
         (fun k : nat => k * p <? p * s + H)
         (map (fun k : nat => k + s) (seq 0 (p * s + H - s)))) =
    map (fun k : nat => k + s)
      (filter (fun k : nat => k * p <? H) (seq 0 (p * s + H - s)))).
  {
    induction (seq 0 (p * s + H - s)) as [|k ks IH]; simpl.
    - reflexivity.
    - assert (Hbefore :
        ((k + s) * p <? p * s + H) =
        (k * p <? H)).
      {
        destruct (k * p <? H) eqn:Hlt.
        - apply Nat.ltb_lt in Hlt.
          apply Nat.ltb_lt.
          nia.
        - apply Nat.ltb_ge in Hlt.
          apply Nat.ltb_ge.
          nia.
      }
      rewrite Hbefore.
      destruct (k * p <? H) eqn:Hlt; simpl.
      + assert (Hpred :
          ((p * s <=? (k + s) * p)
           && ((k + s) * p <? p * s + H)) = true).
        {
          apply andb_true_iff.
          split.
          - apply Nat.leb_le.
            nia.
          - apply Nat.ltb_lt in Hlt.
            apply Nat.ltb_lt.
            nia.
        }
        rewrite Hpred.
        simpl.
        rewrite IH.
        reflexivity.
      + rewrite IH.
        reflexivity.
  }
  rewrite Hshift_filter.
  assert (Hextend :
    filter (fun k : nat => k * p <? H) (seq 0 (p * s + H - s)) =
    filter (fun k : nat => k * p <? H) (seq 0 H)).
  {
    replace (p * s + H - s) with (H + (p * s + H - s - H)) by nia.
    rewrite seq_app.
    rewrite filter_app.
    assert (Hsuffix :
      filter (fun k : nat => k * p <? H)
        (seq (0 + H) (p * s + H - s - H)) = []).
    {
      apply filter_all_false.
      intros k Hin.
      apply in_seq in Hin.
      destruct Hin as [Hlo _].
      apply Nat.ltb_ge.
      nia.
    }
    rewrite Hsuffix.
    rewrite app_nil_r.
    reflexivity.
  }
  rewrite Hextend.
  reflexivity.
Qed.

Lemma extracted_periodic_shift_forward_job_id_of :
  forall ts τ k n,
    extracted_taskset_wf ts = true ->
    extracted_task_scope ts τ ->
    extracted_periodic_shift_forward_job_id ts n
      (global_periodic_job_id_of
         (extracted_task_scope ts)
         (extracted_periodic_tasks ts)
         (fun _ => 0)
         (extracted_periodic_jobs ts)
         (extracted_periodic_codec ts)
         τ k) =
    global_periodic_job_id_of
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (extracted_periodic_codec ts)
      τ
      (k + extracted_periodic_hyperperiod_task_step ts τ * n).
Proof.
  intros ts τ k n _ HT.
  unfold extracted_periodic_shift_forward_job_id.
  rewrite
    (codec_job_task
       (extracted_task_scope ts)
       (extracted_periodic_tasks ts)
       (fun _ => 0)
       (extracted_periodic_jobs ts)
       (extracted_periodic_codec ts)
       τ k HT).
  rewrite
    (codec_job_index
       (extracted_task_scope ts)
       (extracted_periodic_tasks ts)
       (fun _ => 0)
       (extracted_periodic_jobs ts)
       (extracted_periodic_codec ts)
       τ k HT).
  reflexivity.
Qed.

Lemma extracted_periodic_hyperperiod_task_step_spec :
  forall ts τ,
    extracted_taskset_wf ts = true ->
    extracted_task_scope ts τ ->
    periodic_hyperperiod
      (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) =
    task_period (extracted_periodic_tasks ts τ) *
    extracted_periodic_hyperperiod_task_step ts τ.
Proof.
  intros ts τ Hwf HT.
  set (tasks := extracted_periodic_tasks ts).
  set (enumT := enumT_of_extracted_list ts).
  assert (Hin : In τ enumT).
  {
    subst enumT.
    apply extracted_enum_complete.
    exact HT.
  }
  destruct (periodic_hyperperiod_divides tasks enumT τ Hin)
    as [step Hhp_div].
  assert (Hperiod_pos : 0 < task_period (tasks τ)).
  {
    subst tasks.
    eapply extracted_tasks_well_formed_on_enum; eauto.
  }
  unfold extracted_periodic_hyperperiod_task_step.
  subst tasks enumT.
  rewrite Hhp_div.
  replace
    ((step * task_period (extracted_periodic_tasks ts τ)) /
     task_period (extracted_periodic_tasks ts τ))
    with step.
  - lia.
  - symmetry.
    apply Nat.div_mul.
    lia.
Qed.

Lemma extracted_periodic_indices_hyperperiod_shift_window :
  forall ts τ n H,
    extracted_taskset_wf ts = true ->
    extracted_task_scope ts τ ->
    let tasks := extracted_periodic_tasks ts in
    let hp := periodic_hyperperiod tasks (enumT_of_extracted_list ts) in
    let step := extracted_periodic_hyperperiod_task_step ts τ in
    filter
      (fun k =>
         Nat.leb (hp * n) (expected_release tasks (fun _ => 0) τ k)
         && Nat.ltb (expected_release tasks (fun _ => 0) τ k) (hp * n + H))
      (enum_periodic_indices_upto tasks (fun _ => 0) τ (hp * n + H)) =
    map (fun k => k + step * n)
      (enum_periodic_indices_upto tasks (fun _ => 0) τ H).
Proof.
  intros ts τ n H Hwf HT tasks hp step.
  subst tasks hp step.
  pose proof
    (extracted_periodic_hyperperiod_task_step_spec ts τ Hwf HT)
    as Hhp.
  assert (Hperiod_pos : 0 < task_period (extracted_periodic_tasks ts τ)).
  {
    eapply extracted_tasks_well_formed_on_enum; eauto.
  }
  unfold enum_periodic_indices_upto.
  rewrite Hhp.
  replace (task_period (extracted_periodic_tasks ts τ) *
             extracted_periodic_hyperperiod_task_step ts τ * n)
    with (task_period (extracted_periodic_tasks ts τ) *
          (extracted_periodic_hyperperiod_task_step ts τ * n)) by nia.
  unfold expected_release.
  cbn.
  apply filter_shifted_release_window_indices.
  exact Hperiod_pos.
Qed.

Lemma extracted_periodic_shift_forward_candidates_before_map :
  forall ts n H,
    extracted_taskset_wf ts = true ->
    map (extracted_periodic_shift_forward_job_id ts n)
      (enum_periodic_jobs_before
         (extracted_task_scope ts)
         (extracted_periodic_tasks ts)
         (fun _ => 0)
         (extracted_periodic_jobs ts)
         (enumT_of_extracted_list ts)
         (extracted_periodic_codec ts)
         H) =
    flat_map
      (fun τ =>
         map
           (global_periodic_job_id_of
              (extracted_task_scope ts)
              (extracted_periodic_tasks ts)
              (fun _ => 0)
              (extracted_periodic_jobs ts)
              (extracted_periodic_codec ts)
              τ)
           (map
              (fun k =>
                 k + extracted_periodic_hyperperiod_task_step ts τ * n)
              (enum_periodic_indices_upto
                 (extracted_periodic_tasks ts) (fun _ => 0) τ H)))
      (enumT_of_extracted_list ts).
Proof.
  intros ts n H Hwf.
  set (enumT := enumT_of_extracted_list ts).
  assert (HenumT_sound :
    forall τ, In τ enumT -> extracted_task_scope ts τ).
  {
    subst enumT.
    apply extracted_enum_sound.
  }
  unfold enum_periodic_jobs_before, enum_periodic_jobs_upto.
  fold enumT.
  rewrite map_flat_map_local.
  induction enumT as [|τ enumT IH]; simpl.
  - reflexivity.
  - f_equal.
    + rewrite !map_map.
      apply map_ext_in.
      intros k _.
      apply extracted_periodic_shift_forward_job_id_of.
      * exact Hwf.
      * apply HenumT_sound.
        left; reflexivity.
    + apply IH.
      intros τ' Hin.
      apply HenumT_sound.
      right; exact Hin.
Qed.

Lemma extracted_periodic_shift_forward_candidate_window_eq :
  forall ts n H,
    extracted_taskset_wf ts = true ->
    let hp :=
      periodic_hyperperiod
        (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) in
    filter
      (fun j =>
         Nat.leb (hp * n) (job_release (extracted_periodic_jobs ts j))
         && Nat.ltb (job_release (extracted_periodic_jobs ts j)) (hp * n + H))
      (enum_periodic_jobs_before
         (extracted_task_scope ts)
         (extracted_periodic_tasks ts)
         (fun _ => 0)
         (extracted_periodic_jobs ts)
         (enumT_of_extracted_list ts)
         (extracted_periodic_codec ts)
         (hp * n + H)) =
    map (extracted_periodic_shift_forward_job_id ts n)
      (enum_periodic_jobs_before
         (extracted_task_scope ts)
         (extracted_periodic_tasks ts)
         (fun _ => 0)
         (extracted_periodic_jobs ts)
         (enumT_of_extracted_list ts)
         (extracted_periodic_codec ts)
         H).
Proof.
  intros ts n H Hwf hp.
  subst hp.
  unfold enum_periodic_jobs_before at 1.
  rewrite
    (enum_periodic_jobs_upto_filter_release_range
       (extracted_task_scope ts)
       (extracted_periodic_tasks ts)
       (fun _ => 0)
       (extracted_periodic_jobs ts)
       (periodic_hyperperiod
          (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) * n + H)
       (enumT_of_extracted_list ts)
       (extracted_periodic_codec ts)
       (periodic_hyperperiod
          (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) * n)
       (periodic_hyperperiod
          (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) * n + H)
       (extracted_enum_sound ts)).
  rewrite extracted_periodic_shift_forward_candidates_before_map by exact Hwf.
  assert (Hflat :
    forall enumT,
      (forall τ, In τ enumT -> extracted_task_scope ts τ) ->
      flat_map
        (fun τ : TaskId =>
           map
             (global_periodic_job_id_of
                (extracted_task_scope ts)
                (extracted_periodic_tasks ts)
                (fun _ : TaskId => 0)
                (extracted_periodic_jobs ts)
                (extracted_periodic_codec ts) τ)
             (filter
                (fun k : nat =>
                   (periodic_hyperperiod
                      (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) *
                    n <=?
                    expected_release
                      (extracted_periodic_tasks ts) (fun _ : TaskId => 0) τ k)
                   &&
                   (expected_release
                      (extracted_periodic_tasks ts) (fun _ : TaskId => 0) τ k <?
                    periodic_hyperperiod
                      (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) *
                    n + H))
                (enum_periodic_indices_upto
                   (extracted_periodic_tasks ts) (fun _ : TaskId => 0) τ
                   (periodic_hyperperiod
                      (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) *
                    n + H))))
        enumT =
      flat_map
        (fun τ : TaskId =>
           map
             (global_periodic_job_id_of
                (extracted_task_scope ts)
                (extracted_periodic_tasks ts)
                (fun _ : TaskId => 0)
                (extracted_periodic_jobs ts)
                (extracted_periodic_codec ts) τ)
             (map
                (fun k : nat =>
                   k + extracted_periodic_hyperperiod_task_step ts τ * n)
                (enum_periodic_indices_upto
                   (extracted_periodic_tasks ts) (fun _ : TaskId => 0) τ H)))
        enumT).
  {
    intros enumT HenumT_sound.
    induction enumT as [|τ enumT IH]; simpl.
    - reflexivity.
    - f_equal.
      + rewrite extracted_periodic_indices_hyperperiod_shift_window.
        * reflexivity.
        * exact Hwf.
        * apply HenumT_sound.
          left; reflexivity.
      + apply IH.
        intros τ' Hin.
        apply HenumT_sound.
        right; exact Hin.
  }
  apply Hflat.
  apply extracted_enum_sound.
Qed.

Lemma extracted_periodic_shift_forward_job_id_sound :
  forall ts j n,
    extracted_taskset_wf ts = true ->
    periodic_jobset
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      j ->
    let j1 := extracted_periodic_shift_forward_job_id ts n j in
    let step :=
      extracted_periodic_hyperperiod_task_step
        ts (job_task (extracted_periodic_jobs ts j)) in
    periodic_jobset
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      j1
    /\
    transport_rep_to_target_job
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (extracted_periodic_codec ts)
      j j1 step n
    /\
    step * n *
      task_period
        (extracted_periodic_tasks ts
           (job_task (extracted_periodic_jobs ts j))) =
    periodic_hyperperiod
      (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) * n.
Proof.
  intros ts j n Hwf Hjob j1 step.
  set (T := extracted_task_scope ts).
  set (tasks := extracted_periodic_tasks ts).
  set (jobs := extracted_periodic_jobs ts).
  set (codec := extracted_periodic_codec ts).
  set (τ := job_task (jobs j)).
  set (k := job_index (jobs j)).
  assert (HT : T τ).
  {
    subst T τ jobs.
    exact (proj1 Hjob).
  }
  assert (Hstep :
    periodic_hyperperiod tasks (enumT_of_extracted_list ts) =
    task_period (tasks τ) * step).
  {
    subst tasks T τ step.
    apply extracted_periodic_hyperperiod_task_step_spec.
    - exact Hwf.
    - exact HT.
  }
  assert (Hj1_unfold :
    j1 =
    global_periodic_job_id_of
      T tasks (fun _ => 0) jobs codec τ (k + step * n)).
  {
    subst j1 step τ k jobs tasks T codec.
    unfold extracted_periodic_shift_forward_job_id.
    reflexivity.
  }
  split.
  - split.
    + rewrite Hj1_unfold.
      subst codec.
      rewrite (codec_job_task
                 T tasks (fun _ => 0) jobs
                 (extracted_periodic_codec ts)
                 τ (k + step * n) HT).
      exact HT.
    + rewrite Hj1_unfold.
      subst codec.
      eapply codec_job_generated.
      exact HT.
  - split.
    + unfold transport_rep_to_target_job.
      rewrite Hj1_unfold.
      subst τ k.
      reflexivity.
    + rewrite Hstep.
      nia.
Qed.

Lemma extracted_periodic_shift_forward_candidate_before_deterministic :
  forall ts j n t,
    extracted_taskset_wf ts = true ->
    periodic_jobset
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      j ->
    job_release (extracted_periodic_jobs ts j) < t ->
    In (extracted_periodic_shift_forward_job_id ts n j)
      (enum_periodic_jobs_before
         (extracted_task_scope ts)
         (extracted_periodic_tasks ts)
         (fun _ => 0)
         (extracted_periodic_jobs ts)
         (enumT_of_extracted_list ts)
         (extracted_periodic_codec ts)
         (t +
          periodic_hyperperiod
            (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) * n)).
Proof.
  intros ts j n t Hwf Hjob Hrelease_before.
  pose proof
    (extracted_periodic_shift_forward_job_id_sound
       ts j n Hwf Hjob)
    as [Hj1 [Htransport Hdelta]].
  assert (Hrelease_shift :
    job_release
      (extracted_periodic_jobs ts
         (extracted_periodic_shift_forward_job_id ts n j)) =
    job_release (extracted_periodic_jobs ts j) +
    periodic_hyperperiod
      (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) * n).
  {
    rewrite <- Hdelta.
    eapply codec_transport_target_release_shift.
    - exact (proj1 Hjob).
    - exact (proj2 Hjob).
    - exact Htransport.
  }
  eapply enum_periodic_jobs_before_complete.
  - apply extracted_tasks_well_formed_on_enum.
    exact Hwf.
  - apply extracted_enum_complete.
  - exact Hj1.
  - rewrite Hrelease_shift.
    lia.
Qed.

Lemma extracted_periodic_shift_forward_job_facts :
  forall ts j j1 step n,
    periodic_jobset
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      j ->
    periodic_jobset
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      j1 ->
    transport_rep_to_target_job
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (extracted_periodic_codec ts)
      j j1 step n ->
    step * n *
      task_period
        (extracted_periodic_tasks ts
           (job_task (extracted_periodic_jobs ts j))) =
    periodic_hyperperiod
      (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) * n ->
    job_task (extracted_periodic_jobs ts j1) =
      job_task (extracted_periodic_jobs ts j)
    /\
    job_release (extracted_periodic_jobs ts j1) =
      job_release (extracted_periodic_jobs ts j) +
      periodic_hyperperiod
        (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) * n
    /\
    job_abs_deadline (extracted_periodic_jobs ts j1) =
      job_abs_deadline (extracted_periodic_jobs ts j) +
      periodic_hyperperiod
        (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) * n
    /\
    job_cost (extracted_periodic_jobs ts j1) =
      job_cost (extracted_periodic_jobs ts j).
Proof.
  intros ts j j1 step n Hjob Hj1 Htransport Hdelta.
  assert (Htask :
    job_task (extracted_periodic_jobs ts j1) =
    job_task (extracted_periodic_jobs ts j)).
  {
    unfold transport_rep_to_target_job in Htransport.
    subst j1.
    rewrite
      (codec_job_task
         (extracted_task_scope ts)
         (extracted_periodic_tasks ts)
         (fun _ => 0)
         (extracted_periodic_jobs ts)
         (extracted_periodic_codec ts)
         (job_task (extracted_periodic_jobs ts j))
         (job_index (extracted_periodic_jobs ts j) + step * n)
         (proj1 Hjob)).
    reflexivity.
  }
  split; [exact Htask|].
  split.
  - rewrite <- Hdelta.
    eapply codec_transport_target_release_shift.
    + exact (proj1 Hjob).
    + exact (proj2 Hjob).
    + exact Htransport.
  - split.
    + rewrite <- Hdelta.
      eapply codec_transport_target_deadline_shift.
      * exact (proj1 Hjob).
      * exact (proj2 Hjob).
      * exact Htransport.
    + symmetry.
      eapply extracted_periodic_same_task_job_cost.
      * exact Hjob.
      * exact Hj1.
      * symmetry.
        exact Htask.
Qed.

Lemma extracted_periodic_shift_forward_eligibleb :
  forall ts j j1 step n sched0 sched1 t,
    periodic_jobset
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      j ->
    periodic_jobset
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      j1 ->
    transport_rep_to_target_job
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (extracted_periodic_codec ts)
      j j1 step n ->
    step * n *
      task_period
        (extracted_periodic_tasks ts
           (job_task (extracted_periodic_jobs ts j))) =
    periodic_hyperperiod
      (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) * n ->
    service_job 1 sched1 j1
      (t +
       periodic_hyperperiod
         (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) * n) =
    service_job 1 sched0 j t ->
    eligibleb
      (extracted_periodic_jobs ts) 1 sched1 j1
      (t +
       periodic_hyperperiod
         (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) * n) =
    eligibleb (extracted_periodic_jobs ts) 1 sched0 j t.
Proof.
  intros ts j j1 step n sched0 sched1 t
         Hjob Hj1 Htransport Hdelta Hservice.
  destruct
    (extracted_periodic_shift_forward_job_facts
       ts j j1 step n Hjob Hj1 Htransport Hdelta)
    as [_ [Hrelease [_ Hcost]]].
  unfold eligibleb.
  rewrite Hrelease.
  rewrite Hcost.
  rewrite Hservice.
  assert (Hreleaseb :
    (job_release (extracted_periodic_jobs ts j) +
       periodic_hyperperiod
         (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) * n
     <=?
     t +
       periodic_hyperperiod
         (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) * n) =
    (job_release (extracted_periodic_jobs ts j) <=? t)).
  {
    destruct (job_release (extracted_periodic_jobs ts j) <=? t)
      eqn:Hrel.
    - apply Nat.leb_le in Hrel.
      apply Nat.leb_le.
      lia.
    - apply Nat.leb_gt in Hrel.
      apply Nat.leb_gt.
      lia.
  }
  rewrite Hreleaseb.
  assert (Hblocked1 :
    job_blocked (extracted_periodic_jobs ts j1)
      (t +
       periodic_hyperperiod
         (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) * n) =
    false).
  {
    destruct
      (job_blocked (extracted_periodic_jobs ts j1)
         (t +
          periodic_hyperperiod
            (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) * n))
      eqn:Hblocked; [|reflexivity].
    exfalso.
    apply (extracted_periodic_nonblocking ts j1
             (t +
              periodic_hyperperiod
                (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) * n)
             Hj1).
    unfold blocked.
    exact Hblocked.
  }
  assert (Hblocked0 :
    job_blocked (extracted_periodic_jobs ts j) t = false).
  {
    destruct (job_blocked (extracted_periodic_jobs ts j) t) eqn:Hblocked;
      [|reflexivity].
    exfalso.
    apply (extracted_periodic_nonblocking ts j t Hjob).
    unfold blocked.
    exact Hblocked.
  }
  rewrite Hblocked1, Hblocked0.
  reflexivity.
Qed.

Lemma extracted_periodic_shift_forward_edf_metric_cmp :
  forall ts a b a1 b1 step_a step_b n,
    periodic_jobset
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      a ->
    periodic_jobset
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      b ->
    periodic_jobset
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      a1 ->
    periodic_jobset
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      b1 ->
    transport_rep_to_target_job
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (extracted_periodic_codec ts)
      a a1 step_a n ->
    transport_rep_to_target_job
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (extracted_periodic_codec ts)
      b b1 step_b n ->
    step_a * n *
      task_period
        (extracted_periodic_tasks ts
           (job_task (extracted_periodic_jobs ts a))) =
    periodic_hyperperiod
      (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) * n ->
    step_b * n *
      task_period
        (extracted_periodic_tasks ts
           (job_task (extracted_periodic_jobs ts b))) =
    periodic_hyperperiod
      (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) * n ->
    (edf_metric (extracted_periodic_jobs ts) a1
     <=? edf_metric (extracted_periodic_jobs ts) b1)%Z =
    (edf_metric (extracted_periodic_jobs ts) a
     <=? edf_metric (extracted_periodic_jobs ts) b)%Z.
Proof.
  intros ts a b a1 b1 step_a step_b n
         Ha Hb Ha1 Hb1 Htransport_a Htransport_b Hdelta_a Hdelta_b.
  destruct
    (extracted_periodic_shift_forward_job_facts
       ts a a1 step_a n Ha Ha1 Htransport_a Hdelta_a)
    as [_ [_ [Hdeadline_a _]]].
  destruct
    (extracted_periodic_shift_forward_job_facts
       ts b b1 step_b n Hb Hb1 Htransport_b Hdelta_b)
    as [_ [_ [Hdeadline_b _]]].
  unfold edf_metric.
  rewrite Hdeadline_a, Hdeadline_b.
  destruct
    (Z.of_nat (job_abs_deadline (extracted_periodic_jobs ts a))
     <=?
     Z.of_nat (job_abs_deadline (extracted_periodic_jobs ts b)))%Z
    eqn:Hcmp.
  - apply Z.leb_le in Hcmp.
    apply Z.leb_le.
    lia.
  - apply Z.leb_gt in Hcmp.
    apply Z.leb_gt.
    lia.
Qed.

Lemma extracted_periodic_shift_forward_job_id_facts :
  forall ts j n,
    extracted_taskset_wf ts = true ->
    periodic_jobset
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      j ->
    job_task
      (extracted_periodic_jobs ts
         (extracted_periodic_shift_forward_job_id ts n j)) =
      job_task (extracted_periodic_jobs ts j)
    /\
    job_release
      (extracted_periodic_jobs ts
         (extracted_periodic_shift_forward_job_id ts n j)) =
      job_release (extracted_periodic_jobs ts j) +
      periodic_hyperperiod
        (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) * n
    /\
    job_abs_deadline
      (extracted_periodic_jobs ts
         (extracted_periodic_shift_forward_job_id ts n j)) =
      job_abs_deadline (extracted_periodic_jobs ts j) +
      periodic_hyperperiod
        (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) * n
    /\
    job_cost
      (extracted_periodic_jobs ts
         (extracted_periodic_shift_forward_job_id ts n j)) =
      job_cost (extracted_periodic_jobs ts j).
Proof.
  intros ts j n Hwf Hjob.
  pose proof
    (extracted_periodic_shift_forward_job_id_sound
       ts j n Hwf Hjob)
    as [Hj1 [Htransport Hdelta]].
  eapply extracted_periodic_shift_forward_job_facts.
  - exact Hjob.
  - exact Hj1.
  - exact Htransport.
  - exact Hdelta.
Qed.

Lemma extracted_periodic_shift_forward_job_id_index :
  forall ts j n,
    extracted_taskset_wf ts = true ->
    periodic_jobset
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      j ->
    job_index
      (extracted_periodic_jobs ts
         (extracted_periodic_shift_forward_job_id ts n j)) =
    job_index (extracted_periodic_jobs ts j) +
    extracted_periodic_hyperperiod_task_step
      ts (job_task (extracted_periodic_jobs ts j)) * n.
Proof.
  intros ts j n _ Hjob.
  unfold extracted_periodic_shift_forward_job_id.
  rewrite
    (codec_job_index
       (extracted_task_scope ts)
       (extracted_periodic_tasks ts)
       (fun _ => 0)
       (extracted_periodic_jobs ts)
       (extracted_periodic_codec ts)
       (job_task (extracted_periodic_jobs ts j))
       (job_index (extracted_periodic_jobs ts j) +
        extracted_periodic_hyperperiod_task_step
          ts (job_task (extracted_periodic_jobs ts j)) * n)).
  - reflexivity.
  - exact (proj1 Hjob).
Qed.

Lemma extracted_periodic_jobs_same_task_index_eq :
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
    job_index (extracted_periodic_jobs ts j1) =
    job_index (extracted_periodic_jobs ts j2) ->
    j1 = j2.
Proof.
  intros ts j1 j2 Hj1 Hj2 Htask Hidx.
  rewrite
    (global_periodic_job_id_of_complete
       (extracted_task_scope ts)
       (extracted_periodic_tasks ts)
       (fun _ => 0)
       (extracted_periodic_jobs ts)
       (extracted_periodic_codec ts)
       j1
       Hj1).
  rewrite
    (global_periodic_job_id_of_complete
       (extracted_task_scope ts)
       (extracted_periodic_tasks ts)
       (fun _ => 0)
       (extracted_periodic_jobs ts)
       (extracted_periodic_codec ts)
       j2
       Hj2).
  now rewrite Htask, Hidx.
Qed.

Lemma extracted_periodic_shift_forward_job_id_injective :
  forall ts n j1 j2,
    extracted_taskset_wf ts = true ->
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
    extracted_periodic_shift_forward_job_id ts n j1 =
    extracted_periodic_shift_forward_job_id ts n j2 ->
    j1 = j2.
Proof.
  intros ts n j1 j2 Hwf Hj1 Hj2 Hshift.
  pose proof
    (extracted_periodic_shift_forward_job_id_facts
       ts j1 n Hwf Hj1) as [Htask1 _].
  pose proof
    (extracted_periodic_shift_forward_job_id_facts
       ts j2 n Hwf Hj2) as [Htask2 _].
  assert (Htask_shift :
    job_task
      (extracted_periodic_jobs ts
         (extracted_periodic_shift_forward_job_id ts n j1)) =
    job_task
      (extracted_periodic_jobs ts
         (extracted_periodic_shift_forward_job_id ts n j2))).
  { now rewrite Hshift. }
  assert (Htask :
    job_task (extracted_periodic_jobs ts j1) =
    job_task (extracted_periodic_jobs ts j2)).
  { rewrite <- Htask1, <- Htask2. exact Htask_shift. }
  assert (Hidx_shift :
    job_index
      (extracted_periodic_jobs ts
         (extracted_periodic_shift_forward_job_id ts n j1)) =
    job_index
      (extracted_periodic_jobs ts
         (extracted_periodic_shift_forward_job_id ts n j2))).
  { now rewrite Hshift. }
  rewrite
    (extracted_periodic_shift_forward_job_id_index ts j1 n Hwf Hj1)
    in Hidx_shift.
  rewrite
    (extracted_periodic_shift_forward_job_id_index ts j2 n Hwf Hj2)
    in Hidx_shift.
  rewrite Htask in Hidx_shift.
  eapply extracted_periodic_jobs_same_task_index_eq; eauto.
  lia.
Qed.

Lemma extracted_periodic_shift_forward_eligibleb_deterministic :
  forall ts j n sched0 sched1 t,
    extracted_taskset_wf ts = true ->
    periodic_jobset
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      j ->
    service_job 1 sched1
      (extracted_periodic_shift_forward_job_id ts n j)
      (t +
       periodic_hyperperiod
         (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) * n) =
    service_job 1 sched0 j t ->
    eligibleb
      (extracted_periodic_jobs ts) 1 sched1
      (extracted_periodic_shift_forward_job_id ts n j)
      (t +
       periodic_hyperperiod
         (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) * n) =
    eligibleb (extracted_periodic_jobs ts) 1 sched0 j t.
Proof.
  intros ts j n sched0 sched1 t Hwf Hjob Hservice.
  pose proof
    (extracted_periodic_shift_forward_job_id_sound
       ts j n Hwf Hjob)
    as [Hj1 [Htransport Hdelta]].
  eapply extracted_periodic_shift_forward_eligibleb.
  - exact Hjob.
  - exact Hj1.
  - exact Htransport.
  - exact Hdelta.
  - exact Hservice.
Qed.

Lemma extracted_periodic_shift_forward_edf_metric_cmp_deterministic :
  forall ts a b n,
    extracted_taskset_wf ts = true ->
    periodic_jobset
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      a ->
    periodic_jobset
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      b ->
    (edf_metric (extracted_periodic_jobs ts)
       (extracted_periodic_shift_forward_job_id ts n a)
     <=?
     edf_metric (extracted_periodic_jobs ts)
       (extracted_periodic_shift_forward_job_id ts n b))%Z =
    (edf_metric (extracted_periodic_jobs ts) a
     <=? edf_metric (extracted_periodic_jobs ts) b)%Z.
Proof.
  intros ts a b n Hwf Ha Hb.
  pose proof
    (extracted_periodic_shift_forward_job_id_sound
       ts a n Hwf Ha)
    as [Ha1 [Htransport_a Hdelta_a]].
  pose proof
    (extracted_periodic_shift_forward_job_id_sound
       ts b n Hwf Hb)
    as [Hb1 [Htransport_b Hdelta_b]].
  eapply extracted_periodic_shift_forward_edf_metric_cmp.
  - exact Ha.
  - exact Hb.
  - exact Ha1.
  - exact Hb1.
  - exact Htransport_a.
  - exact Htransport_b.
  - exact Hdelta_a.
  - exact Hdelta_b.
Qed.

Lemma extracted_periodic_choose_edf_shift_forward_map :
  forall ts n sched0 sched1 t candidates,
    extracted_taskset_wf ts = true ->
    (forall j,
      In j candidates ->
      periodic_jobset
        (extracted_task_scope ts)
        (extracted_periodic_tasks ts)
        (fun _ => 0)
        (extracted_periodic_jobs ts)
        j) ->
    (forall j,
      In j candidates ->
      service_job 1 sched1
        (extracted_periodic_shift_forward_job_id ts n j)
        (t +
         periodic_hyperperiod
           (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) * n) =
      service_job 1 sched0 j t) ->
    choose_edf (extracted_periodic_jobs ts) 1 sched1
      (t +
       periodic_hyperperiod
         (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) * n)
      (map (extracted_periodic_shift_forward_job_id ts n) candidates) =
    match
      choose_edf (extracted_periodic_jobs ts) 1 sched0 t candidates
    with
    | Some j => Some (extracted_periodic_shift_forward_job_id ts n j)
    | None => None
    end.
Proof.
  intros ts n sched0 sched1 t candidates Hwf Hjobs Hservice.
  apply choose_edf_map_cmp.
  - intros j Hin.
    eapply extracted_periodic_shift_forward_eligibleb_deterministic.
    + exact Hwf.
    + apply Hjobs.
      exact Hin.
    + apply Hservice.
      exact Hin.
  - intros j1 j2 Hin1 Hin2 _ _.
    eapply extracted_periodic_shift_forward_edf_metric_cmp_deterministic.
    + exact Hwf.
    + apply Hjobs.
      exact Hin1.
    + apply Hjobs.
      exact Hin2.
Qed.

Lemma extracted_periodic_choose_edf_shift_forward_candidates_before :
  forall ts n sched0 sched1 t,
    extracted_taskset_wf ts = true ->
    (forall j,
      In j
        (enum_periodic_jobs_before
           (extracted_task_scope ts)
           (extracted_periodic_tasks ts)
           (fun _ => 0)
           (extracted_periodic_jobs ts)
           (enumT_of_extracted_list ts)
           (extracted_periodic_codec ts)
           (S t)) ->
      service_job 1 sched1
        (extracted_periodic_shift_forward_job_id ts n j)
        (t +
         periodic_hyperperiod
           (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) * n) =
      service_job 1 sched0 j t) ->
    choose_edf (extracted_periodic_jobs ts) 1 sched1
      (t +
       periodic_hyperperiod
         (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) * n)
      (map (extracted_periodic_shift_forward_job_id ts n)
         (enum_periodic_jobs_before
            (extracted_task_scope ts)
            (extracted_periodic_tasks ts)
            (fun _ => 0)
            (extracted_periodic_jobs ts)
            (enumT_of_extracted_list ts)
            (extracted_periodic_codec ts)
            (S t))) =
    match
      choose_edf (extracted_periodic_jobs ts) 1 sched0 t
        (enum_periodic_jobs_before
           (extracted_task_scope ts)
           (extracted_periodic_tasks ts)
           (fun _ => 0)
           (extracted_periodic_jobs ts)
           (enumT_of_extracted_list ts)
           (extracted_periodic_codec ts)
           (S t))
    with
    | Some j => Some (extracted_periodic_shift_forward_job_id ts n j)
    | None => None
    end.
Proof.
  intros ts n sched0 sched1 t Hwf Hservice.
  apply extracted_periodic_choose_edf_shift_forward_map.
  - exact Hwf.
  - intros j Hin.
    apply
      (proj1
         (enum_periodic_jobs_before_sound
            (extracted_task_scope ts)
            (extracted_periodic_tasks ts)
            (fun _ => 0)
            (extracted_periodic_jobs ts)
            (enumT_of_extracted_list ts)
            (extracted_periodic_codec ts)
            (extracted_enum_sound ts)
            (S t)
            j
            Hin)).
  - exact Hservice.
Qed.

Lemma extracted_periodic_choose_edf_shift_forward_window :
  forall ts n sched0 sched1 t,
    extracted_taskset_wf ts = true ->
    (forall j,
      In j
        (enum_periodic_jobs_before
           (extracted_task_scope ts)
           (extracted_periodic_tasks ts)
           (fun _ => 0)
           (extracted_periodic_jobs ts)
           (enumT_of_extracted_list ts)
           (extracted_periodic_codec ts)
           (S t)) ->
      service_job 1 sched1
        (extracted_periodic_shift_forward_job_id ts n j)
        (t +
         periodic_hyperperiod
           (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) * n) =
      service_job 1 sched0 j t) ->
    let hp :=
      periodic_hyperperiod
        (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) in
    choose_edf (extracted_periodic_jobs ts) 1 sched1
      (t + hp * n)
      (filter
         (fun j =>
            Nat.leb (hp * n) (job_release (extracted_periodic_jobs ts j))
            && Nat.ltb
                 (job_release (extracted_periodic_jobs ts j))
                 (hp * n + S t))
         (enum_periodic_jobs_before
            (extracted_task_scope ts)
            (extracted_periodic_tasks ts)
            (fun _ => 0)
            (extracted_periodic_jobs ts)
            (enumT_of_extracted_list ts)
            (extracted_periodic_codec ts)
            (hp * n + S t))) =
    match
      choose_edf (extracted_periodic_jobs ts) 1 sched0 t
        (enum_periodic_jobs_before
           (extracted_task_scope ts)
           (extracted_periodic_tasks ts)
           (fun _ => 0)
           (extracted_periodic_jobs ts)
           (enumT_of_extracted_list ts)
           (extracted_periodic_codec ts)
           (S t))
    with
    | Some j => Some (extracted_periodic_shift_forward_job_id ts n j)
    | None => None
    end.
Proof.
  intros ts n sched0 sched1 t Hwf Hservice hp.
  subst hp.
  rewrite extracted_periodic_shift_forward_candidate_window_eq by exact Hwf.
  apply extracted_periodic_choose_edf_shift_forward_candidates_before.
  - exact Hwf.
  - exact Hservice.
Qed.

Lemma extracted_periodic_old_candidate_not_eligible_after_boundary :
  forall ts n sched t j,
    let jobs := extracted_periodic_jobs ts in
    let hp :=
      periodic_hyperperiod
        (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) in
    job_release (jobs j) < hp * n ->
    completed jobs 1 sched j (hp * n) ->
    ~ eligible jobs 1 sched j (t + hp * n).
Proof.
  intros ts n sched t j jobs hp Hrelease Hcompleted.
  eapply completed_not_eligible.
  eapply completed_monotone with (t1 := hp * n).
  - lia.
  - exact Hcompleted.
Qed.

Lemma extracted_periodic_target_prefix_keep_false_old :
  forall ts n t j,
    let hp :=
      periodic_hyperperiod
        (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) in
    In j
      (enum_periodic_jobs_before
         (extracted_task_scope ts)
         (extracted_periodic_tasks ts)
         (fun _ => 0)
         (extracted_periodic_jobs ts)
         (enumT_of_extracted_list ts)
         (extracted_periodic_codec ts)
         (hp * n + S t)) ->
    (Nat.leb (hp * n) (job_release (extracted_periodic_jobs ts j))
     && Nat.ltb
          (job_release (extracted_periodic_jobs ts j))
          (hp * n + S t)) = false ->
    job_release (extracted_periodic_jobs ts j) < hp * n.
Proof.
  intros ts n t j hp Hin Hkeep.
  pose proof
    (proj2
       (enum_periodic_jobs_before_sound
          (extracted_task_scope ts)
          (extracted_periodic_tasks ts)
          (fun _ => 0)
          (extracted_periodic_jobs ts)
          (enumT_of_extracted_list ts)
          (extracted_periodic_codec ts)
          (extracted_enum_sound ts)
          (hp * n + S t)
          j
          Hin)) as Hrelease_before.
  assert (Hupper :
    (job_release (extracted_periodic_jobs ts j) <? hp * n + S t) = true).
  {
    apply Nat.ltb_lt.
    exact Hrelease_before.
  }
  rewrite Hupper in Hkeep.
  destruct (hp * n <=? job_release (extracted_periodic_jobs ts j)) eqn:Hlower.
  - discriminate.
  - apply Nat.leb_gt.
    exact Hlower.
Qed.

Lemma extracted_periodic_choose_edf_prune_old_candidates :
  forall ts n sched t,
    (forall j,
      In j
        (enum_periodic_jobs_before
           (extracted_task_scope ts)
           (extracted_periodic_tasks ts)
           (fun _ => 0)
           (extracted_periodic_jobs ts)
           (enumT_of_extracted_list ts)
           (extracted_periodic_codec ts)
           (periodic_hyperperiod
              (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) * n +
            S t)) ->
      job_release (extracted_periodic_jobs ts j) <
        periodic_hyperperiod
          (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) * n ->
      completed (extracted_periodic_jobs ts) 1 sched j
        (periodic_hyperperiod
           (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) * n)) ->
    let hp :=
      periodic_hyperperiod
        (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) in
    choose_edf (extracted_periodic_jobs ts) 1 sched
      (t + hp * n)
      (enum_periodic_jobs_before
         (extracted_task_scope ts)
         (extracted_periodic_tasks ts)
         (fun _ => 0)
         (extracted_periodic_jobs ts)
         (enumT_of_extracted_list ts)
         (extracted_periodic_codec ts)
         (hp * n + S t)) =
    choose_edf (extracted_periodic_jobs ts) 1 sched
      (t + hp * n)
      (filter
         (fun j =>
            Nat.leb (hp * n) (job_release (extracted_periodic_jobs ts j))
            && Nat.ltb
                 (job_release (extracted_periodic_jobs ts j))
                 (hp * n + S t))
         (enum_periodic_jobs_before
            (extracted_task_scope ts)
            (extracted_periodic_tasks ts)
            (fun _ => 0)
            (extracted_periodic_jobs ts)
            (enumT_of_extracted_list ts)
            (extracted_periodic_codec ts)
            (hp * n + S t))).
Proof.
  intros ts n sched t Hcompleted_old hp.
  subst hp.
  rewrite choose_edf_filter_ineligible
    with
      (keep :=
         fun j =>
           Nat.leb
             (periodic_hyperperiod
                (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) * n)
             (job_release (extracted_periodic_jobs ts j))
           && Nat.ltb
                (job_release (extracted_periodic_jobs ts j))
                (periodic_hyperperiod
                   (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) * n +
                 S t)).
  - reflexivity.
  - intros j Hin Hkeep.
    eapply extracted_periodic_old_candidate_not_eligible_after_boundary.
    + eapply extracted_periodic_target_prefix_keep_false_old.
      * exact Hin.
      * exact Hkeep.
    + apply Hcompleted_old.
      * exact Hin.
      * eapply extracted_periodic_target_prefix_keep_false_old.
        -- exact Hin.
        -- exact Hkeep.
Qed.

Lemma extracted_periodic_choose_edf_shift_forward_unfiltered :
  forall ts n sched0 sched1 t,
    extracted_taskset_wf ts = true ->
    (forall j,
      In j
        (enum_periodic_jobs_before
           (extracted_task_scope ts)
           (extracted_periodic_tasks ts)
           (fun _ => 0)
           (extracted_periodic_jobs ts)
           (enumT_of_extracted_list ts)
           (extracted_periodic_codec ts)
           (periodic_hyperperiod
              (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) * n +
            S t)) ->
      job_release (extracted_periodic_jobs ts j) <
        periodic_hyperperiod
          (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) * n ->
      completed (extracted_periodic_jobs ts) 1 sched1 j
        (periodic_hyperperiod
           (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) * n)) ->
    (forall j,
      In j
        (enum_periodic_jobs_before
           (extracted_task_scope ts)
           (extracted_periodic_tasks ts)
           (fun _ => 0)
           (extracted_periodic_jobs ts)
           (enumT_of_extracted_list ts)
           (extracted_periodic_codec ts)
           (S t)) ->
      service_job 1 sched1
        (extracted_periodic_shift_forward_job_id ts n j)
        (t +
         periodic_hyperperiod
           (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) * n) =
      service_job 1 sched0 j t) ->
    let hp :=
      periodic_hyperperiod
        (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) in
    choose_edf (extracted_periodic_jobs ts) 1 sched1
      (t + hp * n)
      (enum_periodic_jobs_before
         (extracted_task_scope ts)
         (extracted_periodic_tasks ts)
         (fun _ => 0)
         (extracted_periodic_jobs ts)
         (enumT_of_extracted_list ts)
         (extracted_periodic_codec ts)
         (hp * n + S t)) =
    match
      choose_edf (extracted_periodic_jobs ts) 1 sched0 t
        (enum_periodic_jobs_before
           (extracted_task_scope ts)
           (extracted_periodic_tasks ts)
           (fun _ => 0)
           (extracted_periodic_jobs ts)
           (enumT_of_extracted_list ts)
           (extracted_periodic_codec ts)
           (S t))
    with
    | Some j => Some (extracted_periodic_shift_forward_job_id ts n j)
    | None => None
    end.
Proof.
  intros ts n sched0 sched1 t Hwf Hcompleted_old Hservice hp.
  subst hp.
  rewrite extracted_periodic_choose_edf_prune_old_candidates.
  - apply extracted_periodic_choose_edf_shift_forward_window.
    + exact Hwf.
    + exact Hservice.
  - exact Hcompleted_old.
Qed.

Lemma extracted_periodic_generated_schedule_prefix_shift_forward_one_step_cpu0 :
  forall ts n t,
    extracted_taskset_wf ts = true ->
    let jobs := extracted_periodic_jobs ts in
    let candidates :=
      periodic_candidates_before
        (extracted_task_scope ts)
        (extracted_periodic_tasks ts)
        (fun _ => 0)
        jobs
        (enumT_of_extracted_list ts)
        (extracted_periodic_codec ts) in
    let hp :=
      periodic_hyperperiod
        (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) in
    (forall j,
      In j
        (enum_periodic_jobs_before
           (extracted_task_scope ts)
           (extracted_periodic_tasks ts)
           (fun _ => 0)
           jobs
           (enumT_of_extracted_list ts)
           (extracted_periodic_codec ts)
           (hp * n + S t)) ->
      job_release (jobs j) < hp * n ->
      completed jobs 1
        (generated_schedule_prefix
           edf_generic_spec candidates jobs (t + hp * n))
        j
        (hp * n)) ->
    (forall j,
      In j
        (enum_periodic_jobs_before
           (extracted_task_scope ts)
           (extracted_periodic_tasks ts)
           (fun _ => 0)
           jobs
           (enumT_of_extracted_list ts)
           (extracted_periodic_codec ts)
           (S t)) ->
      service_job 1
        (generated_schedule_prefix
           edf_generic_spec candidates jobs (t + hp * n))
        (extracted_periodic_shift_forward_job_id ts n j)
        (t + hp * n) =
      service_job 1
        (generated_schedule_prefix
           edf_generic_spec candidates jobs t)
        j
        t) ->
    generated_schedule_prefix
      edf_generic_spec candidates jobs (S (t + hp * n)) (t + hp * n) 0 =
    match
      generated_schedule_prefix
        edf_generic_spec candidates jobs (S t) t 0
    with
    | Some j => Some (extracted_periodic_shift_forward_job_id ts n j)
    | None => None
    end.
Proof.
  intros ts n t Hwf jobs candidates hp Hcompleted_old Hservice.
  subst jobs candidates hp.
  cbn [generated_schedule_prefix].
  rewrite !Nat.ltb_irrefl.
  rewrite !Nat.eqb_refl.
  unfold periodic_candidates_before.
  replace (S (t +
              periodic_hyperperiod
                (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) * n))
    with
      (periodic_hyperperiod
         (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) * n +
       S t) by lia.
  eapply extracted_periodic_choose_edf_shift_forward_unfiltered.
  - exact Hwf.
  - exact Hcompleted_old.
  - exact Hservice.
Qed.

Lemma extracted_periodic_generated_schedule_prefix_shift_forward_one_step_other_cpu :
  forall ts n t c,
    c <> 0 ->
    let jobs := extracted_periodic_jobs ts in
    let candidates :=
      periodic_candidates_before
        (extracted_task_scope ts)
        (extracted_periodic_tasks ts)
        (fun _ => 0)
        jobs
        (enumT_of_extracted_list ts)
        (extracted_periodic_codec ts) in
    let hp :=
      periodic_hyperperiod
        (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) in
    generated_schedule_prefix
      edf_generic_spec candidates jobs (S (t + hp * n)) (t + hp * n) c =
    None.
Proof.
  intros ts n t c Hc jobs candidates hp.
  subst jobs candidates hp.
  cbn [generated_schedule_prefix].
  rewrite Nat.ltb_irrefl.
  rewrite Nat.eqb_refl.
  destruct c as [|c']; [contradiction|reflexivity].
Qed.

Lemma extracted_periodic_generated_schedule_prefix_slot_some_periodic :
  forall ts H t j,
    let jobs := extracted_periodic_jobs ts in
    let candidates :=
      periodic_candidates_before
        (extracted_task_scope ts)
        (extracted_periodic_tasks ts)
        (fun _ => 0)
        jobs
        (enumT_of_extracted_list ts)
        (extracted_periodic_codec ts) in
    t < H ->
    generated_schedule_prefix
      edf_generic_spec candidates jobs H t 0 = Some j ->
    periodic_jobset
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      jobs
      j.
Proof.
  intros ts H t j jobs candidates Ht Hrun.
  subst jobs candidates.
  rewrite
    (generated_schedule_prefix_stable
       edf_generic_spec
       (periodic_candidates_before
          (extracted_task_scope ts)
          (extracted_periodic_tasks ts)
          (fun _ => 0)
          (extracted_periodic_jobs ts)
          (enumT_of_extracted_list ts)
          (extracted_periodic_codec ts))
       (extracted_periodic_jobs ts)
       H t 0 Ht)
    in Hrun.
  unfold generated_schedule in Hrun.
  cbn [generated_schedule_prefix] in Hrun.
  rewrite Nat.ltb_irrefl in Hrun.
  rewrite !Nat.eqb_refl in Hrun.
  pose proof
    (choose_edf_in_candidates
       (extracted_periodic_jobs ts) 1
       (generated_schedule_prefix
          edf_generic_spec
          (periodic_candidates_before
             (extracted_task_scope ts)
             (extracted_periodic_tasks ts)
             (fun _ => 0)
             (extracted_periodic_jobs ts)
             (enumT_of_extracted_list ts)
             (extracted_periodic_codec ts))
          (extracted_periodic_jobs ts)
          t)
       t
       (periodic_candidates_before
          (extracted_task_scope ts)
          (extracted_periodic_tasks ts)
          (fun _ => 0)
          (extracted_periodic_jobs ts)
          (enumT_of_extracted_list ts)
          (extracted_periodic_codec ts)
          (extracted_periodic_jobs ts) 1
          (generated_schedule_prefix
             edf_generic_spec
             (periodic_candidates_before
                (extracted_task_scope ts)
                (extracted_periodic_tasks ts)
                (fun _ => 0)
                (extracted_periodic_jobs ts)
                (enumT_of_extracted_list ts)
                (extracted_periodic_codec ts))
             (extracted_periodic_jobs ts)
             t)
          t)
       j
       Hrun) as Hin.
  unfold periodic_candidates_before in Hin.
  exact
    (proj1
       (enum_periodic_jobs_before_sound
          (extracted_task_scope ts)
          (extracted_periodic_tasks ts)
          (fun _ => 0)
          (extracted_periodic_jobs ts)
          (enumT_of_extracted_list ts)
          (extracted_periodic_codec ts)
          (extracted_enum_sound ts)
          (S t)
          j
          Hin)).
Qed.

Lemma extracted_periodic_service_shift_forward_of_slots :
  forall ts n sched0 sched1 j t,
    extracted_taskset_wf ts = true ->
    periodic_jobset
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      j ->
    valid_schedule (extracted_periodic_jobs ts) 1 sched1 ->
    (forall u,
      u < t ->
      sched1
        (u +
         periodic_hyperperiod
           (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) * n)
        0 =
      match sched0 u 0 with
      | Some k => Some (extracted_periodic_shift_forward_job_id ts n k)
      | None => None
      end) ->
    (forall u k,
      u < t ->
      sched0 u 0 = Some k ->
      periodic_jobset
        (extracted_task_scope ts)
        (extracted_periodic_tasks ts)
        (fun _ => 0)
        (extracted_periodic_jobs ts)
        k) ->
    service_job 1 sched1
      (extracted_periodic_shift_forward_job_id ts n j)
      (t +
       periodic_hyperperiod
         (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) * n) =
    service_job 1 sched0 j t.
Proof.
  intros ts n.
  set (jobs := extracted_periodic_jobs ts).
  set (hp :=
    periodic_hyperperiod
      (extracted_periodic_tasks ts) (enumT_of_extracted_list ts)).
  set (delta := hp * n).
  intros sched0 sched1 j t Hwf Hjob Hvalid Hslots Hsource_periodic.
  assert (Hrelease_shift :
    delta <=
    job_release
      (jobs (extracted_periodic_shift_forward_job_id ts n j))).
  {
    subst jobs delta hp.
    pose proof
      (extracted_periodic_shift_forward_job_id_facts
         ts j n Hwf Hjob) as [_ [Hrelease _]].
    rewrite Hrelease.
    lia.
  }
  revert sched0 sched1 j Hjob Hvalid Hslots Hsource_periodic Hrelease_shift.
  induction t as [|t IH]; intros sched0 sched1 j Hjob Hvalid Hslots Hsource_periodic Hrelease_shift.
  - simpl.
    replace (0 + delta) with delta by lia.
    apply (service_before_release_zero jobs 1 sched1
             (extracted_periodic_shift_forward_job_id ts n j)
             delta).
    + subst jobs. exact Hvalid.
    + exact Hrelease_shift.
  - replace (S t + delta) with (S (t + delta)) by lia.
    rewrite (service_job_step 1 sched1
               (extracted_periodic_shift_forward_job_id ts n j)
               (t + delta)).
    rewrite (service_job_step 1 sched0 j t).
    rewrite
      (IH sched0 sched1 j Hjob Hvalid
         (fun u Hu => Hslots u ltac:(lia))
         (fun u k Hu Hrun => Hsource_periodic u k ltac:(lia) Hrun)
         Hrelease_shift).
    assert (Hcpu :
        cpu_count 1 sched1
          (extracted_periodic_shift_forward_job_id ts n j)
          (t + delta) =
        cpu_count 1 sched0 j t).
      {
        specialize (Hslots t (Nat.lt_succ_diag_r t)).
        destruct (sched0 t 0) as [k|] eqn:Hsrc.
        - pose proof Hslots as Htarget.
          destruct (Nat.eq_dec k j) as [-> | Hne].
          + rewrite
              (cpu_count_1_some_eq
                 sched1
                 (extracted_periodic_shift_forward_job_id ts n j)
                 (t + delta)
                 Htarget).
            rewrite (cpu_count_1_some_eq sched0 j t Hsrc).
            reflexivity.
          + assert (Hk :
              periodic_jobset
                (extracted_task_scope ts)
                (extracted_periodic_tasks ts)
                (fun _ => 0)
                (extracted_periodic_jobs ts)
                k).
            { eapply Hsource_periodic; eauto using Nat.lt_succ_diag_r. }
            assert (Hshift_ne :
              extracted_periodic_shift_forward_job_id ts n j <>
              extracted_periodic_shift_forward_job_id ts n k).
            {
              intro Heq.
              apply Hne.
              symmetry.
              eapply extracted_periodic_shift_forward_job_id_injective.
              - exact Hwf.
              - exact Hjob.
              - exact Hk.
              - exact Heq.
            }
            rewrite
              (cpu_count_1_some_neq
                 sched1
                 (extracted_periodic_shift_forward_job_id ts n j)
                 (extracted_periodic_shift_forward_job_id ts n k)
                 (t + delta)
                 Htarget
                 Hshift_ne).
            rewrite
              (cpu_count_1_some_neq sched0 j k t Hsrc
                 ltac:(intro Heq; apply Hne; symmetry; exact Heq)).
            reflexivity.
        - pose proof Hslots as Htarget.
          rewrite
            (cpu_count_1_none
               sched1
               (extracted_periodic_shift_forward_job_id ts n j)
               (t + delta)
               Htarget).
          rewrite (cpu_count_1_none sched0 j t Hsrc).
          reflexivity.
      }
      lia.
Qed.

Lemma extracted_periodic_generated_schedule_prefix_shift_forward_before :
  forall ts n H,
    extracted_taskset_wf ts = true ->
    let jobs := extracted_periodic_jobs ts in
    let candidates :=
      periodic_candidates_before
        (extracted_task_scope ts)
        (extracted_periodic_tasks ts)
        (fun _ => 0)
        jobs
        (enumT_of_extracted_list ts)
        (extracted_periodic_codec ts) in
    let hp :=
      periodic_hyperperiod
        (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) in
    (forall t j,
      t < H ->
      In j
        (enum_periodic_jobs_before
           (extracted_task_scope ts)
           (extracted_periodic_tasks ts)
           (fun _ => 0)
           jobs
           (enumT_of_extracted_list ts)
           (extracted_periodic_codec ts)
           (hp * n + S t)) ->
      job_release (jobs j) < hp * n ->
      completed jobs 1
        (generated_schedule_prefix
           edf_generic_spec candidates jobs (t + hp * n))
        j
        (hp * n)) ->
    forall t c,
      t < H ->
      generated_schedule_prefix
        edf_generic_spec candidates jobs (H + hp * n) (t + hp * n) c =
      match
        generated_schedule_prefix edf_generic_spec candidates jobs H t c
      with
      | Some j => Some (extracted_periodic_shift_forward_job_id ts n j)
      | None => None
      end.
Proof.
  intros ts n H Hwf jobs candidates hp Hcompleted_old t c Ht.
  subst jobs candidates hp.
  set (jobs := extracted_periodic_jobs ts).
  set (candidates :=
    periodic_candidates_before
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      jobs
      (enumT_of_extracted_list ts)
      (extracted_periodic_codec ts)).
  set (hp :=
    periodic_hyperperiod
      (extracted_periodic_tasks ts) (enumT_of_extracted_list ts)).
  set (delta := hp * n).
  assert (Hstep :
    forall u cpu,
      u < H ->
      generated_schedule_prefix
        edf_generic_spec candidates jobs (S (u + delta)) (u + delta) cpu =
      match
        generated_schedule_prefix edf_generic_spec candidates jobs (S u) u cpu
      with
      | Some j => Some (extracted_periodic_shift_forward_job_id ts n j)
      | None => None
      end).
  {
    intro q.
    induction q as [q IH] using lt_wf_ind.
    intros cpu Hu.
    destruct q as [|u].
    - destruct (Nat.eq_dec cpu 0) as [-> | Hc].
      + eapply extracted_periodic_generated_schedule_prefix_shift_forward_one_step_cpu0.
        * exact Hwf.
        * intros j Hin Hrelease.
          subst jobs candidates hp delta.
          eapply Hcompleted_old; eauto.
        * intros j Hin.
          eapply extracted_periodic_service_shift_forward_of_slots.
          -- exact Hwf.
          -- subst jobs.
             exact
               (proj1
                  (enum_periodic_jobs_before_sound
                     (extracted_task_scope ts)
                     (extracted_periodic_tasks ts)
                     (fun _ => 0)
                     (extracted_periodic_jobs ts)
                     (enumT_of_extracted_list ts)
                     (extracted_periodic_codec ts)
                     (extracted_enum_sound ts)
                     1
                     j
                     Hin)).
          -- subst jobs candidates.
             apply generated_schedule_prefix_valid_schedule.
          -- intros r Hr. lia.
          -- intros r k Hr _. lia.
      + subst jobs candidates hp delta.
        rewrite
          (extracted_periodic_generated_schedule_prefix_shift_forward_one_step_other_cpu
             ts n 0 cpu Hc).
        cbn [generated_schedule_prefix].
        rewrite Nat.ltb_irrefl.
        rewrite Nat.eqb_refl.
        destruct cpu as [|cpu']; [contradiction|reflexivity].
    - destruct (Nat.eq_dec cpu 0) as [-> | Hc].
      + eapply extracted_periodic_generated_schedule_prefix_shift_forward_one_step_cpu0.
        * exact Hwf.
        * intros j Hin Hrelease.
          subst jobs candidates hp delta.
          eapply Hcompleted_old; eauto.
        * intros j Hin.
          assert (Hjob :
            periodic_jobset
              (extracted_task_scope ts)
              (extracted_periodic_tasks ts)
              (fun _ => 0)
              jobs
              j).
          {
            subst jobs.
            exact
              (proj1
                 (enum_periodic_jobs_before_sound
                    (extracted_task_scope ts)
                    (extracted_periodic_tasks ts)
                    (fun _ => 0)
                    (extracted_periodic_jobs ts)
                    (enumT_of_extracted_list ts)
                    (extracted_periodic_codec ts)
                    (extracted_enum_sound ts)
                    (S (S u))
                    j
                    Hin)).
          }
          eapply
            (extracted_periodic_service_shift_forward_of_slots
               ts n
               (generated_schedule_prefix
                  edf_generic_spec candidates jobs (S u))
               (generated_schedule_prefix
                  edf_generic_spec candidates jobs (S u + delta))
               j
               (S u)).
          -- exact Hwf.
          -- exact Hjob.
          -- subst jobs candidates.
             apply generated_schedule_prefix_valid_schedule.
          -- intros r Hr.
             change
               (periodic_hyperperiod
                  (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) * n)
               with delta.
             rewrite
               (generated_schedule_prefix_stable
                  edf_generic_spec candidates jobs
                  (S u + delta) (r + delta) 0) by lia.
             rewrite
               (generated_schedule_prefix_stable
                  edf_generic_spec candidates jobs
                  (S u) r 0) by lia.
             rewrite <-
               (generated_schedule_prefix_stable
                  edf_generic_spec candidates jobs
                  (S (r + delta)) (r + delta) 0) by lia.
             rewrite <-
               (generated_schedule_prefix_stable
                  edf_generic_spec candidates jobs
                  (S r) r 0) by lia.
             apply IH; lia.
          -- intros r k Hr Hrun.
             eapply extracted_periodic_generated_schedule_prefix_slot_some_periodic.
             ++ exact Hr.
             ++ exact Hrun.
      + subst jobs candidates hp delta.
        rewrite
          (extracted_periodic_generated_schedule_prefix_shift_forward_one_step_other_cpu
             ts n (S u) cpu Hc).
        cbn [generated_schedule_prefix].
        rewrite Nat.ltb_irrefl.
        rewrite Nat.eqb_refl.
        destruct cpu as [|cpu']; [contradiction|reflexivity].
  }
  assert (Htgt :
    generated_schedule_prefix
      edf_generic_spec candidates jobs (H + delta) (t + delta) c =
    generated_schedule_prefix
      edf_generic_spec candidates jobs (S (t + delta)) (t + delta) c).
  {
    rewrite
      (generated_schedule_prefix_stable
         edf_generic_spec candidates jobs
         (H + delta) (t + delta) c) by lia.
    symmetry.
    rewrite
      (generated_schedule_prefix_stable
         edf_generic_spec candidates jobs
         (S (t + delta)) (t + delta) c) by lia.
    reflexivity.
  }
  assert (Hsrc :
    generated_schedule_prefix edf_generic_spec candidates jobs H t c =
    generated_schedule_prefix edf_generic_spec candidates jobs (S t) t c).
  {
    rewrite
      (generated_schedule_prefix_stable
         edf_generic_spec candidates jobs H t c) by exact Ht.
    symmetry.
    rewrite
      (generated_schedule_prefix_stable
         edf_generic_spec candidates jobs (S t) t c) by lia.
    reflexivity.
  }
  rewrite Htgt.
  rewrite Hsrc.
  apply Hstep.
  exact Ht.
Qed.

Lemma extracted_periodic_shift_forward_candidate_before :
  forall ts j n t,
    extracted_taskset_wf ts = true ->
    periodic_jobset
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      j ->
    job_release (extracted_periodic_jobs ts j) < t ->
    exists j1 step,
      periodic_jobset
        (extracted_task_scope ts)
        (extracted_periodic_tasks ts)
        (fun _ => 0)
        (extracted_periodic_jobs ts)
        j1
      /\
      transport_rep_to_target_job
        (extracted_task_scope ts)
        (extracted_periodic_tasks ts)
        (fun _ => 0)
        (extracted_periodic_jobs ts)
        (extracted_periodic_codec ts)
        j j1 step n
      /\
      step * n *
        task_period
          (extracted_periodic_tasks ts
             (job_task (extracted_periodic_jobs ts j))) =
      periodic_hyperperiod
        (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) * n
      /\
      In j1
        (enum_periodic_jobs_before
           (extracted_task_scope ts)
           (extracted_periodic_tasks ts)
           (fun _ => 0)
           (extracted_periodic_jobs ts)
           (enumT_of_extracted_list ts)
           (extracted_periodic_codec ts)
           (t +
            periodic_hyperperiod
              (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) * n)).
Proof.
  intros ts j n t Hwf Hjob Hrelease_before.
  destruct
    (extracted_periodic_shift_forward_job_by_hyperperiod
       ts j n Hwf Hjob)
    as [j1 [step [Hj1 [Htransport Hdelta]]]].
  exists j1, step.
  split; [exact Hj1|].
  split; [exact Htransport|].
  split; [exact Hdelta|].
  assert (Hrelease_shift :
    job_release (extracted_periodic_jobs ts j1) =
    job_release (extracted_periodic_jobs ts j) +
    step * n *
      task_period
        (extracted_periodic_tasks ts
           (job_task (extracted_periodic_jobs ts j)))).
  {
    eapply codec_transport_target_release_shift.
    - exact (proj1 Hjob).
    - exact (proj2 Hjob).
    - exact Htransport.
  }
  eapply enum_periodic_jobs_before_complete.
  - apply extracted_tasks_well_formed_on_enum.
    exact Hwf.
  - apply extracted_enum_complete.
  - exact Hj1.
  - rewrite Hrelease_shift.
    rewrite Hdelta.
    lia.
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

Lemma extracted_periodic_shift_forward_deadline_between_pair :
  forall ts target0 x0 n,
    extracted_taskset_wf ts = true ->
    periodic_jobset
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      target0 ->
    periodic_jobset_deadline_between
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      0
      (job_abs_deadline (extracted_periodic_jobs ts target0))
      x0 ->
    job_release (extracted_periodic_jobs ts x0) <
    job_release (extracted_periodic_jobs ts target0) ->
    exists target x,
      periodic_jobset
        (extracted_task_scope ts)
        (extracted_periodic_tasks ts)
        (fun _ => 0)
        (extracted_periodic_jobs ts)
        target
      /\
      periodic_jobset_deadline_between
        (extracted_task_scope ts)
        (extracted_periodic_tasks ts)
        (fun _ => 0)
        (extracted_periodic_jobs ts)
        0
        (job_abs_deadline (extracted_periodic_jobs ts target))
        x
      /\
      job_release (extracted_periodic_jobs ts x) <
      job_release (extracted_periodic_jobs ts target)
      /\
      HyperperiodShiftedServicePair
        (extracted_periodic_tasks ts)
        (enumT_of_extracted_list ts)
        (extracted_periodic_jobs ts)
        target x target0 x0
        (periodic_hyperperiod
           (extracted_periodic_tasks ts) (enumT_of_extracted_list ts) * n).
Proof.
  intros ts target0 x0 n Hwf Htarget0 Hbetween0 Hrelease0.
  assert (Hx0 : periodic_jobset
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      x0).
  {
    split.
    - eapply periodic_jobset_deadline_between_implies_task_in_scope.
      exact Hbetween0.
    - eapply periodic_jobset_deadline_between_implies_generated.
      exact Hbetween0.
  }
  destruct
    (extracted_periodic_shift_forward_job_by_hyperperiod
       ts target0 n Hwf Htarget0)
    as [target [target_step
        [Htarget [Htarget_transport Htarget_delta]]]].
  destruct
    (extracted_periodic_shift_forward_job_by_hyperperiod
       ts x0 n Hwf Hx0)
    as [x [x_step [Hx [Hx_transport Hx_delta]]]].
  pose proof
    (extracted_periodic_hyperperiod_shifted_service_pair_of_transport
       ts target x target0 x0 target_step x_step n
       Htarget0 Hx0 Htarget_transport Hx_transport
       Htarget_delta Hx_delta) as Hshift.
  exists target, x.
  split; [exact Htarget|].
  split.
  - destruct Hshift as [_ Htarget_release Htarget_deadline
                        Hx_release Hx_deadline _].
    split.
    + exact (proj1 Hx).
    + split.
      * exact (proj2 Hx).
      * split; [lia|].
        pose proof
          (periodic_jobset_deadline_between_implies_deadline_le
             (extracted_task_scope ts)
             (extracted_periodic_tasks ts)
             (fun _ => 0)
             (extracted_periodic_jobs ts)
             0
             (job_abs_deadline (extracted_periodic_jobs ts target0))
             x0 Hbetween0) as Hdeadline0.
        lia.
  - split.
    + destruct Hshift as [_ Htarget_release _ Hx_release _ _].
      lia.
    + exact Hshift.
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

Lemma check_periodic_edf_checked_sidecar_first_hyperperiod_reset_completion :
  forall ts
         (codec :
          PeriodicCodec
            (extracted_task_scope ts)
            (extracted_periodic_tasks ts)
            (fun _ => 0)
            (extracted_periodic_jobs ts))
         cert sidecar target x,
    check_periodic_edf_checked_sidecar ts codec cert sidecar = true ->
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
      (job_release (extracted_periodic_jobs ts target)).
Proof.
  intros ts codec cert sidecar target x Hcheck Htarget Hbetween
         Htarget_after_reset Hx_before_reset.
  destruct
    (check_periodic_edf_checked_sidecar_fields
       ts codec cert sidecar Hcheck)
    as (_ & _ & _ & _ & Hhorizon_covers
        & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
  pose proof
    (check_periodic_edf_checked_sidecar_hyperperiod_facts
       ts codec cert sidecar Hcheck)
    as [Hreset _].
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
    + exact Hreset.
    + split.
      * exact (proj1 Hbetween).
      * exact (proj1 (proj2 Hbetween)).
    + exact Hx_before_reset.
Qed.

Theorem check_periodic_edf_checked_sidecar_extracted_first_hyperperiod_reset_completion :
  forall ts cert sidecar target x,
    check_periodic_edf_checked_sidecar_extracted ts cert sidecar = true ->
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
         (extracted_periodic_codec ts))
      x
      (job_release (extracted_periodic_jobs ts target)).
Proof.
  intros ts cert sidecar target x Hcheck Htarget Hbetween
         Htarget_after_reset Hx_before_reset.
  destruct
    (check_periodic_edf_checked_sidecar_extracted_fields
       ts cert sidecar Hcheck)
    as [_ Hchecked].
  eapply check_periodic_edf_checked_sidecar_first_hyperperiod_reset_completion;
    eauto.
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
    eapply check_periodic_edf_checked_sidecar_first_hyperperiod_reset_completion;
      eauto.
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
