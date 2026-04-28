From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Semantics.ScheduleLemmas.ScheduleFacts.
From RocqSched Require Import Semantics.ScheduleLemmas.SchedulePrefix.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.EnumCandidates.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Uniprocessor.Generic.FinitePrefixScheduleWitness.
From RocqSched Require Import Uniprocessor.Policies.EDF.
From RocqSched Require Import Uniprocessor.Policies.EDFLemmas.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicTasks.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicInfiniteJobset.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicCodec.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicEnumeration.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicPrefixCoherence.
Import ListNotations.

Lemma jittered_expected_release_ge_index :
  forall T tasks offset τ k,
    well_formed_periodic_tasks_on T tasks ->
    T τ ->
    k <= expected_release tasks offset τ k.
Proof.
  intros T tasks offset τ k Hwf Hτ.
  unfold expected_release.
  pose proof (Hwf τ Hτ) as Hperiod.
  nia.
Qed.

Lemma filter_all_false :
  forall A (f : A -> bool) l,
    (forall x, In x l -> f x = false) ->
    filter f l = [].
Proof.
  intros A f l Hall.
  induction l as [|x l IH]; simpl.
  - reflexivity.
  - rewrite (Hall x (or_introl eq_refl)).
    apply IH.
    intros y Hy.
    apply Hall.
    right; exact Hy.
Qed.

Lemma filter_filter :
  forall A (f g : A -> bool) l,
    filter f (filter g l) = filter (fun x => f x && g x) l.
Proof.
  intros A f g l.
  induction l as [|x l IH]; simpl.
  - reflexivity.
  - destruct (g x) eqn:Hg; simpl.
    + destruct (f x) eqn:Hf; simpl; rewrite IH; reflexivity.
    + destruct (f x); simpl; exact IH.
Qed.

Lemma jittered_before_indices_suffix_empty :
  forall T tasks offset τ t H,
    well_formed_periodic_tasks_on T tasks ->
    T τ ->
    S t <= H ->
    filter
      (fun k => Nat.ltb (expected_release tasks offset τ k) (S t))
      (seq (S t) (H - S t)) = [].
Proof.
  intros T tasks offset τ t H Hwf Hτ Hle.
  apply filter_all_false.
  intros k Hin.
  apply in_seq in Hin.
  destruct Hin as [Hk _].
  apply Nat.ltb_ge.
  eapply Nat.le_trans.
  - exact Hk.
  - exact (jittered_expected_release_ge_index T tasks offset τ k Hwf Hτ).
Qed.

Lemma jittered_before_indices_on_large_horizon :
  forall T tasks offset τ t H,
    well_formed_periodic_tasks_on T tasks ->
    T τ ->
    S t <= H ->
    filter
      (fun k => Nat.ltb (expected_release tasks offset τ k) (S t))
      (seq 0 H) =
    enum_jittered_periodic_indices_upto tasks offset τ (S t).
Proof.
  intros T tasks offset τ t H Hwf Hτ Hle.
  unfold enum_jittered_periodic_indices_upto.
  replace H with (S t + (H - S t)) by lia.
  rewrite seq_app, filter_app.
  replace (0 + S t) with (S t) by lia.
  rewrite (jittered_before_indices_suffix_empty T tasks offset τ t H Hwf Hτ Hle).
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma jittered_actual_before_implies_expected_before :
  forall T tasks offset jitter jobs H
         (codec : JitteredPeriodicFiniteHorizonCodec
                    T tasks offset jitter jobs H)
         τ k t,
    T τ ->
    expected_release tasks offset τ k < H ->
    job_release
      (jobs (jittered_periodic_job_id_of
               T tasks offset jitter jobs H codec τ k)) < S t ->
    expected_release tasks offset τ k < S t.
Proof.
  intros T tasks offset jitter jobs H codec τ k t Hτ Hexpected Hactual.
  pose proof
    (jittered_periodic_job_id_of_sound
       T tasks offset jitter jobs H codec τ k Hτ Hexpected)
    as [Htask [Hidx Hgen]].
  pose proof
    (generated_by_jittered_periodic_release_lb
       tasks offset jitter jobs
       (jittered_periodic_job_id_of
          T tasks offset jitter jobs H codec τ k) Hgen) as Hlb.
  rewrite Htask, Hidx in Hlb.
  lia.
Qed.

Lemma filter_jittered_before_indices_upto :
  forall T tasks offset jitter jobs τ t H
         (codec : JitteredPeriodicCodec T tasks offset jitter jobs),
    well_formed_periodic_tasks_on T tasks ->
    T τ ->
    S t <= H ->
    filter
      (fun k =>
         Nat.ltb
           (job_release
              (jobs
                 (global_jittered_periodic_job_id_of
                    T tasks offset jitter jobs codec τ k)))
           (S t))
      (enum_jittered_periodic_indices_upto tasks offset τ H) =
    filter
      (fun k =>
         Nat.ltb
           (job_release
              (jobs
                 (global_jittered_periodic_job_id_of
                    T tasks offset jitter jobs codec τ k)))
           (S t))
      (enum_jittered_periodic_indices_upto tasks offset τ (S t)).
Proof.
  intros T tasks offset jitter jobs τ t H codec Hwf Hτ Hle.
  unfold enum_jittered_periodic_indices_upto.
  rewrite !filter_filter.
  assert (Hfg :
    filter
      (fun x =>
         (job_release
            (jobs
               (global_jittered_periodic_job_id_of
                  T tasks offset jitter jobs codec τ x)) <? S t)
         && (expected_release tasks offset τ x <? H))
      (seq 0 H) =
    filter
      (fun x =>
         job_release
           (jobs
              (global_jittered_periodic_job_id_of
                 T tasks offset jitter jobs codec τ x)) <? S t)
      (seq 0 H)).
  {
    apply filter_ext_in.
    intros k Hin.
    destruct
      (Nat.ltb
         (job_release
            (jobs
               (global_jittered_periodic_job_id_of
                  T tasks offset jitter jobs codec τ k))) (S t)) eqn:Hactual;
      simpl.
    - apply Nat.ltb_lt in Hactual.
      apply Nat.ltb_lt.
      pose proof
        (global_jittered_periodic_job_id_of_sound
           T tasks offset jitter jobs codec τ k Hτ)
        as [Htask [Hidx Hgen]].
      pose proof
        (generated_by_jittered_periodic_release_lb
           tasks offset jitter jobs
           (global_jittered_periodic_job_id_of
              T tasks offset jitter jobs codec τ k) Hgen) as Hlb.
      rewrite Htask, Hidx in Hlb.
      lia.
    - reflexivity.
  }
  rewrite Hfg.
  assert (Hfg_before :
    filter
      (fun x =>
         (job_release
            (jobs
               (global_jittered_periodic_job_id_of
                  T tasks offset jitter jobs codec τ x)) <? S t)
         && (expected_release tasks offset τ x <? S t))
      (seq 0 (S t)) =
    filter
      (fun x =>
         job_release
           (jobs
              (global_jittered_periodic_job_id_of
                 T tasks offset jitter jobs codec τ x)) <? S t)
      (seq 0 (S t))).
  {
    apply filter_ext_in.
    intros k Hin.
    destruct
      (Nat.ltb
         (job_release
            (jobs
               (global_jittered_periodic_job_id_of
                  T tasks offset jitter jobs codec τ k))) (S t)) eqn:Hactual;
      simpl.
    - apply Nat.ltb_lt in Hactual.
      apply Nat.ltb_lt.
      pose proof
        (global_jittered_periodic_job_id_of_sound
           T tasks offset jitter jobs codec τ k Hτ)
        as [Htask [Hidx Hgen]].
      pose proof
        (generated_by_jittered_periodic_release_lb
           tasks offset jitter jobs
           (global_jittered_periodic_job_id_of
              T tasks offset jitter jobs codec τ k) Hgen) as Hlb.
      rewrite Htask, Hidx in Hlb.
      lia.
    - reflexivity.
  }
  rewrite Hfg_before.
  replace
    (filter
       (fun x =>
          job_release
            (jobs
               (global_jittered_periodic_job_id_of
                  T tasks offset jitter jobs codec τ x)) <? S t)
       (seq 0 H))
    with
    (filter
       (fun x =>
          job_release
            (jobs
               (global_jittered_periodic_job_id_of
                  T tasks offset jitter jobs codec τ x)) <? S t)
       (filter
          (fun x => expected_release tasks offset τ x <? S t)
          (seq 0 H))).
  2: {
    rewrite filter_filter.
    apply filter_ext_in.
    intros k Hin.
    destruct
      (job_release
         (jobs
            (global_jittered_periodic_job_id_of
               T tasks offset jitter jobs codec τ k)) <? S t) eqn:Hactual;
      simpl.
    - apply Nat.ltb_lt in Hactual.
      apply Nat.ltb_lt.
      pose proof
        (global_jittered_periodic_job_id_of_sound
           T tasks offset jitter jobs codec τ k Hτ)
        as [Htask [Hidx Hgen]].
      pose proof
        (generated_by_jittered_periodic_release_lb
           tasks offset jitter jobs
           (global_jittered_periodic_job_id_of
              T tasks offset jitter jobs codec τ k) Hgen) as Hlb.
      rewrite Htask, Hidx in Hlb.
      lia.
    - reflexivity.
  }
  rewrite (jittered_before_indices_on_large_horizon T tasks offset τ t H Hwf Hτ Hle).
  unfold enum_jittered_periodic_indices_upto.
  rewrite filter_filter.
  exact Hfg_before.
Qed.

Lemma filter_map_jobs_by_before :
  forall jobs (id_of : TaskId -> nat -> JobId) τ t ks,
    filter (fun j => Nat.ltb (job_release (jobs j)) (S t))
      (map (id_of τ) ks) =
    map (id_of τ)
      (filter
         (fun k =>
            Nat.ltb
              (job_release (jobs (id_of τ k)))
              (S t)) ks).
Proof.
  intros jobs id_of τ t ks.
  induction ks as [|k ks IH]; simpl.
  - reflexivity.
  - destruct
      (Nat.ltb
         (job_release
            (jobs (id_of τ k))) (S t));
      simpl; rewrite IH; reflexivity.
Qed.

Lemma enum_jittered_periodic_jobs_upto_unfiltered_filter_before :
  forall T tasks offset jitter jobs H enumT
         (codec : JitteredPeriodicCodec T tasks offset jitter jobs) t,
    well_formed_periodic_tasks_on T tasks ->
    (forall τ, In τ enumT -> T τ) ->
    S t <= H ->
    filter
      (fun j => Nat.ltb (job_release (jobs j)) (S t))
      (enum_jittered_periodic_jobs_upto_unfiltered
         T tasks offset jitter jobs H enumT
         (jittered_periodic_finite_horizon_codec_of
            T tasks offset jitter jobs H codec)) =
    filter
      (fun j => Nat.ltb (job_release (jobs j)) (S t))
      (enum_jittered_periodic_jobs_upto_unfiltered
         T tasks offset jitter jobs (S t) enumT
         (jittered_periodic_finite_horizon_codec_of
            T tasks offset jitter jobs (S t) codec)).
Proof.
  intros T tasks offset jitter jobs H enumT codec t Hwf HenumT_sound Hle.
  unfold enum_jittered_periodic_jobs_upto_unfiltered.
  change
    (jittered_periodic_job_id_of
       T tasks offset jitter jobs H
       (jittered_periodic_finite_horizon_codec_of
          T tasks offset jitter jobs H codec))
    with
    (global_jittered_periodic_job_id_of
       T tasks offset jitter jobs codec).
  change
    (jittered_periodic_job_id_of
       T tasks offset jitter jobs (S t)
       (jittered_periodic_finite_horizon_codec_of
          T tasks offset jitter jobs (S t) codec))
    with
    (global_jittered_periodic_job_id_of
       T tasks offset jitter jobs codec).
  induction enumT as [|τ enumT IH]; simpl.
  - reflexivity.
  - rewrite !filter_app.
    rewrite
      (filter_map_jobs_by_before
         jobs
         (global_jittered_periodic_job_id_of
            T tasks offset jitter jobs codec)
         τ t
         (enum_jittered_periodic_indices_upto tasks offset τ H)).
    rewrite
      (filter_map_jobs_by_before
         jobs
         (global_jittered_periodic_job_id_of
            T tasks offset jitter jobs codec)
         τ t
         (enum_jittered_periodic_indices_upto tasks offset τ (S t))).
    rewrite
      (filter_jittered_before_indices_upto
         T tasks offset jitter jobs τ t H codec Hwf
         (HenumT_sound τ (or_introl eq_refl)) Hle).
    rewrite IH.
    + reflexivity.
    + intros τ' Hτ'.
      apply HenumT_sound.
      right; exact Hτ'.
Qed.

Lemma enum_jittered_periodic_jobs_upto_filter_before :
  forall T tasks offset jitter jobs H enumT
         (codec : JitteredPeriodicCodec T tasks offset jitter jobs) t,
    well_formed_periodic_tasks_on T tasks ->
    (forall τ, In τ enumT -> T τ) ->
    S t <= H ->
    filter
      (fun j => Nat.ltb (job_release (jobs j)) (S t))
      (enum_jittered_periodic_jobs_upto
         T tasks offset jitter jobs H enumT
         (jittered_periodic_finite_horizon_codec_of
            T tasks offset jitter jobs H codec)) =
    enum_jittered_periodic_jobs_before
      T tasks offset jitter jobs enumT codec (S t).
Proof.
  intros T tasks offset jitter jobs H enumT codec t Hwf HenumT_sound Hle.
  unfold enum_jittered_periodic_jobs_upto at 1.
  rewrite filter_filter.
  assert (Hdrop :
    filter
      (fun x =>
         (job_release (jobs x) <? S t) &&
         (job_release (jobs x) <? H))
      (enum_jittered_periodic_jobs_upto_unfiltered
         T tasks offset jitter jobs H enumT
         (jittered_periodic_finite_horizon_codec_of
            T tasks offset jitter jobs H codec)) =
    filter
      (fun x => job_release (jobs x) <? S t)
      (enum_jittered_periodic_jobs_upto_unfiltered
         T tasks offset jitter jobs H enumT
         (jittered_periodic_finite_horizon_codec_of
            T tasks offset jitter jobs H codec))).
  {
    apply filter_ext_in.
    intros j _.
    destruct (job_release (jobs j) <? S t) eqn:Hbefore; simpl.
    - apply Nat.ltb_lt in Hbefore.
      apply Nat.ltb_lt.
      lia.
    - reflexivity.
  }
  rewrite Hdrop.
  unfold enum_jittered_periodic_jobs_before,
         enum_jittered_periodic_jobs_upto.
  rewrite
    (enum_jittered_periodic_jobs_upto_unfiltered_filter_before
       T tasks offset jitter jobs H enumT codec t Hwf HenumT_sound Hle).
  reflexivity.
Qed.

Lemma future_jittered_job_not_eligible_at_time :
  forall T tasks offset jitter jobs H enumT
         (codec : JitteredPeriodicCodec T tasks offset jitter jobs) sched t j,
    (forall τ, In τ enumT -> T τ) ->
    In j (enum_jittered_periodic_jobs_upto
            T tasks offset jitter jobs H enumT
            (jittered_periodic_finite_horizon_codec_of
               T tasks offset jitter jobs H codec)) ->
    Nat.ltb (job_release (jobs j)) (S t) = false ->
    ~ eligible jobs 1 sched j t.
Proof.
  intros T tasks offset jitter jobs H enumT codec sched t j HenumT_sound Hin Hbefore.
  pose proof
    (enum_jittered_periodic_jobs_upto_sound
       T tasks offset jitter jobs H enumT
       (jittered_periodic_finite_horizon_codec_of
          T tasks offset jitter jobs H codec)
       HenumT_sound j Hin) as _Hjob.
  apply Nat.ltb_ge in Hbefore.
  intro Helig.
  pose proof (eligible_after_release jobs 1 sched j t Helig) as Hrel.
  lia.
Qed.

Lemma generated_jittered_edf_schedule_prefix_coherent_at :
  forall T tasks offset jitter jobs enumT
         (codec : JitteredPeriodicCodec T tasks offset jitter jobs) H,
    well_formed_periodic_tasks_on T tasks ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    forall h t c,
      t < h ->
      h <= H ->
      generated_schedule_prefix
        edf_generic_spec
        (enum_candidates_of
           (enum_jittered_periodic_jobs_upto
              T tasks offset jitter jobs H enumT
              (jittered_periodic_finite_horizon_codec_of
                 T tasks offset jitter jobs H codec)))
        jobs h t c =
      generated_schedule_prefix
        edf_generic_spec
        (jittered_periodic_candidates_before
           T tasks offset jitter jobs enumT codec)
        jobs h t c.
Proof.
  intros T tasks offset jitter jobs enumT codec H Hwf HenumT_complete HenumT_sound h.
  induction h as [|h' IH]; intros t c Hlt Hh.
  - lia.
  - simpl.
    destruct (Nat.eq_dec t h') as [Heq|Hneq].
    + subst t.
      destruct c as [|c'].
      * rewrite Nat.eqb_refl.
        simpl.
        rewrite Nat.ltb_irrefl.
        change
          (choose edf_generic_spec jobs 1
             (generated_schedule_prefix
                edf_generic_spec
                (enum_candidates_of
                   (enum_jittered_periodic_jobs_upto
                      T tasks offset jitter jobs H enumT
                      (jittered_periodic_finite_horizon_codec_of
                         T tasks offset jitter jobs H codec)))
                jobs h')
             h'
             (enum_jittered_periodic_jobs_upto
                T tasks offset jitter jobs H enumT
                (jittered_periodic_finite_horizon_codec_of
                   T tasks offset jitter jobs H codec)))
          with
          (choose_edf jobs 1
             (generated_schedule_prefix
                edf_generic_spec
                (enum_candidates_of
                   (enum_jittered_periodic_jobs_upto
                      T tasks offset jitter jobs H enumT
                      (jittered_periodic_finite_horizon_codec_of
                         T tasks offset jitter jobs H codec)))
                jobs h')
             h'
             (enum_jittered_periodic_jobs_upto
                T tasks offset jitter jobs H enumT
                (jittered_periodic_finite_horizon_codec_of
                   T tasks offset jitter jobs H codec))).
        change
          (choose edf_generic_spec jobs 1
             (generated_schedule_prefix
                edf_generic_spec
                (jittered_periodic_candidates_before
                   T tasks offset jitter jobs enumT codec)
                jobs h')
             h'
             (jittered_periodic_candidates_before
                T tasks offset jitter jobs enumT codec jobs 1
                (generated_schedule_prefix
                   edf_generic_spec
                   (jittered_periodic_candidates_before
                      T tasks offset jitter jobs enumT codec)
                   jobs h') h'))
          with
          (choose_edf jobs 1
             (generated_schedule_prefix
                edf_generic_spec
                (jittered_periodic_candidates_before
                   T tasks offset jitter jobs enumT codec)
                jobs h')
             h'
             (jittered_periodic_candidates_before
                T tasks offset jitter jobs enumT codec jobs 1
                (generated_schedule_prefix
                   edf_generic_spec
                   (jittered_periodic_candidates_before
                      T tasks offset jitter jobs enumT codec)
                   jobs h') h')).
        assert (Hagree :
          agrees_before
            (generated_schedule_prefix
               edf_generic_spec
               (enum_candidates_of
                  (enum_jittered_periodic_jobs_upto
                     T tasks offset jitter jobs H enumT
                     (jittered_periodic_finite_horizon_codec_of
                        T tasks offset jitter jobs H codec)))
               jobs h')
            (generated_schedule_prefix
               edf_generic_spec
               (jittered_periodic_candidates_before
                  T tasks offset jitter jobs enumT codec)
               jobs h')
            h').
        {
          intros t' c' Hlt'.
          apply IH; try assumption; lia.
        }
        transitivity
          (choose_edf jobs 1
             (generated_schedule_prefix
                edf_generic_spec
                (jittered_periodic_candidates_before
                   T tasks offset jitter jobs enumT codec)
                jobs h')
             h'
             (enum_jittered_periodic_jobs_upto
                T tasks offset jitter jobs H enumT
                (jittered_periodic_finite_horizon_codec_of
                   T tasks offset jitter jobs H codec))).
        2: {
          rewrite choose_edf_filter_ineligible
            with (keep := fun j => Nat.ltb (job_release (jobs j)) (S h')).
          - replace
              (filter (fun j : JobId => job_release (jobs j) <? S h')
                 (enum_jittered_periodic_jobs_upto
                    T tasks offset jitter jobs H enumT
                    (jittered_periodic_finite_horizon_codec_of
                       T tasks offset jitter jobs H codec)))
              with
              (jittered_periodic_candidates_before
                 T tasks offset jitter jobs enumT codec jobs 1
                 (generated_schedule_prefix
                    edf_generic_spec
                    (jittered_periodic_candidates_before
                       T tasks offset jitter jobs enumT codec)
                    jobs h') h').
            2: {
              rewrite
                (enum_jittered_periodic_jobs_upto_filter_before
                   T tasks offset jitter jobs H enumT codec h'
                   Hwf HenumT_sound).
              2: lia.
              unfold jittered_periodic_candidates_before.
              reflexivity.
            }
            unfold jittered_periodic_candidates_before.
            reflexivity.
          - intros j Hin Hkeep.
            eapply future_jittered_job_not_eligible_at_time; eauto.
        }
        apply choose_edf_agrees_before.
        exact Hagree.
      * rewrite Nat.ltb_irrefl, Nat.eqb_refl.
        simpl.
        destruct (Nat.eqb_spec (S c') 0); [lia | reflexivity].
    + assert (t < h') by lia.
      destruct (Nat.ltb t h') eqn:Hcmp.
      * apply IH; try assumption; lia.
      * apply Nat.ltb_ge in Hcmp.
        lia.
Qed.

Theorem infinite_generated_jittered_edf_prefix_coherence :
  forall T tasks offset jitter jobs enumT
         (codec : JitteredPeriodicCodec T tasks offset jitter jobs),
    well_formed_periodic_tasks_on T tasks ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    forall H,
      agrees_before
        (generated_schedule
           edf_generic_spec
           (enum_candidates_of
              (enum_jittered_periodic_jobs_upto
                 T tasks offset jitter jobs H enumT
                 (jittered_periodic_finite_horizon_codec_of
                    T tasks offset jitter jobs H codec)))
           jobs)
        (generated_schedule
           edf_generic_spec
           (jittered_periodic_candidates_before
              T tasks offset jitter jobs enumT codec)
           jobs)
        H.
Proof.
  intros T tasks offset jitter jobs enumT codec Hwf HenumT_complete HenumT_sound H t c Hlt.
  rewrite <-
    (generated_schedule_prefix_stable
       edf_generic_spec
       (enum_candidates_of
          (enum_jittered_periodic_jobs_upto
             T tasks offset jitter jobs H enumT
             (jittered_periodic_finite_horizon_codec_of
                T tasks offset jitter jobs H codec)))
       jobs H t c Hlt).
  rewrite <-
    (generated_schedule_prefix_stable
       edf_generic_spec
       (jittered_periodic_candidates_before
          T tasks offset jitter jobs enumT codec)
       jobs H t c Hlt).
  eapply generated_jittered_edf_schedule_prefix_coherent_at; eauto; lia.
Qed.
